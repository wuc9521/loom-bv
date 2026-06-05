//! LFP synthesis frontend.
//!
//! A monotone LFP problem is "find an operator F and a value v over a
//! finite bit-vector domain such that v = F(v) and v matches the given
//! bit-label constraints." Two SyGuS-IF encodings are recognized:
//!
//!   * `Recursive`: a single nullary synth-fun whose constructor define-funs
//!     reference the synth-fun itself. The synth-fun simultaneously names
//!     the operator (its grammar) and the fixpoint (its value).
//!
//!   * `Separate`: two nullary synth-funs of the same BV sort — one with a
//!     real grammar (the operator) and one whose grammar is `((Constant T))`
//!     (the fixpoint placeholder) — joined by a closure constraint
//!     `(= operator fixpoint)`.
//!
//! Both encode the same LFP problem; the search engine
//! (`exact::search::Searcher`) is variant-agnostic.

use std::collections::BTreeMap;

use sygus_parser::ast::{GrammarDef, Literal, Sort, SyGuSTerm};

use crate::enumerate::expr::OwnedExpr;
use crate::enumerate::value::Value;
use crate::exact::util::{empty_span, extract_single_bit_idx};
use crate::exact::{eval_defined_with_closure};
use crate::info;
use crate::parse::cfg::Cfg;
use crate::parse::{self, deffun, new_custom_error_span, ProblemView, SynthFunView, SynthProblem};

// ---------------------------------------------------------------------------
//  LfpSpec — pattern detection + finalization
// ---------------------------------------------------------------------------

/// LFP synthesis pattern detected in a SyGuS problem.
pub enum LfpSpec<'a> {
    /// Operator and fixpoint live in the same self-referencing synth-fun.
    Recursive {
        synth: SynthFunView<'a>,
        bits: usize,
        labels: Vec<(usize, bool)>,
    },
    /// Operator and fixpoint are separate synth-funs joined by a closure
    /// constraint. `fixpoint_sort` is captured at detection time so
    /// `finalize` doesn't need a back-reference to the original `SyGuSFile`.
    Separate {
        op: SynthFunView<'a>,
        fixpoint_name: &'a str,
        fixpoint_sort: &'a Sort,
        bits: usize,
        labels: Vec<(usize, bool)>,
    },
}

impl<'a> LfpSpec<'a> {
    pub fn detect(view: &'a ProblemView<'_>) -> Option<Self> {
        Self::detect_separate(view).or_else(|| Self::detect_recursive(view))
    }

    fn detect_separate(view: &'a ProblemView<'_>) -> Option<Self> {
        if view.synth_funs.len() != 2 {
            return None;
        }
        let (fixpoint, op) = pick_constant_and_structural(&view.synth_funs)?;
        if !fixpoint.args.is_empty() || !op.args.is_empty() {
            return None;
        }
        let bits = view.sort_aliases.parse_sort_width(fixpoint.ret)?;
        if bits != view.sort_aliases.parse_sort_width(op.ret)? {
            return None;
        }
        let mut closure_seen = false;
        let mut labels = Vec::new();
        for c in &view.constraints {
            if is_closure_constraint(c, op.name, fixpoint.name)
                || is_closure_constraint(c, fixpoint.name, op.name)
            {
                if closure_seen {
                    return None;
                }
                closure_seen = true;
                continue;
            }
            if let Some(lbl) = parse_label_constraint(c, fixpoint.name)
                .or_else(|| parse_label_constraint(c, op.name))
            {
                labels.push(lbl);
            } else {
                return None;
            }
        }
        if !closure_seen {
            return None;
        }
        Some(Self::Separate {
            op,
            fixpoint_name: fixpoint.name,
            fixpoint_sort: fixpoint.ret,
            bits,
            labels,
        })
    }

    fn detect_recursive(view: &'a ProblemView<'_>) -> Option<Self> {
        if view.synth_funs.len() != 1 {
            return None;
        }
        let synth = view.synth_funs[0];
        if !synth.args.is_empty() {
            return None;
        }
        let bits = view.sort_aliases.parse_sort_width(synth.ret)?;
        let mut labels = Vec::new();
        for c in &view.constraints {
            let Some(lbl) = parse_label_constraint(c, synth.name) else {
                return None;
            };
            labels.push(lbl);
        }
        if labels.is_empty() {
            return None;
        }
        let references_self = view
            .define_funs
            .iter()
            .any(|def| term_mentions_symbol(def.body, synth.name));
        if !references_self {
            return None;
        }
        Some(Self::Recursive { synth, bits, labels })
    }

    pub fn bits(&self) -> usize {
        match self {
            Self::Recursive { bits, .. } | Self::Separate { bits, .. } => *bits,
        }
    }

    pub fn labels(&self) -> &[(usize, bool)] {
        match self {
            Self::Recursive { labels, .. } | Self::Separate { labels, .. } => labels,
        }
    }

    /// The synth-fun whose grammar drives enumeration (the operator).
    pub fn operator(&self) -> SynthFunView<'_> {
        match self {
            Self::Recursive { synth, .. } => *synth,
            Self::Separate { op, .. } => *op,
        }
    }

    /// Name to bind closure substitutions to during evaluation.
    pub fn closure_name(&self) -> &str {
        match self {
            Self::Recursive { synth, .. } => synth.name,
            Self::Separate { fixpoint_name, .. } => fixpoint_name,
        }
    }

    pub fn variant_tag(&self) -> &'static str {
        match self {
            Self::Recursive { .. } => "lfp-recursive",
            Self::Separate { .. } => "lfp-separate",
        }
    }

    /// Drive the LFP search: wrap the operator's grammar as a single-arg
    /// SynthProblem (closure synth-fun = the arg), build the bit-constraint
    /// spec from the labels, and hand off to the unified
    /// `NullarySpec::search` with `fixpoint = Some(closure_name)`. Result is
    /// formatted as one or two `define-fun`s.
    pub fn search(&self, env: &deffun::Environ) -> parse::Result<Option<String>> {
        let op = self.operator();
        let grammar_def = op.grammar.ok_or_else(|| {
            new_custom_error_span(
                format!("{}: operator has no grammar", self.variant_tag()),
                empty_span(),
            )
        })?;
        let cfg = Cfg::from_grammar(grammar_def, None)?;
        let closure_name: &'static str =
            Box::leak(self.closure_name().to_string().into_boxed_str());
        let problem = SynthProblem {
            name: Box::leak(op.name.to_string().into_boxed_str()),
            args: vec![closure_name],
            arg_decls: vec![sygus_parser::ast::SortedVar {
                name: closure_name.to_string(),
                sort: op.ret.clone(),
            }],
            cfg,
            span: empty_span(),
            description: String::new(),
            chatgpt_exprs: Vec::new(),
            bits: self.bits(),
            ret_sort: op.ret.clone(),
            axioms: None,
        };
        let labels: BTreeMap<usize, bool> = self.labels().iter().copied().collect();
        let spec = super::bitspec::BitSpec::from_labels(
            self.bits(),
            labels,
            closure_name.to_string(),
        );
        info!(
            "{}: routing to exact search with fixpoint='{}' (bits={}, labels={})",
            self.variant_tag(),
            closure_name,
            self.bits(),
            self.labels().len()
        );
        crate::exact::enable_eval_cache();
        crate::exact::enable_dedup_stats_if_env(self.bits());
        let expr = spec.search(&problem, true, Some(closure_name))?;
        crate::exact::dump_and_disable_eval_cache(self.variant_tag());
        crate::exact::dump_and_disable_dedup_stats(self.variant_tag());
        Ok(Some(self.finalize(env, expr)?))
    }

    /// Format a verified candidate term as one or two `define-fun`s. For
    /// `Recursive`, the synth-fun's value is the body itself. For `Separate`,
    /// we materialize the fixpoint by iterating the operator and emit both
    /// `define-fun`s, matching the SyGuS-IF expectations.
    pub fn finalize(&self, env: &deffun::Environ, expr: OwnedExpr) -> parse::Result<String> {
        match self {
            Self::Recursive { synth, .. } => Ok(format!(
                "(define-fun {} () {} {})",
                synth.name,
                synth.ret,
                expr.to_sygus(&[])
            )),
            Self::Separate {
                op,
                fixpoint_name,
                fixpoint_sort,
                bits,
                ..
            } => {
                let fixpoint = expr.full_lfp(env, fixpoint_name, *bits)?;
                let value = format!("#b{}", fixpoint.to_binstr(*bits));
                Ok(format!(
                    "(define-fun {} () {} {})\n(define-fun {} () {} {})",
                    op.name,
                    op.ret,
                    expr.to_sygus(&[]),
                    fixpoint_name,
                    fixpoint_sort,
                    value
                ))
            }
        }
    }
}

// ---------------------------------------------------------------------------
//  Detection helpers
// ---------------------------------------------------------------------------

fn pick_constant_and_structural<'a>(
    synths: &[SynthFunView<'a>],
) -> Option<(SynthFunView<'a>, SynthFunView<'a>)> {
    let a = &synths[0];
    let b = &synths[1];
    match (is_constant_grammar(a.grammar?), is_constant_grammar(b.grammar?)) {
        (true, false) => Some((*a, *b)),
        (false, true) => Some((*b, *a)),
        _ => None,
    }
}

fn is_constant_grammar(grammar: &GrammarDef) -> bool {
    grammar.grouped_rule_lists.len() == 1
        && grammar.grouped_rule_lists[0].terms.len() == 1
        && matches!(
            &grammar.grouped_rule_lists[0].terms[0],
            sygus_parser::ast::SyGuSGTerm::Constant(_)
        )
}

fn is_closure_constraint(term: &SyGuSTerm, left: &str, right: &str) -> bool {
    let SyGuSTerm::Application(id, args) = term else { return false; };
    if id.get_name() != "=" || args.len() != 2 {
        return false;
    }
    matches!(&args[0], SyGuSTerm::Identifier(a) if a.get_name() == left)
        && matches!(&args[1], SyGuSTerm::Identifier(b) if b.get_name() == right)
}

/// `(= ((_ extract i i) target) #b0|#b1)` or its negation.
fn parse_label_constraint(term: &SyGuSTerm, target: &str) -> Option<(usize, bool)> {
    let (term, negate) = match term {
        SyGuSTerm::Application(id, args) if id.get_name() == "not" && args.len() == 1 => {
            (&args[0], true)
        }
        _ => (term, false),
    };
    let SyGuSTerm::Application(eq, args) = term else { return None; };
    if eq.get_name() != "=" || args.len() != 2 {
        return None;
    }
    let (extract_side, lit_side) = match (&args[0], &args[1]) {
        (SyGuSTerm::Application(_, _), SyGuSTerm::Literal(Literal::BinConst(_))) => {
            (&args[0], &args[1])
        }
        (SyGuSTerm::Literal(Literal::BinConst(_)), SyGuSTerm::Application(_, _)) => {
            (&args[1], &args[0])
        }
        _ => return None,
    };
    let SyGuSTerm::Application(id, ex_args) = extract_side else { return None; };
    let bit_idx = extract_single_bit_idx(id)?;
    if ex_args.len() != 1 {
        return None;
    }
    let SyGuSTerm::Identifier(tgt_id) = &ex_args[0] else { return None; };
    if tgt_id.get_name() != target {
        return None;
    }
    let SyGuSTerm::Literal(Literal::BinConst(bits)) = lit_side else { return None; };
    if bits.len() != 1 || bits.chars().any(|c| c != '0' && c != '1') {
        return None;
    }
    let mut expected = bits.starts_with('1');
    if negate {
        expected = !expected;
    }
    Some((bit_idx, expected))
}

fn term_mentions_symbol(term: &SyGuSTerm, target: &str) -> bool {
    match term {
        SyGuSTerm::Identifier(id) => id.get_name() == target,
        SyGuSTerm::Application(id, args) => {
            id.get_name() == target || args.iter().any(|arg| term_mentions_symbol(arg, target))
        }
        SyGuSTerm::Annotated(inner, _) => term_mentions_symbol(inner, target),
        SyGuSTerm::Let(bindings, body) => {
            bindings.iter().any(|b| term_mentions_symbol(&b.term, target))
                || term_mentions_symbol(body, target)
        }
        SyGuSTerm::Forall(_, body) | SyGuSTerm::Exists(_, body) => {
            term_mentions_symbol(body, target)
        }
        SyGuSTerm::Literal(_) => false,
    }
}

// ---------------------------------------------------------------------------
//  Closure-aware OwnedExpr evaluation + Kleene iteration
// ---------------------------------------------------------------------------

impl OwnedExpr {
    /// Closure-aware evaluation. `closure_value` substitutes for both
    /// (a) bare `Var` placeholders that the parser emits when the operator's
    /// grammar references the closure synth-fun by name, and (b) the
    /// env-tracked closure-arg slots that each `define-fun` body uses.
    pub fn eval_with_closure(
        &self,
        env: &deffun::Environ,
        closure_value: &Value,
        closure_name: &str,
    ) -> parse::Result<Value> {
        let closure = Some((closure_name, closure_value));
        let div_by_zero = || new_custom_error_span("lfp: divide-by-zero".into(), empty_span());
        let fn_div_by_zero = |id: usize, nargs: usize| {
            new_custom_error_span(
                format!("lfp: divide-by-zero in {}", env.name(id, nargs)),
                empty_span(),
            )
        };
        match self {
            OwnedExpr::Const(v) => Ok(v.clone()),
            OwnedExpr::Var(_, _) => Ok(closure_value.clone()),
            OwnedExpr::Concat(a, b) => Ok(a
                .eval_with_closure(env, closure_value, closure_name)?
                .concat(&b.eval_with_closure(env, closure_value, closure_name)?)),
            OwnedExpr::Extract(a, hi, lo) => Ok(a
                .eval_with_closure(env, closure_value, closure_name)?
                .extract(*hi, *lo)),
            OwnedExpr::Not(a) => Ok(a
                .eval_with_closure(env, closure_value, closure_name)?
                .bitnot()),
            OwnedExpr::Neg(a) => Ok(a.eval_with_closure(env, closure_value, closure_name)?.neg()),
            OwnedExpr::Add(a, b) => Ok(a
                .eval_with_closure(env, closure_value, closure_name)?
                .add(b.eval_with_closure(env, closure_value, closure_name)?)),
            OwnedExpr::Xor(a, b) => Ok(a
                .eval_with_closure(env, closure_value, closure_name)?
                .bitxor(b.eval_with_closure(env, closure_value, closure_name)?)),
            OwnedExpr::And(a, b) => Ok(a
                .eval_with_closure(env, closure_value, closure_name)?
                .bitand(b.eval_with_closure(env, closure_value, closure_name)?)),
            OwnedExpr::Or(a, b) => Ok(a
                .eval_with_closure(env, closure_value, closure_name)?
                .bitor(b.eval_with_closure(env, closure_value, closure_name)?)),
            OwnedExpr::Mul(a, b) => Ok(a
                .eval_with_closure(env, closure_value, closure_name)?
                .mul(b.eval_with_closure(env, closure_value, closure_name)?)),
            OwnedExpr::Sub(a, b) => Ok(a
                .eval_with_closure(env, closure_value, closure_name)?
                .sub(b.eval_with_closure(env, closure_value, closure_name)?)),
            OwnedExpr::LShr(a, b) => Ok(a
                .eval_with_closure(env, closure_value, closure_name)?
                .lshr(b.eval_with_closure(env, closure_value, closure_name)?)),
            OwnedExpr::AShr(a, b) => Ok(a
                .eval_with_closure(env, closure_value, closure_name)?
                .ashr(b.eval_with_closure(env, closure_value, closure_name)?)),
            OwnedExpr::Shl(a, b) => Ok(a
                .eval_with_closure(env, closure_value, closure_name)?
                .shl(b.eval_with_closure(env, closure_value, closure_name)?)),
            OwnedExpr::UDiv(a, b) => a
                .eval_with_closure(env, closure_value, closure_name)?
                .udiv(b.eval_with_closure(env, closure_value, closure_name)?)
                .ok_or_else(div_by_zero),
            OwnedExpr::URem(a, b) => a
                .eval_with_closure(env, closure_value, closure_name)?
                .urem(b.eval_with_closure(env, closure_value, closure_name)?)
                .ok_or_else(div_by_zero),
            OwnedExpr::SDiv(a, b) => a
                .eval_with_closure(env, closure_value, closure_name)?
                .sdiv(b.eval_with_closure(env, closure_value, closure_name)?)
                .ok_or_else(div_by_zero),
            OwnedExpr::SRem(a, b) => a
                .eval_with_closure(env, closure_value, closure_name)?
                .srem(b.eval_with_closure(env, closure_value, closure_name)?)
                .ok_or_else(div_by_zero),
            OwnedExpr::Fop0Dyn(id) => {
                eval_defined_with_closure(*id, 0, &[], closure).map_err(|_| fn_div_by_zero(*id, 0))
            }
            OwnedExpr::Fop1Dyn(id, a) => {
                let args = [a.eval_with_closure(env, closure_value, closure_name)?];
                eval_defined_with_closure(*id, 1, &args, closure)
                    .map_err(|_| fn_div_by_zero(*id, 1))
            }
            OwnedExpr::Fop2Dyn(id, a, b) => {
                let args = [
                    a.eval_with_closure(env, closure_value, closure_name)?,
                    b.eval_with_closure(env, closure_value, closure_name)?,
                ];
                eval_defined_with_closure(*id, 2, &args, closure)
                    .map_err(|_| fn_div_by_zero(*id, 2))
            }
            OwnedExpr::FopDyn(id, exprs) => {
                let nargs = exprs.len();
                let args = exprs
                    .iter()
                    .map(|arg| arg.eval_with_closure(env, closure_value, closure_name))
                    .collect::<parse::Result<Vec<_>>>()?;
                eval_defined_with_closure(*id, nargs, &args, closure)
                    .map_err(|_| fn_div_by_zero(*id, nargs))
            }
            OwnedExpr::Ite(cond, then_e, else_e) => {
                let c = cond.eval_with_closure(env, closure_value, closure_name)?;
                if c.as_bool().holds() {
                    then_e.eval_with_closure(env, closure_value, closure_name)
                } else {
                    else_e.eval_with_closure(env, closure_value, closure_name)
                }
            }
            OwnedExpr::Let(_, _, _) => self
                .eval(std::slice::from_ref(closure_value))
                .map_err(|_| new_custom_error_span("lfp: let-eval failed".into(), empty_span())),
        }
    }

    /// Iterate `self` as the body of a closure synth-fun until reaching a
    /// `bits`-wide fixpoint, starting from all-zeros. Bounded by `bits + 1`
    /// iterations (monotone Boolean lattice height).
    pub fn full_lfp(
        &self,
        env: &deffun::Environ,
        closure_name: &str,
        bits: usize,
    ) -> parse::Result<Value> {
        let mut aux = Value::from_u64(0, bits);
        for _ in 0..=bits {
            let next = self.eval_with_closure(env, &aux, closure_name)?;
            if next == aux {
                return Ok(next);
            }
            aux = next;
        }
        Err(new_custom_error_span(
            "lfp: full LFP did not converge".into(),
            empty_span(),
        ))
    }
}

impl Value {
    pub(crate) fn to_binstr(&self, bits: usize) -> String {
        let mut out = String::with_capacity(bits);
        for i in (0..bits).rev() {
            out.push(if self.bit(i) { '1' } else { '0' });
        }
        out
    }
}
