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

use sygus_parser::ast::{Literal, Sort, SyGuSTerm};

use crate::enumerate::expr::OwnedExpr;
use crate::enumerate::value::BitVec;
use crate::exact::util::{empty_span, extract_single_bit_idx};
use crate::info;
use crate::parse::cfg::Cfg;
use crate::parse::{
    self, deffun, is_constant_grammar, new_custom_error_span, term_mentions_symbol, ProgramEnv,
    SynthFunView, SynthProblem,
};

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
    pub fn detect(env: &'a ProgramEnv<'_>) -> Option<Self> {
        Self::detect_separate(env).or_else(|| Self::detect_recursive(env))
    }

    fn detect_separate(env: &'a ProgramEnv<'_>) -> Option<Self> {
        if env.synth_funs.len() != 2 {
            return None;
        }
        let (fixpoint, op) = pick_constant_and_structural(&env.synth_funs)?;
        if !fixpoint.args.is_empty() || !op.args.is_empty() {
            return None;
        }
        let bits = env.sort_aliases.parse_sort_width(fixpoint.ret)?;
        if bits != env.sort_aliases.parse_sort_width(op.ret)? {
            return None;
        }
        let mut closure_seen = false;
        let mut labels = Vec::new();
        for c in &env.constraints {
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

    fn detect_recursive(env: &'a ProgramEnv<'_>) -> Option<Self> {
        if env.synth_funs.len() != 1 {
            return None;
        }
        let synth = env.synth_funs[0];
        if !synth.args.is_empty() {
            return None;
        }
        let bits = env.sort_aliases.parse_sort_width(synth.ret)?;
        let mut labels = Vec::new();
        for c in &env.constraints {
            let Some(lbl) = parse_label_constraint(c, synth.name) else {
                return None;
            };
            labels.push(lbl);
        }
        if labels.is_empty() {
            return None;
        }
        let references_self = env
            .grammar_deps_for(0)
            .is_some_and(|deps| deps.requires_recursion())
            || env
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
        let cfg = Cfg::from_grammar(grammar_def)?;
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
            description: String::new(),
            chatgpt_exprs: Vec::new(),
            bits: self.bits(),
            ret_sort: op.ret.clone(),
        };
        let labels: BTreeMap<usize, bool> = self.labels().iter().copied().collect();
        let spec = super::bitspec::Constraint::from_labels(
            self.bits(),
            labels,
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
        let _ = closure_name;
        let expr = spec.search(&problem, true)?;
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

// ---------------------------------------------------------------------------
//  Kleene iteration (legacy single-aux path, used by `LfpSpec::finalize`
//  for the `Separate` variant). The new fwd-decls path will replace this
//  with multi-aux iteration over a `Bindings`.
// ---------------------------------------------------------------------------

impl OwnedExpr {
    /// Iterate `self` as the body of a closure synth-fun until reaching a
    /// `bits`-wide fixpoint, starting from all-zeros. Bounded by `bits + 1`
    /// iterations (monotone Boolean lattice height).
    pub fn full_lfp(
        &self,
        env: &deffun::Environ,
        closure_name: &str,
        bits: usize,
    ) -> parse::Result<BitVec> {
        let _ = env;
        let mut aux = BitVec::from_u64(0, bits);
        for _ in 0..=bits {
            let next = self
                .eval_with_bindings(&[aux.clone()], &[(closure_name, &aux)])
                .map_err(|_| {
                    new_custom_error_span("lfp: divide-by-zero".into(), empty_span())
                })?;
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

impl BitVec {
    pub(crate) fn to_binstr(&self, bits: usize) -> String {
        let mut out = String::with_capacity(bits);
        for i in (0..bits).rev() {
            out.push(if self.bit(i) { '1' } else { '0' });
        }
        out
    }
}
