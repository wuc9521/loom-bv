//! Least-fixed-point synthesis spec.
//!
//! A monotone LFP problem is "find an operator F and a value v over a
//! finite bit-vector domain such that v = F(v) and v matches the given
//! bit-label constraints." Two encodings are recognized in SyGuS input:
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
//! Both encode the same LFP problem; the rest of the closure module is
//! variant-agnostic.

use std::collections::BTreeMap;

use sygus_parser::ast::{GrammarDef, Identifier, Literal, Sort, SortedVar, SyGuSTerm};

use crate::enumerate::expr::OwnedExpr;
use crate::enumerate::grammar::MultiConfig;
use crate::enumerate::value::Value;
use crate::exact::{relevance, ExactGrammar, NullarySpec};
use crate::parse::cfg::Cfg;
use crate::parse::{self, deffun, new_custom_error_span, ProblemView, SynthFunView, SynthProblem};

use super::eval::compute_full_lfp;

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

    pub fn grammar_def(&self) -> Option<&GrammarDef> {
        self.operator().grammar
    }

    pub fn variant_tag(&self) -> &'static str {
        match self {
            Self::Recursive { .. } => "lfp-recursive",
            Self::Separate { .. } => "lfp-separate",
        }
    }

    /// Build the `ExactGrammar` used by relevance and bottom-up search.
    /// The operator's synth-fun is rewrapped with a synthetic arg that names
    /// the closure target, so `OwnedExpr::from_term` resolves the closure
    /// leaf as `Var(0, bits)` instead of erroring on an unknown identifier.
    pub fn build_grammar(&self) -> parse::Result<ExactGrammar<'static>> {
        let op = self.operator();
        let grammar_def = op.grammar.ok_or_else(|| {
            new_custom_error_span("lfp: operator has no grammar".into(), empty_span())
        })?;
        let cfg = Cfg::from_grammar(grammar_def, None)?;
        let closure_name: &'static str = Box::leak(self.closure_name().to_string().into_boxed_str());
        let problem = SynthProblem {
            name: Box::leak(op.name.to_string().into_boxed_str()),
            args: vec![closure_name],
            arg_decls: vec![SortedVar {
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
        let multi = MultiConfig::from_problem(&problem)?;
        Ok(ExactGrammar::from_config(&multi))
    }

    /// Backward relevance with the closure-feedback edge enabled. Returns
    /// `(per-NT relevant bits, closure-relevant bits)`, defaulting both to
    /// "all bits" if relevance reports nothing.
    pub fn closure_relevant_bits(&self) -> parse::Result<(Vec<Vec<usize>>, Vec<usize>)> {
        let exact = self.build_grammar()?;
        let known: BTreeMap<usize, bool> = self.labels().iter().copied().collect();
        let nullary = NullarySpec::BitConstraints {
            bits: self.bits(),
            known_bits: known,
            structural: Vec::new(),
        };
        let nt_default = || {
            exact
                .nts
                .iter()
                .map(|(_, rules)| (0..relevance::nt_output_bits(rules)).collect::<Vec<_>>())
                .collect::<Vec<_>>()
        };
        let closure_default = || (0..self.bits()).collect::<Vec<_>>();
        let Some(mut lazy) = relevance::LazyRelevance::new_with_closure(&exact, &nullary, 0) else {
            return Ok((nt_default(), closure_default()));
        };
        while !lazy.advance(1024) {}
        let (nt_bits, closure_bits) = lazy.finish_with_closure();
        Ok((nt_bits.unwrap_or_else(nt_default), closure_bits.unwrap_or_else(closure_default)))
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
                let fixpoint = compute_full_lfp(env, &expr, fixpoint_name, *bits)?;
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
        (SyGuSTerm::Application(_, _), SyGuSTerm::Literal(Literal::BinConst(_))) => (&args[0], &args[1]),
        (SyGuSTerm::Literal(Literal::BinConst(_)), SyGuSTerm::Application(_, _)) => (&args[1], &args[0]),
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

fn extract_single_bit_idx(id: &Identifier) -> Option<usize> {
    let Identifier::Indexed(name, idxs) = id else { return None; };
    if name != "extract" || idxs.len() != 2 {
        return None;
    }
    let hi = numeral_index(&idxs[0])?;
    let lo = numeral_index(&idxs[1])?;
    if hi != lo {
        return None;
    }
    Some(hi)
}

fn numeral_index(idx: &sygus_parser::ast::Index) -> Option<usize> {
    match idx {
        sygus_parser::ast::Index::Numeral(n) => Some(*n),
        sygus_parser::ast::Index::Symbol(_) => None,
    }
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
        SyGuSTerm::Forall(_, body) | SyGuSTerm::Exists(_, body) => term_mentions_symbol(body, target),
        SyGuSTerm::Literal(_) => false,
    }
}

pub fn empty_span() -> pest::Span<'static> {
    pest::Span::new("", 0, 0).unwrap()
}

impl Value {
    fn to_binstr(&self, bits: usize) -> String {
    let mut out = String::with_capacity(bits);
    for i in (0..bits).rev() {
        out.push(if self.bit(i) { '1' } else { '0' });
    }
    out
    }
}
