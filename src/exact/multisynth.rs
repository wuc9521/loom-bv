//! Multi-synth-fun closure-constraint solver.
//!
//! Pattern detected:
//!   * Two nullary synth-funs both returning the same BV sort.  One has a
//!     real grammar (call it `g`); the other has only `(Constant <sort>)`
//!     (call it `cfg.rhs.S`).
//!   * Exactly one closure constraint of shape `(= g cfg.rhs.S)`.
//!   * Zero or more bit-extract label constraints on `cfg.rhs.S` of the form
//!     `(= ((_ extract i i) cfg.rhs.S) #b0|#b1)`.
//!
//! The closure constraint forces `cfg.rhs.S` to be a fixed point of g's
//! productions, evaluated using `cfg.rhs.S`'s own value for the recursive
//! reference.  The LFP encodes "S parses (sample, i, j)" for each cell.
//!
//! Search:
//!   * Enumerate candidate `g` terms via the grammar, smallest-first.
//!   * For each candidate, compute the LFP of `cfg.rhs.S` by iteration
//!     (start at 0, repeatedly evaluate g with the previous value, stop at
//!     fixed point or word-length+1 iterations).
//!   * Check label bits; if all match, return the solution.
//!
//! No Int, no datatypes, no recursive functions — pure BV throughout.

use sygus_parser::ast::{GrammarDef, Identifier, Literal, Sort, SortedVar, SyGuSCmd, SyGuSFile, SyGuSTerm};

use crate::enumerate::expr::OwnedExpr;
use crate::enumerate::grammar::{for_each_candidate_tuple, for_each_size_split, MultiConfig, TemplateExpr};
use crate::enumerate::value::Value;
use crate::info;
use crate::parse::cfg::Cfg;
use crate::parse::{self, deffun, new_custom_error_span, ProblemView, SynthFunView, SynthProblem};

use super::grammar::compile_exact_grammar;
use super::{
    intern_node, materialize_node, relevance, ExactEvalCache, ExactGrammar, ExactRule, Node,
    NullarySpec,
};

use num_bigint::BigUint;
use num_traits::Zero;
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::{hash_map::Entry, BTreeMap};

/// The multi-synth closure pattern, extracted from the file's view.
pub struct MultiSynthSpec<'a> {
    /// The synth-fun with the substantial grammar — the structural `g`.
    pub g: SynthFunView<'a>,
    /// The synth-fun whose grammar is `((C T ((Constant T))))` — the LFP table.
    pub rhs_s_name: &'a str,
    pub bits: usize,
    /// Bit-extract label constraints on `rhs_s_name`: `(bit_idx, expected_bit)`.
    pub labels: Vec<(usize, bool)>,
}

/// Single synth-fun closure pattern: the synth-fun's constructor semantics
/// reference the synth-fun itself, so search must interpret the candidate as
/// a closure operator over its own BV value.
pub struct SingleSynthSpec<'a> {
    pub synth: SynthFunView<'a>,
    pub bits: usize,
    pub labels: Vec<(usize, bool)>,
}

impl<'a> MultiSynthSpec<'a> {
    pub fn detect(view: &'a ProblemView<'_>) -> Option<Self> {
        if view.synth_funs.len() != 2 {
            return None;
        }
        // Identify which synth-fun is "Constant" (the LFP table) and which is the structural g.
        let (rhs_s, g) = pick_constant_and_structural(&view.synth_funs)?;
        if !rhs_s.args.is_empty() || !g.args.is_empty() {
            return None;
        }
        let bits = view.sort_aliases.parse_sort_width(rhs_s.ret)?;
        let g_bits = view.sort_aliases.parse_sort_width(g.ret)?;
        if bits != g_bits {
            return None;
        }

        // Constraints: exactly one closure `(= g rhs.S)` or `(= rhs.S g)`, plus
        // label bit-extracts on either `rhs.S` or `g` (they're equivalent
        // because of the closure). The cyk encoder emits labels on rhs.S;
        // Delis's native bv.rs emits them on g. We accept both.
        let mut closure_seen = false;
        let mut labels: Vec<(usize, bool)> = Vec::new();
        for c in &view.constraints {
            if is_closure_constraint(c, g.name, rhs_s.name)
                || is_closure_constraint(c, rhs_s.name, g.name)
            {
                if closure_seen {
                    return None; // only one closure allowed
                }
                closure_seen = true;
                continue;
            }
            if let Some(lbl) = parse_label_constraint(c, rhs_s.name)
                .or_else(|| parse_label_constraint(c, g.name))
            {
                labels.push(lbl);
            } else {
                return None; // unknown constraint shape — bail
            }
        }
        if !closure_seen {
            return None;
        }

        Some(Self {
            g,
            rhs_s_name: rhs_s.name,
            bits,
            labels,
        })
    }
}

impl<'a> SingleSynthSpec<'a> {
    pub fn detect(view: &'a ProblemView<'_>) -> Option<Self> {
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
            if let Some(lbl) = parse_label_constraint(c, synth.name) {
                labels.push(lbl);
            } else {
                return None;
            }
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
        Some(Self { synth, bits, labels })
    }
}

/// Choose which synth-fun is the constant LFP table and which is the structural g.
/// The constant one has grammar with a single "Constant" production.
fn pick_constant_and_structural<'a>(
    synths: &[SynthFunView<'a>],
) -> Option<(SynthFunView<'a>, SynthFunView<'a>)> {
    let a = &synths[0];
    let b = &synths[1];
    match (is_constant_grammar(a.grammar?), is_constant_grammar(b.grammar?)) {
        (true, false) => Some((*a, *b)),
        (false, true) => Some((*b, *a)),
        _ => None, // both or neither — not the expected pattern
    }
}

/// Is this grammar just `((Constant <sort>))` (the LFP-table placeholder)?
fn is_constant_grammar(grammar: &GrammarDef) -> bool {
    if grammar.grouped_rule_lists.len() != 1 {
        return false;
    }
    let rules = &grammar.grouped_rule_lists[0].terms;
    if rules.len() != 1 {
        return false;
    }
    matches!(&rules[0], sygus_parser::ast::SyGuSGTerm::Constant(_))
}

fn is_closure_constraint(term: &SyGuSTerm, left: &str, right: &str) -> bool {
    let SyGuSTerm::Application(id, args) = term else { return false; };
    if id.get_name() != "=" || args.len() != 2 {
        return false;
    }
    matches!(&args[0], SyGuSTerm::Identifier(a) if a.get_name() == left)
        && matches!(&args[1], SyGuSTerm::Identifier(b) if b.get_name() == right)
}

/// Parses a label constraint into `(bit_idx, expected)`. Accepts:
///   - `(= ((_ extract i i) target) #b0|#b1)`
///   - `(not (= ((_ extract i i) target) #b0|#b1))`  → polarity flipped
///
/// The negated form is what Delis emits when a `(constraint (not ...))` in
/// the source compiles to a bit-extract under the BV encoding.
fn parse_label_constraint(term: &SyGuSTerm, target: &str) -> Option<(usize, bool)> {
    // Strip a top-level `not`, flipping the expected polarity.
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
    let trimmed = bits.trim_start_matches(|c| c == '0' || c == '1');
    if !trimmed.is_empty() {
        return None;
    }
    if bits.len() != 1 {
        return None; // a single-bit extract should give a 1-bit literal
    }
    let mut expected = bits.chars().next().unwrap() == '1';
    if negate {
        expected = !expected;
    }
    Some((bit_idx, expected))
}

/// `((_ extract hi lo) x)` where hi == lo gives a single bit. Return that index.
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
            bindings.iter().any(|binding| term_mentions_symbol(&binding.term, target))
                || term_mentions_symbol(body, target)
        }
        SyGuSTerm::Forall(_, body) | SyGuSTerm::Exists(_, body) => term_mentions_symbol(body, target),
        SyGuSTerm::Literal(_) => false,
    }
}

// ---------------------------------------------------------------------------
//  Search
// ---------------------------------------------------------------------------

/// Enumerate candidate `g` terms; for each, compute the LFP of `cfg.rhs.S`
/// and check label bits. Returns the rendered solution on success.
///
/// Optimization: compute the relevant bits of the closure target via backward
/// relevance with a feedback edge (the `cfg.rhs.S` leaf demand propagates back
/// to g's start NT). Use the resulting bit set to dedup LFP values across
/// candidate g's via projection. This is the first step toward unifying
/// multisynth with the exact-nullary path — it validates the closure-feedback
/// relevance computation end-to-end before the heavier Tabulated refactor.
pub fn search(
    file: &SyGuSFile,
    spec: &MultiSynthSpec,
    env: &deffun::Environ,
    max_g_size: usize,
) -> parse::Result<Option<String>> {
    let relevance = compute_all_closure_relevant_bits(spec).unwrap_or_else(|err| {
        info!("multisynth: relevance computation skipped: {}", err);
        None
    });
    if let Some((nt_bits, closure_bits)) = relevance.as_ref() {
        let start_bits = nt_bits.first().map(Vec::len).unwrap_or(0);
        info!(
            "multisynth: closure input bits = {}/{}; start output bits = {}/{}",
            closure_bits.len(),
            spec.bits,
            start_bits,
            spec.bits
        );
    }
    if let Some((all_bits, closure_bits)) = relevance.as_ref() {
        if !closure_bits.is_empty() && closure_bits.len() <= 12 {
            if let Some(solution) = search_bottom_up(
                file,
                spec,
                env,
                max_g_size,
                all_bits,
                closure_bits,
            )?
            {
                return Ok(Some(solution));
            }
            return Ok(None);
        }
    }
    search_top_down(file, spec, env, max_g_size)
}

pub fn search_single(
    spec: &SingleSynthSpec<'_>,
    env: &deffun::Environ,
) -> parse::Result<Option<OwnedExpr>> {
    let Some((relevant_bits, closure_bits)) = compute_all_single_closure_relevant_bits(spec)? else {
        info!("single-closure: falling back to top-down (no relevance result)");
        return search_single_top_down(spec, env);
    };
    if closure_bits.is_empty() {
        info!("single-closure: falling back to top-down (empty closure bits)");
        return search_single_top_down(spec, env);
    }
    if closure_bits.len() > 12 {
        info!(
            "single-closure: falling back to top-down (closure support needs {} bits)",
            closure_bits.len()
        );
        return search_single_top_down(spec, env);
    }
    info!(
        "single-closure: using bottom-up search (closure bits={}, start bits={})",
        closure_bits.len(),
        relevant_bits.first().map(|bits| bits.len()).unwrap_or(0)
    );
    search_single_bottom_up(spec, env, &relevant_bits, &closure_bits)
}

fn search_single_top_down(
    spec: &SingleSynthSpec<'_>,
    env: &deffun::Environ,
) -> parse::Result<Option<OwnedExpr>> {
    let grammar = spec
        .synth
        .grammar
        .ok_or_else(|| new_custom_error_span("single-closure: synth-fun has no grammar".into(), empty_span()))?;
    let max_iters = spec.bits + 1;
    let enumerator = TermEnumerator::new(grammar);
    let mut candidates_total = 0usize;
    let mut candidates_converged = 0usize;
    for size in 1.. {
        for term in enumerator.terms_of_size(size) {
            candidates_total += 1;
            let mut value = Value::from_u64(0, spec.bits);
            let mut converged = false;
            for _ in 0..max_iters {
                let next = eval_term(&term, env, &value, spec.synth.name, spec.bits)?;
                if next == value {
                    converged = true;
                    break;
                }
                value = next;
            }
            if !converged {
                continue;
            }
            candidates_converged += 1;
            if spec
                .labels
                .iter()
                .all(|(bit, expected)| value.bit(*bit) == *expected)
            {
                info!(
                    "single-closure: found solution at size={}, candidates_total={}, candidates_converged={}",
                    size, candidates_total, candidates_converged
                );
                return Ok(Some(term_to_owned_expr(&term)?));
            }
        }
    }
    Ok(None)
}

fn compute_all_single_closure_relevant_bits(
    spec: &SingleSynthSpec,
) -> parse::Result<Option<(Vec<Vec<usize>>, Vec<usize>)>> {
    let exact = build_exact_grammar_for_synth(spec.synth, spec.synth.name, spec.bits)?;
    let known_bits: BTreeMap<usize, bool> = spec.labels.iter().copied().collect();
    let nullary_spec = NullarySpec::BitConstraints {
        bits: spec.bits,
        known_bits,
        structural: Vec::new(),
    };
    let Some(mut lazy) = relevance::LazyRelevance::new_with_closure(&exact, &nullary_spec, 0)
    else {
        return Ok(None);
    };
    while !lazy.advance(1024) {}
    let (nt_bits, closure_relevant_bits) = lazy.finish_with_closure();
    let nt_bits = nt_bits.unwrap_or_else(|| {
        exact
            .nts
            .iter()
            .map(|(_, rules)| (0..relevance::nt_output_bits(rules)).collect::<Vec<_>>())
            .collect::<Vec<_>>()
    });
    let closure_bits = closure_relevant_bits.unwrap_or_else(|| (0..spec.bits).collect::<Vec<_>>());
    Ok(Some((nt_bits, closure_bits)))
}

/// Build an `ExactGrammar` from g's grammar (with the closure leaf as a
/// synthetic arg `Var(0, bits)`), then run `LazyRelevance` with the
/// closure-feedback edge enabled. Returns the relevant bit set of the start
/// NT (== the closure target), or `Ok(None)` if no reduction is possible.
fn compute_all_closure_relevant_bits(
    spec: &MultiSynthSpec,
) -> parse::Result<Option<(Vec<Vec<usize>>, Vec<usize>)>> {
    let grammar_def = spec
        .g
        .grammar
        .ok_or_else(|| new_custom_error_span("multisynth: g has no grammar".into(), empty_span()))?;

    // Construct a SynthProblem for g where the closure leaf is a synthetic arg.
    // OwnedExpr::from_term will resolve the leaf as Var(0, bits) instead of
    // erroring on the unknown identifier (it's a synth-fun, not a define-fun).
    let cfg = Cfg::from_grammar(grammar_def, None)?;
    let leaf_name: &'static str = Box::leak(spec.rhs_s_name.to_string().into_boxed_str());
    let problem = SynthProblem {
        name: Box::leak(spec.g.name.to_string().into_boxed_str()),
        args: vec![leaf_name],
        arg_decls: vec![SortedVar {
            name: leaf_name.to_string(),
            sort: spec.g.ret.clone(),
        }],
        cfg,
        span: empty_span(),
        description: String::new(),
        chatgpt_exprs: Vec::new(),
        bits: spec.bits,
        ret_sort: spec.g.ret.clone(),
        axioms: None,
    };

    let multi = MultiConfig::from_problem(&problem)?;
    let exact = compile_exact_grammar(&multi);

    let known_bits: BTreeMap<usize, bool> = spec.labels.iter().copied().collect();
    let nullary_spec = NullarySpec::BitConstraints {
        bits: spec.bits,
        known_bits,
        structural: Vec::new(),
    };

    let Some(mut lazy) = relevance::LazyRelevance::new_with_closure(&exact, &nullary_spec, 0)
    else {
        return Ok(None);
    };
    while !lazy.advance(1024) {}
    let (nt_bits, closure_bits) = lazy.finish_with_closure();
    Ok(nt_bits.zip(closure_bits))
}

fn format_solution(
    file: &SyGuSFile,
    spec: &MultiSynthSpec,
    g_expr: &OwnedExpr,
    rhs_s: &Value,
) -> String {
    let g_sort_text = display_sort(spec.g.ret);
    let rhs_sort_text = display_sort_from_name(file, spec.rhs_s_name).unwrap_or(g_sort_text.clone());
    let rhs_s_lit = format!("#b{}", value_to_binstr(rhs_s, spec.bits));
    let g_text = g_expr.to_sygus(&[]);
    // Order: g first, cfg.rhs.S second (mirrors the encoder).
    format!(
        "(define-fun {} () {} {})\n(define-fun {} () {} {})",
        spec.g.name, g_sort_text, g_text, spec.rhs_s_name, rhs_sort_text, rhs_s_lit
    )
}

fn search_top_down(
    file: &SyGuSFile,
    spec: &MultiSynthSpec,
    env: &deffun::Environ,
    max_g_size: usize,
) -> parse::Result<Option<String>> {
    let grammar = spec
        .g
        .grammar
        .ok_or_else(|| new_custom_error_span("multisynth: g has no grammar".into(), empty_span()))?;
    let max_iters = spec.bits + 1;
    let relevant_bits = compute_all_closure_relevant_bits(spec)?
        .and_then(|(nt_bits, _closure_bits)| nt_bits.into_iter().next());
    let mut seen_lfp: FxHashSet<Vec<u64>> = FxHashSet::default();
    let enumerator = TermEnumerator::new(grammar);
    let mut candidates_total = 0usize;
    let mut candidates_converged = 0usize;
    for size in 1..=max_g_size {
        for term in enumerator.terms_of_size(size) {
            candidates_total += 1;
            let mut rhs_s = Value::from_u64(0, spec.bits);
            let mut converged = false;
            for _ in 0..max_iters {
                let next = eval_term(&term, env, &rhs_s, spec.rhs_s_name, spec.bits)?;
                if next == rhs_s {
                    converged = true;
                    break;
                }
                rhs_s = next;
            }
            if !converged {
                continue;
            }
            candidates_converged += 1;
            if let Some(bits) = relevant_bits.as_ref() {
                let key = rhs_s.project_bits(bits);
                if !seen_lfp.insert(key) {
                    continue;
                }
            }
            if spec
                .labels
                .iter()
                .all(|(bit, expected)| rhs_s.bit(*bit) == *expected)
            {
                info!(
                    "multisynth: found solution at size={}, candidates_total={}, candidates_converged={}",
                    size, candidates_total, candidates_converged
                );
                let g_expr = term_to_owned_expr(&term)?;
                let solution = format_solution(file, spec, &g_expr, &rhs_s);
                return Ok(Some(solution));
            }
        }
    }
    Ok(None)
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct TransferKey(Vec<Vec<u64>>);

#[derive(Clone, PartialEq, Eq, Hash)]
struct SingleApplySummaryCacheKey {
    fid: usize,
    child_keys: Vec<TransferKey>,
    output_relevant_bits: Vec<usize>,
}

#[derive(Clone)]
struct TransferCandidate {
    node: usize,
    key: TransferKey,
}

fn search_bottom_up(
    file: &SyGuSFile,
    spec: &MultiSynthSpec,
    env: &deffun::Environ,
    max_g_size: usize,
    relevant_bits: &[Vec<usize>],
    closure_bits: &[usize],
) -> parse::Result<Option<String>> {
    let exact = build_exact_grammar(spec)?;
    let nt_widths = exact
        .nts
        .iter()
        .map(|(_, rules)| relevance::nt_output_bits(rules))
        .collect::<Vec<_>>();
    let start_rel = &relevant_bits[exact.start];
    if start_rel.is_empty() {
        return Ok(None);
    }
    let domain_size = 1usize << closure_bits.len();
    let closure_inputs = (0..domain_size)
        .map(|mask| full_value_from_mask(mask, spec.bits, closure_bits))
        .collect::<Vec<_>>();
    let label_positions = spec
        .labels
        .iter()
        .map(|(bit, expected)| {
            start_rel
                .iter()
                .position(|b| b == bit)
                .map(|idx| (idx, *expected))
                .ok_or_else(|| {
                    new_custom_error_span(
                        format!("multisynth: label bit {bit} missing from relevant set"),
                        empty_span(),
                    )
                })
        })
        .collect::<parse::Result<Vec<_>>>()?;

    let nt_count = exact.nts.len();
    let mut by_size = vec![vec![Vec::<TransferCandidate>::new()]; nt_count];
    let mut seen = (0..nt_count)
        .map(|_| FxHashMap::<TransferKey, usize>::default())
        .collect::<Vec<_>>();
    let mut nodes = Vec::<Node>::new();
    let mut eval_cache = ExactEvalCache::default();
    let mut candidates_total = 0usize;

    for size in 1..=max_g_size {
        for buckets in &mut by_size {
            buckets.push(Vec::new());
        }
        for (nt_idx, (_, rules)) in exact.nts.iter().enumerate() {
            for (rule_idx, rule) in rules.iter().enumerate() {
                match rule {
                    ExactRule::Alias(_) => {}
                    ExactRule::Leaf(expr) => {
                        if size != 1 {
                            continue;
                        }
                        let key = summarize_leaf(
                            expr,
                            nt_idx,
                            relevant_bits,
                            &closure_inputs,
                            spec,
                            env,
                            &mut eval_cache,
                        )?;
                        candidates_total += 1;
                        if let Some(solution) = try_insert_transfer_candidate(
                            file,
                            spec,
                            env,
                            &exact,
                            relevant_bits,
                            &label_positions,
                            nt_idx,
                            size,
                            key,
                            &mut seen,
                            &mut by_size,
                            &mut nodes,
                            Node {
                                nt_idx,
                                rule_idx,
                                children: Vec::new(),
                            },
                        )? {
                            info!(
                                "multisynth: found solution at size={}, candidates_total={}",
                                size, candidates_total
                            );
                            return Ok(Some(solution));
                        }
                    }
                    ExactRule::Unary { fid, child_nt } => {
                        if size < 2 {
                            continue;
                        }
                        let child_size = size - 1;
                        let children = by_size[*child_nt]
                            .get(child_size)
                            .cloned()
                            .unwrap_or_default();
                        for child in children {
                            let key = summarize_apply(
                                *fid,
                                &[child.key.clone()],
                                &[relevant_bits[*child_nt].as_slice()],
                                &[nt_widths[*child_nt]],
                                &relevant_bits[nt_idx],
                                &closure_inputs,
                                spec,
                                env,
                            )?;
                            candidates_total += 1;
                            if let Some(solution) = try_insert_transfer_candidate(
                                file,
                                spec,
                                env,
                                &exact,
                                relevant_bits,
                                &label_positions,
                                nt_idx,
                                size,
                                key,
                                &mut seen,
                                &mut by_size,
                                &mut nodes,
                                Node {
                                    nt_idx,
                                    rule_idx,
                                    children: vec![child.node],
                                },
                            )? {
                                info!(
                                    "multisynth: found solution at size={}, candidates_total={}",
                                    size, candidates_total
                                );
                                return Ok(Some(solution));
                            }
                        }
                    }
                    ExactRule::Binary { fid, lhs_nt, rhs_nt } => {
                        if size < 3 {
                            continue;
                        }
                        for lhs_size in 1..(size - 1) {
                            let rhs_size = size - 1 - lhs_size;
                            let lhs_pool = by_size[*lhs_nt]
                                .get(lhs_size)
                                .cloned()
                                .unwrap_or_default();
                            let rhs_pool = by_size[*rhs_nt]
                                .get(rhs_size)
                                .cloned()
                                .unwrap_or_default();
                            if lhs_pool.is_empty() || rhs_pool.is_empty() {
                                continue;
                            }
                            for lhs in &lhs_pool {
                                for rhs in &rhs_pool {
                                    let key = summarize_apply(
                                        *fid,
                                        &[lhs.key.clone(), rhs.key.clone()],
                                        &[
                                            relevant_bits[*lhs_nt].as_slice(),
                                            relevant_bits[*rhs_nt].as_slice(),
                                        ],
                                        &[nt_widths[*lhs_nt], nt_widths[*rhs_nt]],
                                        &relevant_bits[nt_idx],
                                        &closure_inputs,
                                        spec,
                                        env,
                                    )?;
                                    candidates_total += 1;
                                    if let Some(solution) = try_insert_transfer_candidate(
                                        file,
                                        spec,
                                        env,
                                        &exact,
                                        relevant_bits,
                                        &label_positions,
                                        nt_idx,
                                        size,
                                        key,
                                        &mut seen,
                                        &mut by_size,
                                        &mut nodes,
                                        Node {
                                            nt_idx,
                                            rule_idx,
                                            children: vec![lhs.node, rhs.node],
                                        },
                                    )? {
                                        info!(
                                            "multisynth: found solution at size={}, candidates_total={}",
                                            size, candidates_total
                                        );
                                        return Ok(Some(solution));
                                    }
                                }
                            }
                        }
                    }
                    ExactRule::Nary { fid, child_nts } => {
                        if size <= child_nts.len() {
                            continue;
                        }
                        let child_total = size - 1;
                        let mut found = None;
                        let mut splits = Vec::with_capacity(child_nts.len());
                        for_each_size_split(child_total, child_nts.len(), &mut splits, &mut |sizes| {
                            if found.is_some() {
                                return;
                            }
                            let pools = child_nts
                                .iter()
                                .zip(sizes.iter())
                                .map(|(child_nt, child_size)| {
                                    by_size[*child_nt]
                                        .get(*child_size)
                                        .cloned()
                                        .unwrap_or_default()
                                })
                                .collect::<Vec<_>>();
                            if pools.iter().any(|pool| pool.is_empty()) {
                                return;
                            }
                            let pool_refs =
                                pools.iter().map(Vec::as_slice).collect::<Vec<_>>();
                            let mut tuple = Vec::with_capacity(child_nts.len());
                            for_each_candidate_tuple(&pool_refs, &mut tuple, &mut |tuple| {
                                let child_keys =
                                    tuple.iter().map(|cand| cand.key.clone()).collect::<Vec<_>>();
                                let child_bits = child_nts
                                    .iter()
                                    .map(|child_nt| relevant_bits[*child_nt].as_slice())
                                    .collect::<Vec<_>>();
                                let child_widths = child_nts
                                    .iter()
                                    .map(|child_nt| nt_widths[*child_nt])
                                    .collect::<Vec<_>>();
                                let key = match summarize_apply(
                                    *fid,
                                    &child_keys,
                                    &child_bits,
                                    &child_widths,
                                    &relevant_bits[nt_idx],
                                    &closure_inputs,
                                    spec,
                                    env,
                                ) {
                                    Ok(key) => key,
                                    Err(_) => return,
                                };
                                candidates_total += 1;
                                let node = Node {
                                    nt_idx,
                                    rule_idx,
                                    children: tuple.iter().map(|cand| cand.node).collect(),
                                };
                                match try_insert_transfer_candidate(
                                    file,
                                    spec,
                                    env,
                                    &exact,
                                    relevant_bits,
                                    &label_positions,
                                    nt_idx,
                                    size,
                                    key,
                                    &mut seen,
                                    &mut by_size,
                                    &mut nodes,
                                    node,
                                ) {
                                    Ok(Some(solution)) => found = Some(solution),
                                    Ok(None) | Err(_) => {}
                                }
                            });
                        });
                        if let Some(solution) = found {
                            info!(
                                "multisynth: found solution at size={}, candidates_total={}",
                                size, candidates_total
                            );
                            return Ok(Some(solution));
                        }
                    }
                    ExactRule::GenericTemplate {
                        template,
                        child_nts,
                        base_size,
                    } => {
                        if *base_size > size {
                            continue;
                        }
                        let child_total = size - base_size;
                        if child_nts.is_empty() {
                            let key = summarize_template(
                                template,
                                &[],
                                &[],
                                &[],
                                nt_idx,
                                relevant_bits,
                                &closure_inputs,
                                spec,
                                env,
                                &mut eval_cache,
                            )?;
                            candidates_total += 1;
                            if let Some(solution) = try_insert_transfer_candidate(
                                file,
                                spec,
                                env,
                                &exact,
                                relevant_bits,
                                &label_positions,
                                nt_idx,
                                size,
                                key,
                                &mut seen,
                                &mut by_size,
                                &mut nodes,
                                Node {
                                    nt_idx,
                                    rule_idx,
                                    children: Vec::new(),
                                },
                            )? {
                                info!(
                                    "multisynth: found solution at size={}, candidates_total={}",
                                    size, candidates_total
                                );
                                return Ok(Some(solution));
                            }
                            continue;
                        }
                        if child_total < child_nts.len() {
                            continue;
                        }
                        let mut found = None;
                        let mut splits = Vec::with_capacity(child_nts.len());
                        for_each_size_split(child_total, child_nts.len(), &mut splits, &mut |sizes| {
                            if found.is_some() {
                                return;
                            }
                            let pools = child_nts
                                .iter()
                                .zip(sizes.iter())
                                .map(|(child_nt, child_size)| {
                                    by_size[*child_nt]
                                        .get(*child_size)
                                        .cloned()
                                        .unwrap_or_default()
                                })
                                .collect::<Vec<_>>();
                            if pools.iter().any(|pool| pool.is_empty()) {
                                return;
                            }
                            let pool_refs =
                                pools.iter().map(Vec::as_slice).collect::<Vec<_>>();
                            let mut tuple = Vec::with_capacity(child_nts.len());
                            for_each_candidate_tuple(&pool_refs, &mut tuple, &mut |tuple| {
                                let child_keys =
                                    tuple.iter().map(|cand| cand.key.clone()).collect::<Vec<_>>();
                                let child_bits = child_nts
                                    .iter()
                                    .map(|child_nt| relevant_bits[*child_nt].as_slice())
                                    .collect::<Vec<_>>();
                                let child_widths = child_nts
                                    .iter()
                                    .map(|child_nt| nt_widths[*child_nt])
                                    .collect::<Vec<_>>();
                                let key = match summarize_template(
                                    template,
                                    &child_keys,
                                    &child_bits,
                                    &child_widths,
                                    nt_idx,
                                    relevant_bits,
                                    &closure_inputs,
                                    spec,
                                    env,
                                    &mut eval_cache,
                                ) {
                                    Ok(key) => key,
                                    Err(_) => return,
                                };
                                candidates_total += 1;
                                let node = Node {
                                    nt_idx,
                                    rule_idx,
                                    children: tuple.iter().map(|cand| cand.node).collect(),
                                };
                                match try_insert_transfer_candidate(
                                    file,
                                    spec,
                                    env,
                                    &exact,
                                    relevant_bits,
                                    &label_positions,
                                    nt_idx,
                                    size,
                                    key,
                                    &mut seen,
                                    &mut by_size,
                                    &mut nodes,
                                    node,
                                ) {
                                    Ok(Some(solution)) => found = Some(solution),
                                    Ok(None) | Err(_) => {}
                                }
                            });
                        });
                        if let Some(solution) = found {
                            info!(
                                "multisynth: found solution at size={}, candidates_total={}",
                                size, candidates_total
                            );
                            return Ok(Some(solution));
                        }
                    }
                }
            }
        }
        loop {
            let mut changed = false;
            for (nt_idx, (_, rules)) in exact.nts.iter().enumerate() {
                for (rule_idx, rule) in rules.iter().enumerate() {
                    let ExactRule::Alias(child_nt) = rule else {
                        continue;
                    };
                    let staged = by_size[*child_nt][size].clone();
                    let before = by_size[nt_idx][size].len();
                    for cand in staged {
                        candidates_total += 1;
                        if let Some(solution) = try_insert_transfer_candidate(
                            file,
                            spec,
                            env,
                            &exact,
                            relevant_bits,
                            &label_positions,
                            nt_idx,
                            size,
                            cand.key.clone(),
                            &mut seen,
                            &mut by_size,
                            &mut nodes,
                            Node {
                                nt_idx,
                                rule_idx,
                                children: vec![cand.node],
                            },
                        )? {
                            info!(
                                "multisynth: found solution at size={}, candidates_total={}",
                                size, candidates_total
                            );
                            return Ok(Some(solution));
                        }
                    }
                    changed |= by_size[nt_idx][size].len() > before;
                }
            }
            if !changed {
                break;
            }
        }
        info!(
            "multisynth: size={} start_candidates={} total_seen_start={}",
            size,
            by_size[exact.start][size].len(),
            seen[exact.start].len()
        );
    }
    Ok(None)
}

fn search_single_bottom_up(
    spec: &SingleSynthSpec,
    env: &deffun::Environ,
    relevant_bits: &[Vec<usize>],
    closure_bits: &[usize],
) -> parse::Result<Option<OwnedExpr>> {
    let exact = build_exact_grammar_for_synth(spec.synth, spec.synth.name, spec.bits)?;
    let nt_widths = exact
        .nts
        .iter()
        .map(|(_, rules)| relevance::nt_output_bits(rules))
        .collect::<Vec<_>>();
    let start_rel = &relevant_bits[exact.start];
    if start_rel.is_empty() {
        return Ok(None);
    }
    let domain_size = 1usize << closure_bits.len();
    let closure_inputs = (0..domain_size)
        .map(|mask| full_value_from_mask(mask, spec.bits, closure_bits))
        .collect::<Vec<_>>();
    let label_positions = spec
        .labels
        .iter()
        .map(|(bit, expected)| {
            start_rel
                .iter()
                .position(|b| b == bit)
                .map(|idx| (idx, *expected))
                .ok_or_else(|| {
                    new_custom_error_span(
                        format!("single-closure: label bit {bit} missing from relevant set"),
                        empty_span(),
                    )
                })
        })
        .collect::<parse::Result<Vec<_>>>()?;

    let nt_count = exact.nts.len();
    let mut by_size = vec![vec![Vec::<TransferCandidate>::new()]; nt_count];
    let mut seen = (0..nt_count)
        .map(|_| FxHashMap::<TransferKey, usize>::default())
        .collect::<Vec<_>>();
    let mut nodes = Vec::<Node>::new();
    let mut eval_cache = ExactEvalCache::default();
    let mut apply_cache = FxHashMap::<SingleApplySummaryCacheKey, TransferKey>::default();
    let mut candidates_total = 0usize;

    for size in 1.. {
        for buckets in &mut by_size {
            buckets.push(Vec::new());
        }
        for (nt_idx, (_, rules)) in exact.nts.iter().enumerate() {
            for (rule_idx, rule) in rules.iter().enumerate() {
                match rule {
                    ExactRule::Alias(_) => {}
                    ExactRule::Leaf(expr) => {
                        if size != 1 {
                            continue;
                        }
                        let key = summarize_single_leaf(
                            expr,
                            nt_idx,
                            relevant_bits,
                            &closure_inputs,
                            spec,
                            env,
                            &mut eval_cache,
                        )?;
                        candidates_total += 1;
                        if let Some(solution) = try_insert_single_transfer_candidate(
                            spec,
                            env,
                            &exact,
                            &label_positions,
                            nt_idx,
                            size,
                            key,
                            &mut seen,
                            &mut by_size,
                            &mut nodes,
                            Node { nt_idx, rule_idx, children: Vec::new() },
                        )? {
                            info!(
                                "single-closure: found solution at size={}, candidates_total={}",
                                size, candidates_total
                            );
                            return Ok(Some(solution));
                        }
                    }
                    ExactRule::Unary { fid, child_nt } => {
                        if size < 2 {
                            continue;
                        }
                        let child_size = size - 1;
                        let children = by_size[*child_nt].get(child_size).cloned().unwrap_or_default();
                        for child in children {
                            let key = summarize_single_apply(
                                *fid,
                                &[child.key.clone()],
                                &[relevant_bits[*child_nt].as_slice()],
                                &[nt_widths[*child_nt]],
                                &relevant_bits[nt_idx],
                                &closure_inputs,
                                spec,
                                env,
                                &mut apply_cache,
                            )?;
                            candidates_total += 1;
                            if let Some(solution) = try_insert_single_transfer_candidate(
                                spec,
                                env,
                                &exact,
                                &label_positions,
                                nt_idx,
                                size,
                                key,
                                &mut seen,
                                &mut by_size,
                                &mut nodes,
                                Node { nt_idx, rule_idx, children: vec![child.node] },
                            )? {
                                info!(
                                    "single-closure: found solution at size={}, candidates_total={}",
                                    size, candidates_total
                                );
                                return Ok(Some(solution));
                            }
                        }
                    }
                    ExactRule::Binary { fid, lhs_nt, rhs_nt } => {
                        if size < 3 {
                            continue;
                        }
                        for lhs_size in 1..(size - 1) {
                            let rhs_size = size - 1 - lhs_size;
                            let lhs_pool = by_size[*lhs_nt].get(lhs_size).cloned().unwrap_or_default();
                            let rhs_pool = by_size[*rhs_nt].get(rhs_size).cloned().unwrap_or_default();
                            if lhs_pool.is_empty() || rhs_pool.is_empty() {
                                continue;
                            }
                            for lhs in &lhs_pool {
                                for rhs in &rhs_pool {
                                    let key = summarize_single_apply(
                                        *fid,
                                        &[lhs.key.clone(), rhs.key.clone()],
                                        &[
                                            relevant_bits[*lhs_nt].as_slice(),
                                            relevant_bits[*rhs_nt].as_slice(),
                                        ],
                                        &[nt_widths[*lhs_nt], nt_widths[*rhs_nt]],
                                        &relevant_bits[nt_idx],
                                        &closure_inputs,
                                        spec,
                                        env,
                                        &mut apply_cache,
                                    )?;
                                    candidates_total += 1;
                                    if let Some(solution) = try_insert_single_transfer_candidate(
                                        spec,
                                        env,
                                        &exact,
                                        &label_positions,
                                        nt_idx,
                                        size,
                                        key,
                                        &mut seen,
                                        &mut by_size,
                                        &mut nodes,
                                        Node { nt_idx, rule_idx, children: vec![lhs.node, rhs.node] },
                                    )? {
                                        info!(
                                            "single-closure: found solution at size={}, candidates_total={}",
                                            size, candidates_total
                                        );
                                        return Ok(Some(solution));
                                    }
                                }
                            }
                        }
                    }
                    ExactRule::Nary { fid, child_nts } => {
                        if size <= child_nts.len() {
                            continue;
                        }
                        let child_total = size - 1;
                        let mut found = None;
                        let mut splits = Vec::with_capacity(child_nts.len());
                        for_each_size_split(child_total, child_nts.len(), &mut splits, &mut |sizes| {
                            if found.is_some() {
                                return;
                            }
                            let pools = child_nts
                                .iter()
                                .zip(sizes.iter())
                                .map(|(child_nt, child_size)| {
                                    by_size[*child_nt].get(*child_size).cloned().unwrap_or_default()
                                })
                                .collect::<Vec<_>>();
                            if pools.iter().any(|pool| pool.is_empty()) {
                                return;
                            }
                            let pool_refs = pools.iter().map(Vec::as_slice).collect::<Vec<_>>();
                            let mut tuple = Vec::with_capacity(child_nts.len());
                            for_each_candidate_tuple(&pool_refs, &mut tuple, &mut |tuple| {
                                let child_keys = tuple.iter().map(|cand| cand.key.clone()).collect::<Vec<_>>();
                                let child_bits = child_nts
                                    .iter()
                                    .map(|child_nt| relevant_bits[*child_nt].as_slice())
                                    .collect::<Vec<_>>();
                                let child_widths = child_nts.iter().map(|child_nt| nt_widths[*child_nt]).collect::<Vec<_>>();
                                let key = match summarize_single_apply(
                                    *fid,
                                    &child_keys,
                                    &child_bits,
                                    &child_widths,
                                    &relevant_bits[nt_idx],
                                    &closure_inputs,
                                    spec,
                                    env,
                                    &mut apply_cache,
                                ) {
                                    Ok(key) => key,
                                    Err(_) => return,
                                };
                                candidates_total += 1;
                                let node = Node {
                                    nt_idx,
                                    rule_idx,
                                    children: tuple.iter().map(|cand| cand.node).collect(),
                                };
                                match try_insert_single_transfer_candidate(
                                    spec,
                                    env,
                                    &exact,
                                    &label_positions,
                                    nt_idx,
                                    size,
                                    key,
                                    &mut seen,
                                    &mut by_size,
                                    &mut nodes,
                                    node,
                                ) {
                                    Ok(Some(solution)) => found = Some(solution),
                                    Ok(None) | Err(_) => {}
                                }
                            });
                        });
                        if let Some(solution) = found {
                            info!(
                                "single-closure: found solution at size={}, candidates_total={}",
                                size, candidates_total
                            );
                            return Ok(Some(solution));
                        }
                    }
                    ExactRule::GenericTemplate { template, child_nts, base_size } => {
                        if *base_size > size {
                            continue;
                        }
                        let child_total = size - base_size;
                        if child_nts.is_empty() {
                            let key = summarize_single_template(
                                template,
                                &[],
                                &[],
                                &[],
                                nt_idx,
                                relevant_bits,
                                &closure_inputs,
                                spec,
                                env,
                                &mut eval_cache,
                            )?;
                            candidates_total += 1;
                            if let Some(solution) = try_insert_single_transfer_candidate(
                                spec,
                                env,
                                &exact,
                                &label_positions,
                                nt_idx,
                                size,
                                key,
                                &mut seen,
                                &mut by_size,
                                &mut nodes,
                                Node { nt_idx, rule_idx, children: Vec::new() },
                            )? {
                                info!(
                                    "single-closure: found solution at size={}, candidates_total={}",
                                    size, candidates_total
                                );
                                return Ok(Some(solution));
                            }
                            continue;
                        }
                        if child_total < child_nts.len() {
                            continue;
                        }
                        let mut found = None;
                        let mut splits = Vec::with_capacity(child_nts.len());
                        for_each_size_split(child_total, child_nts.len(), &mut splits, &mut |sizes| {
                            if found.is_some() {
                                return;
                            }
                            let pools = child_nts
                                .iter()
                                .zip(sizes.iter())
                                .map(|(child_nt, child_size)| {
                                    by_size[*child_nt].get(*child_size).cloned().unwrap_or_default()
                                })
                                .collect::<Vec<_>>();
                            if pools.iter().any(|pool| pool.is_empty()) {
                                return;
                            }
                            let pool_refs = pools.iter().map(Vec::as_slice).collect::<Vec<_>>();
                            let mut tuple = Vec::with_capacity(child_nts.len());
                            for_each_candidate_tuple(&pool_refs, &mut tuple, &mut |tuple| {
                                let child_keys = tuple.iter().map(|cand| cand.key.clone()).collect::<Vec<_>>();
                                let child_bits = child_nts
                                    .iter()
                                    .map(|child_nt| relevant_bits[*child_nt].as_slice())
                                    .collect::<Vec<_>>();
                                let child_widths = child_nts.iter().map(|child_nt| nt_widths[*child_nt]).collect::<Vec<_>>();
                                let key = match summarize_single_template(
                                    template,
                                    &child_keys,
                                    &child_bits,
                                    &child_widths,
                                    nt_idx,
                                    relevant_bits,
                                    &closure_inputs,
                                    spec,
                                    env,
                                    &mut eval_cache,
                                ) {
                                    Ok(key) => key,
                                    Err(_) => return,
                                };
                                candidates_total += 1;
                                let node = Node {
                                    nt_idx,
                                    rule_idx,
                                    children: tuple.iter().map(|cand| cand.node).collect(),
                                };
                                match try_insert_single_transfer_candidate(
                                    spec,
                                    env,
                                    &exact,
                                    &label_positions,
                                    nt_idx,
                                    size,
                                    key,
                                    &mut seen,
                                    &mut by_size,
                                    &mut nodes,
                                    node,
                                ) {
                                    Ok(Some(solution)) => found = Some(solution),
                                    Ok(None) | Err(_) => {}
                                }
                            });
                        });
                        if let Some(solution) = found {
                            info!(
                                "single-closure: found solution at size={}, candidates_total={}",
                                size, candidates_total
                            );
                            return Ok(Some(solution));
                        }
                    }
                }
            }
        }
        loop {
            let mut changed = false;
            for (nt_idx, (_, rules)) in exact.nts.iter().enumerate() {
                for (rule_idx, rule) in rules.iter().enumerate() {
                    let ExactRule::Alias(child_nt) = rule else {
                        continue;
                    };
                    let staged = by_size[*child_nt][size].clone();
                    let before = by_size[nt_idx][size].len();
                    for cand in staged {
                        candidates_total += 1;
                        if let Some(solution) = try_insert_single_transfer_candidate(
                            spec,
                            env,
                            &exact,
                            &label_positions,
                            nt_idx,
                            size,
                            cand.key.clone(),
                            &mut seen,
                            &mut by_size,
                            &mut nodes,
                            Node { nt_idx, rule_idx, children: vec![cand.node] },
                        )? {
                            info!(
                                "single-closure: found solution at size={}, candidates_total={}",
                                size, candidates_total
                            );
                            return Ok(Some(solution));
                        }
                    }
                    changed |= by_size[nt_idx][size].len() > before;
                }
            }
            if !changed {
                break;
            }
        }
        info!(
            "single-closure: size={} start_candidates={} total_seen_start={}",
            size,
            by_size[exact.start][size].len(),
            seen[exact.start].len()
        );
    }
    unreachable!("single-closure bottom-up search should either find a solution or diverge")
}

fn build_exact_grammar(spec: &MultiSynthSpec) -> parse::Result<ExactGrammar<'static>> {
    build_exact_grammar_for_synth(spec.g, spec.rhs_s_name, spec.bits)
}

fn build_exact_grammar_for_synth(
    synth: SynthFunView<'_>,
    closure_name: &str,
    bits: usize,
) -> parse::Result<ExactGrammar<'static>> {
    let grammar_def = synth
        .grammar
        .ok_or_else(|| new_custom_error_span("multisynth: g has no grammar".into(), empty_span()))?;
    let cfg = Cfg::from_grammar(grammar_def, None)?;
    let leaf_name: &'static str = Box::leak(closure_name.to_string().into_boxed_str());
    let problem = SynthProblem {
        name: Box::leak(synth.name.to_string().into_boxed_str()),
        args: vec![leaf_name],
        arg_decls: vec![SortedVar {
            name: leaf_name.to_string(),
            sort: synth.ret.clone(),
        }],
        cfg,
        span: empty_span(),
        description: String::new(),
        chatgpt_exprs: Vec::new(),
        bits,
        ret_sort: synth.ret.clone(),
        axioms: None,
    };
    let multi = MultiConfig::from_problem(&problem)?;
    Ok(compile_exact_grammar(&multi))
}

fn try_insert_transfer_candidate(
    file: &SyGuSFile,
    spec: &MultiSynthSpec,
    env: &deffun::Environ,
    exact: &ExactGrammar<'_>,
    relevant_bits: &[Vec<usize>],
    label_positions: &[(usize, bool)],
    nt_idx: usize,
    size: usize,
    key: TransferKey,
    seen: &mut [FxHashMap<TransferKey, usize>],
    by_size: &mut [Vec<Vec<TransferCandidate>>],
    nodes: &mut Vec<Node>,
    node: Node,
) -> parse::Result<Option<String>> {
    if nt_idx == exact.start {
        if table_matches_labels(&key, label_positions) {
            let node_id = intern_node(nodes, node);
            let g_expr = materialize_node(node_id, exact, nodes)
                .ok_or_else(|| new_custom_error_span("multisynth: failed to materialize node".into(), empty_span()))?;
            let rhs_s = compute_full_lfp(env, &g_expr, spec.rhs_s_name, spec.bits)?;
            let solution = format_solution(file, spec, &g_expr, &rhs_s);
            return Ok(Some(solution));
        }
    }
    match seen[nt_idx].entry(key.clone()) {
        Entry::Occupied(_) => Ok(None),
        Entry::Vacant(entry) => {
            entry.insert(size);
            let node_id = intern_node(nodes, node);
            by_size[nt_idx][size].push(TransferCandidate { node: node_id, key });
            Ok(None)
        }
    }
}

fn try_insert_single_transfer_candidate(
    spec: &SingleSynthSpec,
    env: &deffun::Environ,
    exact: &ExactGrammar<'_>,
    label_positions: &[(usize, bool)],
    nt_idx: usize,
    size: usize,
    key: TransferKey,
    seen: &mut [FxHashMap<TransferKey, usize>],
    by_size: &mut [Vec<Vec<TransferCandidate>>],
    nodes: &mut Vec<Node>,
    node: Node,
) -> parse::Result<Option<OwnedExpr>> {
    if nt_idx == exact.start && table_matches_labels(&key, label_positions) {
        let node_id = intern_node(nodes, node);
        let g_expr = materialize_node(node_id, exact, nodes)
            .ok_or_else(|| new_custom_error_span("single-closure: failed to materialize node".into(), empty_span()))?;
        let _ = compute_full_lfp(env, &g_expr, spec.synth.name, spec.bits)?;
        return Ok(Some(g_expr));
    }
    match seen[nt_idx].entry(key.clone()) {
        Entry::Occupied(_) => Ok(None),
        Entry::Vacant(entry) => {
            entry.insert(size);
            let node_id = intern_node(nodes, node);
            by_size[nt_idx][size].push(TransferCandidate { node: node_id, key });
            Ok(None)
        }
    }
}

fn table_matches_labels(key: &TransferKey, label_positions: &[(usize, bool)]) -> bool {
    let mut state = 0usize;
    let width = label_positions.len();
    for _ in 0..=width {
        let next = label_positions.iter().enumerate().fold(0usize, |acc, (state_bit, (output_pos, _))| {
            let bit = key.0[state]
                .get(output_pos / 64)
                .map(|word| ((word >> (output_pos % 64)) & 1) == 1)
                .unwrap_or(false);
            if bit {
                acc | (1usize << state_bit)
            } else {
                acc
            }
        });
        if next == state {
            return label_positions
                .iter()
                .all(|(idx, expected)| (((state >> idx) & 1) == 1) == *expected);
        }
        state = next;
    }
    false
}

fn compute_full_lfp(
    env: &deffun::Environ,
    g_expr: &OwnedExpr,
    rhs_s_name: &str,
    bits: usize,
) -> parse::Result<Value> {
    let mut rhs_s = Value::from_u64(0, bits);
    for _ in 0..=bits {
        let next = eval_owned_with_closure(g_expr, env, &rhs_s, rhs_s_name)?;
        if next == rhs_s {
            return Ok(next);
        }
        rhs_s = next;
    }
    Err(new_custom_error_span(
        "multisynth: full LFP did not converge".into(),
        empty_span(),
    ))
}

fn summarize_leaf(
    expr: &OwnedExpr,
    nt_idx: usize,
    relevant_bits: &[Vec<usize>],
    closure_inputs: &[Value],
    spec: &MultiSynthSpec,
    env: &deffun::Environ,
    _eval_cache: &mut ExactEvalCache,
) -> parse::Result<TransferKey> {
    Ok(TransferKey(
        closure_inputs
            .iter()
            .map(|closure_input| {
                eval_owned_with_closure(expr, env, closure_input, spec.rhs_s_name)
                    .map(|value| value.project_bits(&relevant_bits[nt_idx]))
            })
            .collect::<parse::Result<Vec<_>>>()?,
    ))
}

fn summarize_single_leaf(
    expr: &OwnedExpr,
    nt_idx: usize,
    relevant_bits: &[Vec<usize>],
    closure_inputs: &[Value],
    spec: &SingleSynthSpec,
    env: &deffun::Environ,
    eval_cache: &mut ExactEvalCache,
) -> parse::Result<TransferKey> {
    Ok(TransferKey(
        closure_inputs
            .iter()
            .map(|closure_input| {
                eval_owned_with_closure(expr, env, closure_input, spec.synth.name)
                    .map(|value| value.project_bits(&relevant_bits[nt_idx]))
            })
            .collect::<parse::Result<Vec<_>>>()?,
    ))
}

fn summarize_apply(
    fid: usize,
    child_keys: &[TransferKey],
    child_relevant_bits: &[&[usize]],
    child_widths: &[usize],
    output_relevant_bits: &[usize],
    closure_inputs: &[Value],
    spec: &MultiSynthSpec,
    env: &deffun::Environ,
) -> parse::Result<TransferKey> {
    let outputs = closure_inputs
        .iter()
        .enumerate()
        .map(|(idx, closure_input)| {
            let mut args = child_keys
                .iter()
                .zip(child_relevant_bits.iter().zip(child_widths.iter()))
                .map(|(key, (bits, width))| full_value_from_projected(&key.0[idx], *width, bits))
                .collect::<Vec<_>>();
            args.extend(closure_arg_values(
                env,
                fid,
                child_keys.len(),
                closure_input,
                spec.rhs_s_name,
            ));
            env.eval_defined(fid, child_keys.len(), &args)
                .map_err(|_| {
                    new_custom_error_span(
                        format!("multisynth: divide-by-zero in {}", env.name(fid, child_keys.len())),
                        empty_span(),
                    )
                })
        })
        .collect::<parse::Result<Vec<_>>>()?;
    Ok(TransferKey(
        outputs
            .into_iter()
            .map(|v| v.project_bits(output_relevant_bits))
            .collect(),
    ))
}

fn summarize_single_apply(
    fid: usize,
    child_keys: &[TransferKey],
    child_relevant_bits: &[&[usize]],
    child_widths: &[usize],
    output_relevant_bits: &[usize],
    closure_inputs: &[Value],
    spec: &SingleSynthSpec,
    env: &deffun::Environ,
    cache: &mut FxHashMap<SingleApplySummaryCacheKey, TransferKey>,
) -> parse::Result<TransferKey> {
    let cache_key = SingleApplySummaryCacheKey {
        fid,
        child_keys: child_keys.to_vec(),
        output_relevant_bits: output_relevant_bits.to_vec(),
    };
    if let Some(cached) = cache.get(&cache_key) {
        return Ok(cached.clone());
    }
    let outputs = closure_inputs
        .iter()
        .enumerate()
        .map(|(idx, closure_input)| {
            let mut args = child_keys
                .iter()
                .zip(child_relevant_bits.iter().zip(child_widths.iter()))
                .map(|(key, (bits, width))| full_value_from_projected(&key.0[idx], *width, bits))
                .collect::<Vec<_>>();
            args.extend(closure_arg_values(
                env,
                fid,
                child_keys.len(),
                closure_input,
                spec.synth.name,
            ));
            env.eval_defined(fid, child_keys.len(), &args).map_err(|_| {
                new_custom_error_span(
                    format!("single-closure: divide-by-zero in {}", env.name(fid, child_keys.len())),
                    empty_span(),
                )
            })
        })
        .collect::<parse::Result<Vec<_>>>()?;
    let result = TransferKey(
        outputs
            .into_iter()
            .map(|v| v.project_bits(output_relevant_bits))
            .collect(),
    );
    cache.insert(cache_key, result.clone());
    Ok(result)
}

fn summarize_template(
    template: &TemplateExpr,
    child_keys: &[TransferKey],
    child_relevant_bits: &[&[usize]],
    child_widths: &[usize],
    nt_idx: usize,
    relevant_bits: &[Vec<usize>],
    closure_inputs: &[Value],
    spec: &MultiSynthSpec,
    env: &deffun::Environ,
    eval_cache: &mut ExactEvalCache,
) -> parse::Result<TransferKey> {
    let outputs = closure_inputs
        .iter()
        .enumerate()
        .map(|(idx, closure_input)| {
            let child_values = child_keys
                .iter()
                .zip(child_relevant_bits.iter().zip(child_widths.iter()))
                .map(|(key, (bits, width))| full_value_from_projected(&key.0[idx], *width, bits))
                .collect::<Vec<_>>();
            eval_template_with_closure(template, &child_values, closure_input, spec, env, eval_cache)
        })
        .collect::<parse::Result<Vec<_>>>()?;
    Ok(TransferKey(
        outputs
            .into_iter()
            .map(|v| v.project_bits(&relevant_bits[nt_idx]))
            .collect(),
    ))
}

fn summarize_single_template(
    template: &TemplateExpr,
    child_keys: &[TransferKey],
    child_relevant_bits: &[&[usize]],
    child_widths: &[usize],
    nt_idx: usize,
    relevant_bits: &[Vec<usize>],
    closure_inputs: &[Value],
    spec: &SingleSynthSpec,
    env: &deffun::Environ,
    eval_cache: &mut ExactEvalCache,
) -> parse::Result<TransferKey> {
    let outputs = closure_inputs
        .iter()
        .enumerate()
        .map(|(idx, closure_input)| {
            let child_values = child_keys
                .iter()
                .zip(child_relevant_bits.iter().zip(child_widths.iter()))
                .map(|(key, (bits, width))| full_value_from_projected(&key.0[idx], *width, bits))
                .collect::<Vec<_>>();
            eval_single_template_with_closure(
                template,
                &child_values,
                closure_input,
                spec,
                env,
                eval_cache,
            )
        })
        .collect::<parse::Result<Vec<_>>>()?;
    Ok(TransferKey(
        outputs
            .into_iter()
            .map(|v| v.project_bits(&relevant_bits[nt_idx]))
            .collect(),
    ))
}

fn eval_template_with_closure(
    template: &TemplateExpr,
    child_values: &[Value],
    closure_input: &Value,
    spec: &MultiSynthSpec,
    env: &deffun::Environ,
    eval_cache: &mut ExactEvalCache,
) -> parse::Result<Value> {
    match template {
        TemplateExpr::Slot(i) => child_values.get(*i).cloned().ok_or_else(|| {
            new_custom_error_span("multisynth: missing template slot".into(), empty_span())
        }),
        TemplateExpr::Leaf(expr) => eval_owned_with_closure(expr, env, closure_input, spec.rhs_s_name),
        TemplateExpr::App(id, parts) => {
            let values = parts
                .iter()
                .map(|part| eval_template_with_closure(part, child_values, closure_input, spec, env, eval_cache))
                .collect::<parse::Result<Vec<_>>>()?;
            let nargs = values.len();
            let Some(fid) = env.lookup(id.get_name(), nargs) else {
                return Err(new_custom_error_span(
                    format!("multisynth: unknown {}-arity symbol {}", nargs, id.get_name()),
                    empty_span(),
                ));
            };
            let mut args = values;
            args.extend(closure_arg_values(env, fid, nargs, closure_input, spec.rhs_s_name));
            env.eval_defined(fid, nargs, &args)
                .map_err(|_| new_custom_error_span(format!("multisynth: divide-by-zero in {}", id.get_name()), empty_span()))
        }
    }
}

fn eval_single_template_with_closure(
    template: &TemplateExpr,
    child_values: &[Value],
    closure_input: &Value,
    spec: &SingleSynthSpec,
    env: &deffun::Environ,
    eval_cache: &mut ExactEvalCache,
) -> parse::Result<Value> {
    match template {
        TemplateExpr::Slot(i) => child_values.get(*i).cloned().ok_or_else(|| {
            new_custom_error_span("single-closure: missing template slot".into(), empty_span())
        }),
        TemplateExpr::Leaf(expr) => eval_owned_with_closure(expr, env, closure_input, spec.synth.name),
        TemplateExpr::App(id, parts) => {
            let values = parts
                .iter()
                .map(|part| {
                    eval_single_template_with_closure(
                        part,
                        child_values,
                        closure_input,
                        spec,
                        env,
                        eval_cache,
                    )
                })
                .collect::<parse::Result<Vec<_>>>()?;
            let nargs = values.len();
            let Some(fid) = env.lookup(id.get_name(), nargs) else {
                return Err(new_custom_error_span(
                    format!("single-closure: unknown {}-arity symbol {}", nargs, id.get_name()),
                    empty_span(),
                ));
            };
            let mut args = values;
            args.extend(closure_arg_values(env, fid, nargs, closure_input, spec.synth.name));
            env.eval_defined(fid, nargs, &args).map_err(|_| {
                new_custom_error_span(
                    format!("single-closure: divide-by-zero in {}", id.get_name()),
                    empty_span(),
                )
            })
        }
    }
}

fn eval_leaf_value(expr: &OwnedExpr, eval_cache: &mut ExactEvalCache) -> parse::Result<Value> {
    eval_cache
        .leaves
        .entry(expr.clone())
        .or_insert_with(|| expr.eval(&[]).ok())
        .clone()
        .ok_or_else(|| new_custom_error_span("multisynth: failed to evaluate leaf".into(), empty_span()))
}

fn full_value_from_mask(mask: usize, bits: usize, relevant_bits: &[usize]) -> Value {
    let mut words = vec![0u64; bits.div_ceil(64)];
    for (idx, bit) in relevant_bits.iter().enumerate() {
        if ((mask >> idx) & 1) == 1 {
            words[*bit / 64] |= 1u64 << (*bit % 64);
        }
    }
    value_from_words(words, bits)
}

fn full_value_from_projected(projected: &[u64], bits: usize, relevant_bits: &[usize]) -> Value {
    let mut words = vec![0u64; bits.div_ceil(64)];
    for (idx, bit) in relevant_bits.iter().enumerate() {
        if projected
            .get(idx / 64)
            .map(|word| ((word >> (idx % 64)) & 1) == 1)
            .unwrap_or(false)
        {
            words[*bit / 64] |= 1u64 << (*bit % 64);
        }
    }
    value_from_words(words, bits)
}

fn projected_words_to_mask(projected: &[u64], bits: usize) -> usize {
    let mut out = 0usize;
    for idx in 0..bits {
        if projected
            .get(idx / 64)
            .map(|word| ((word >> (idx % 64)) & 1) == 1)
            .unwrap_or(false)
        {
            out |= 1usize << idx;
        }
    }
    out
}

fn value_from_words(words: Vec<u64>, bits: usize) -> Value {
    if bits <= 64 {
        return Value::from_u64(words.first().copied().unwrap_or(0), bits);
    }
    let mut raw = BigUint::zero();
    for (idx, word) in words.into_iter().enumerate() {
        if word != 0 {
            raw |= BigUint::from(word) << (idx * 64);
        }
    }
    Value::from_biguint(raw, bits)
}

fn eval_owned_with_closure(
    expr: &OwnedExpr,
    env: &deffun::Environ,
    rhs_s_value: &Value,
    rhs_s_name: &str,
) -> parse::Result<Value> {
    match expr {
        OwnedExpr::Const(v) => Ok(v.clone()),
        OwnedExpr::Var(_, _) => Ok(rhs_s_value.clone()),
        OwnedExpr::Concat(a, b) => Ok(eval_owned_with_closure(a, env, rhs_s_value, rhs_s_name)?
            .concat(&eval_owned_with_closure(b, env, rhs_s_value, rhs_s_name)?)),
        OwnedExpr::Extract(a, hi, lo) => Ok(eval_owned_with_closure(a, env, rhs_s_value, rhs_s_name)?
            .extract(*hi, *lo)),
        OwnedExpr::Not(a) => Ok(eval_owned_with_closure(a, env, rhs_s_value, rhs_s_name)?.bitnot()),
        OwnedExpr::Neg(a) => Ok(eval_owned_with_closure(a, env, rhs_s_value, rhs_s_name)?.neg()),
        OwnedExpr::Add(a, b) => Ok(eval_owned_with_closure(a, env, rhs_s_value, rhs_s_name)?
            .add(eval_owned_with_closure(b, env, rhs_s_value, rhs_s_name)?)),
        OwnedExpr::Xor(a, b) => Ok(eval_owned_with_closure(a, env, rhs_s_value, rhs_s_name)?
            .bitxor(eval_owned_with_closure(b, env, rhs_s_value, rhs_s_name)?)),
        OwnedExpr::And(a, b) => Ok(eval_owned_with_closure(a, env, rhs_s_value, rhs_s_name)?
            .bitand(eval_owned_with_closure(b, env, rhs_s_value, rhs_s_name)?)),
        OwnedExpr::Or(a, b) => Ok(eval_owned_with_closure(a, env, rhs_s_value, rhs_s_name)?
            .bitor(eval_owned_with_closure(b, env, rhs_s_value, rhs_s_name)?)),
        OwnedExpr::Mul(a, b) => Ok(eval_owned_with_closure(a, env, rhs_s_value, rhs_s_name)?
            .mul(eval_owned_with_closure(b, env, rhs_s_value, rhs_s_name)?)),
        OwnedExpr::Sub(a, b) => Ok(eval_owned_with_closure(a, env, rhs_s_value, rhs_s_name)?
            .sub(eval_owned_with_closure(b, env, rhs_s_value, rhs_s_name)?)),
        OwnedExpr::LShr(a, b) => Ok(eval_owned_with_closure(a, env, rhs_s_value, rhs_s_name)?
            .lshr(eval_owned_with_closure(b, env, rhs_s_value, rhs_s_name)?)),
        OwnedExpr::AShr(a, b) => Ok(eval_owned_with_closure(a, env, rhs_s_value, rhs_s_name)?
            .ashr(eval_owned_with_closure(b, env, rhs_s_value, rhs_s_name)?)),
        OwnedExpr::Shl(a, b) => Ok(eval_owned_with_closure(a, env, rhs_s_value, rhs_s_name)?
            .shl(eval_owned_with_closure(b, env, rhs_s_value, rhs_s_name)?)),
        OwnedExpr::UDiv(a, b) => eval_owned_with_closure(a, env, rhs_s_value, rhs_s_name)?
            .udiv(eval_owned_with_closure(b, env, rhs_s_value, rhs_s_name)?)
            .ok_or_else(|| new_custom_error_span("multisynth: divide-by-zero".into(), empty_span())),
        OwnedExpr::URem(a, b) => eval_owned_with_closure(a, env, rhs_s_value, rhs_s_name)?
            .urem(eval_owned_with_closure(b, env, rhs_s_value, rhs_s_name)?)
            .ok_or_else(|| new_custom_error_span("multisynth: divide-by-zero".into(), empty_span())),
        OwnedExpr::SDiv(a, b) => eval_owned_with_closure(a, env, rhs_s_value, rhs_s_name)?
            .sdiv(eval_owned_with_closure(b, env, rhs_s_value, rhs_s_name)?)
            .ok_or_else(|| new_custom_error_span("multisynth: divide-by-zero".into(), empty_span())),
        OwnedExpr::SRem(a, b) => eval_owned_with_closure(a, env, rhs_s_value, rhs_s_name)?
            .srem(eval_owned_with_closure(b, env, rhs_s_value, rhs_s_name)?)
            .ok_or_else(|| new_custom_error_span("multisynth: divide-by-zero".into(), empty_span())),
        OwnedExpr::Fop0Dyn(id) => {
            let args = closure_arg_values(env, *id, 0, rhs_s_value, rhs_s_name);
            env.eval_defined(*id, 0, &args)
                .map_err(|_| new_custom_error_span(format!("multisynth: divide-by-zero in {}", env.name(*id, 0)), empty_span()))
        }
        OwnedExpr::Fop1Dyn(id, a) => {
            let mut args = vec![eval_owned_with_closure(a, env, rhs_s_value, rhs_s_name)?];
            args.extend(closure_arg_values(env, *id, 1, rhs_s_value, rhs_s_name));
            env.eval_defined(*id, 1, &args)
                .map_err(|_| new_custom_error_span(format!("multisynth: divide-by-zero in {}", env.name(*id, 1)), empty_span()))
        }
        OwnedExpr::Fop2Dyn(id, a, b) => {
            let mut args = vec![
                eval_owned_with_closure(a, env, rhs_s_value, rhs_s_name)?,
                eval_owned_with_closure(b, env, rhs_s_value, rhs_s_name)?,
            ];
            args.extend(closure_arg_values(env, *id, 2, rhs_s_value, rhs_s_name));
            env.eval_defined(*id, 2, &args)
                .map_err(|_| new_custom_error_span(format!("multisynth: divide-by-zero in {}", env.name(*id, 2)), empty_span()))
        }
        OwnedExpr::FopDyn(id, exprs) => {
            let nargs = exprs.len();
            let mut args = exprs
                .iter()
                .map(|arg| eval_owned_with_closure(arg, env, rhs_s_value, rhs_s_name))
                .collect::<parse::Result<Vec<_>>>()?;
            args.extend(closure_arg_values(env, *id, nargs, rhs_s_value, rhs_s_name));
            env.eval_defined(*id, nargs, &args)
                .map_err(|_| new_custom_error_span(format!("multisynth: divide-by-zero in {}", env.name(*id, nargs)), empty_span()))
        }
        OwnedExpr::Ite(cond, then_e, else_e) => {
            let c = eval_owned_with_closure(cond, env, rhs_s_value, rhs_s_name)?;
            if c.is_zero() {
                eval_owned_with_closure(then_e, env, rhs_s_value, rhs_s_name)
            } else {
                eval_owned_with_closure(else_e, env, rhs_s_value, rhs_s_name)
            }
        }
        OwnedExpr::Let(_, _, _) => expr
            .eval(std::slice::from_ref(rhs_s_value))
            .map_err(|_| new_custom_error_span("multisynth: let-eval failed".into(), empty_span())),
    }
}

fn term_to_owned_expr(term: &Term) -> parse::Result<OwnedExpr> {
    match term {
        Term::Leaf(name) => {
            let fid = deffun::ENV.lookup(name, 0).ok_or_else(|| {
                new_custom_error_span(format!("multisynth: unknown 0-arity symbol {name}"), empty_span())
            })?;
            Ok(OwnedExpr::Fop0Dyn(fid))
        }
        Term::App(name, args) => {
            let child_exprs = args
                .iter()
                .map(term_to_owned_expr)
                .collect::<parse::Result<Vec<_>>>()?;
            let fid = deffun::ENV.lookup(name, child_exprs.len()).ok_or_else(|| {
                new_custom_error_span(
                    format!("multisynth: unknown {}-arity symbol {name}", child_exprs.len()),
                    empty_span(),
                )
            })?;
            Ok(match child_exprs.len() {
                1 => OwnedExpr::Fop1Dyn(fid, Box::new(child_exprs[0].clone())),
                2 => OwnedExpr::Fop2Dyn(
                    fid,
                    Box::new(child_exprs[0].clone()),
                    Box::new(child_exprs[1].clone()),
                ),
                _ => OwnedExpr::FopDyn(fid, child_exprs),
            })
        }
    }
}

fn display_sort(sort: &Sort) -> String {
    format!("{}", sort)
}

fn display_sort_from_name(file: &SyGuSFile, name: &str) -> Option<String> {
    for cmd in &file.cmds {
        if let SyGuSCmd::SynthFun(n, _, ret, _) = cmd {
            if n == name {
                return Some(display_sort(ret));
            }
        }
    }
    None
}

fn value_to_binstr(v: &Value, bits: usize) -> String {
    let mut out = String::with_capacity(bits);
    for i in (0..bits).rev() {
        out.push(if v.bit(i) { '1' } else { '0' });
    }
    out
}

// ---------------------------------------------------------------------------
//  Term enumeration over the synth-fun grammar
// ---------------------------------------------------------------------------

/// A concrete g term: leaf reference or application of a constructor name.
#[derive(Clone, Debug)]
enum Term {
    /// Reference to a 0-arity define-fun or the cfg.rhs.S placeholder.
    Leaf(String),
    /// Application of a (named) constructor to children.
    App(String, Vec<Term>),
}

impl Term {
    fn to_sygus(&self) -> String {
        match self {
            Term::Leaf(name) => name.clone(),
            Term::App(name, args) => {
                let inside = args.iter().map(|a| a.to_sygus()).collect::<Vec<_>>().join(" ");
                format!("({} {})", name, inside)
            }
        }
    }
}

/// Walks the synth-fun grammar and enumerates terms.  Smallest first.
/// Terms are produced eagerly into vectors; OK for small grammars.
struct TermEnumerator<'a> {
    grammar: &'a GrammarDef,
}

impl<'a> TermEnumerator<'a> {
    fn new(grammar: &'a GrammarDef) -> Self {
        Self { grammar }
    }

    fn start_nt(&self) -> &str {
        &self.grammar.grouped_rule_lists[0].symbol
    }

    fn nt_rules(&self, nt: &str) -> &[sygus_parser::ast::SyGuSGTerm] {
        self.grammar
            .grouped_rule_lists
            .iter()
            .find(|grl| grl.symbol == nt)
            .map(|grl| grl.terms.as_slice())
            .unwrap_or(&[])
    }

    /// Returns all terms produced by the start nonterminal with exactly the given size.
    fn terms_of_size(&self, size: usize) -> Vec<Term> {
        let mut cache: std::collections::HashMap<(String, usize), Vec<Term>> =
            std::collections::HashMap::new();
        self.terms_of_nt_size(self.start_nt(), size, &mut cache)
    }

    fn terms_of_nt_size(
        &self,
        nt: &str,
        size: usize,
        cache: &mut std::collections::HashMap<(String, usize), Vec<Term>>,
    ) -> Vec<Term> {
        if size == 0 {
            return Vec::new();
        }
        if let Some(c) = cache.get(&(nt.to_string(), size)) {
            return c.clone();
        }
        let mut out = Vec::new();
        for rule in self.nt_rules(nt) {
            self.extend_from_rule(rule, size, &mut out, cache);
        }
        cache.insert((nt.to_string(), size), out.clone());
        out
    }

    fn extend_from_rule(
        &self,
        rule: &sygus_parser::ast::SyGuSGTerm,
        size: usize,
        out: &mut Vec<Term>,
        cache: &mut std::collections::HashMap<(String, usize), Vec<Term>>,
    ) {
        let term = match rule {
            sygus_parser::ast::SyGuSGTerm::SyGuSTerm(t) => t,
            _ => return, // skip (Constant T)/(Variable T) — not used in g's grammar
        };
        match term {
            SyGuSTerm::Identifier(id) => {
                if size != 1 {
                    return;
                }
                let name = id.get_name();
                // If the identifier matches another nonterminal, expand it.
                if self.nt_rules(name.as_ref()).is_empty() {
                    out.push(Term::Leaf(name.to_string()));
                } else {
                    let nested = self.terms_of_nt_size(name.as_ref(), size, cache);
                    out.extend(nested);
                }
            }
            SyGuSTerm::Application(id, args) => {
                if size < 1 + args.len() {
                    return;
                }
                let remaining = size - 1;
                let child_nts: Vec<&str> = args
                    .iter()
                    .filter_map(|a| match a {
                        SyGuSTerm::Identifier(child_id) => {
                            let n = child_id.get_name();
                            if self.nt_rules(n.as_ref()).is_empty() {
                                None
                            } else {
                                // We need a 'static str-ish or we just lookup again later via Term
                                Some(())
                            }
                        }
                        _ => None,
                    })
                    .map(|()| "")
                    .collect();
                let _ = child_nts; // placeholder
                // Distribute remaining size across children using the args' nonterminals.
                let nts: Vec<String> = args
                    .iter()
                    .filter_map(|a| match a {
                        SyGuSTerm::Identifier(child_id) => Some(child_id.get_name().to_string()),
                        _ => None,
                    })
                    .collect();
                if nts.len() != args.len() {
                    return; // unsupported non-identifier arg position
                }
                // Allocate sizes summing to `remaining`, with each part ≥ 1.
                each_split(remaining, nts.len(), &mut |sizes| {
                    let per_child: Vec<Vec<Term>> = sizes
                        .iter()
                        .zip(nts.iter())
                        .map(|(s, nt)| self.terms_of_nt_size(nt, *s, cache))
                        .collect();
                    if per_child.iter().any(|v| v.is_empty()) {
                        return;
                    }
                    cartesian_product(&per_child, &mut |children| {
                        out.push(Term::App(id.get_name().to_string(), children.to_vec()));
                    });
                });
            }
            _ => {}
        }
    }
}

/// Enumerate compositions of `total` into exactly `parts` positive integers.
fn each_split(total: usize, parts: usize, f: &mut impl FnMut(&[usize])) {
    if parts == 0 {
        if total == 0 {
            f(&[]);
        }
        return;
    }
    if parts == 1 {
        if total >= 1 {
            f(&[total]);
        }
        return;
    }
    for first in 1..=total.saturating_sub(parts - 1) {
        each_split_inner(total - first, parts - 1, first, &mut Vec::new(), f);
    }
}

fn each_split_inner(
    remaining: usize,
    parts: usize,
    head: usize,
    acc: &mut Vec<usize>,
    f: &mut impl FnMut(&[usize]),
) {
    acc.push(head);
    if parts == 0 {
        if remaining == 0 {
            f(acc);
        }
    } else if parts == 1 {
        if remaining >= 1 {
            acc.push(remaining);
            f(acc);
            acc.pop();
        }
    } else {
        for next in 1..=remaining.saturating_sub(parts - 1) {
            each_split_inner(remaining - next, parts - 1, next, acc, f);
        }
    }
    acc.pop();
}

fn cartesian_product(slots: &[Vec<Term>], f: &mut impl FnMut(&[Term])) {
    let mut buf: Vec<Term> = Vec::with_capacity(slots.len());
    cartesian_inner(slots, 0, &mut buf, f);
}

fn cartesian_inner(
    slots: &[Vec<Term>],
    idx: usize,
    buf: &mut Vec<Term>,
    f: &mut impl FnMut(&[Term]),
) {
    if idx == slots.len() {
        f(buf);
        return;
    }
    for item in &slots[idx] {
        buf.push(item.clone());
        cartesian_inner(slots, idx + 1, buf, f);
        buf.pop();
    }
}

// ---------------------------------------------------------------------------
//  Term evaluation against define-funs in the env
// ---------------------------------------------------------------------------

fn eval_term(
    term: &Term,
    env: &deffun::Environ,
    rhs_s_value: &Value,
    rhs_s_name: &str,
    bits: usize,
) -> parse::Result<Value> {
    match term {
        Term::Leaf(name) => {
            if name == rhs_s_name {
                return Ok(rhs_s_value.clone());
            }
            // 0-arity define-fun. May reference closure synth-funs in its body.
            let Some(id) = env.lookup(name, 0) else {
                return Err(new_custom_error_span(
                    format!("multisynth: unknown 0-arity symbol {name}"),
                    empty_span(),
                ));
            };
            let arg_vals = closure_arg_values(env, id, 0, rhs_s_value, rhs_s_name);
            env.eval_defined(id, 0, &arg_vals).map_err(|_| {
                new_custom_error_span(format!("multisynth: divide-by-zero in {name}"), empty_span())
            })
        }
        Term::App(name, args) => {
            let mut arg_vals = Vec::with_capacity(args.len());
            for a in args {
                arg_vals.push(eval_term(a, env, rhs_s_value, rhs_s_name, bits)?);
            }
            let Some(id) = env.lookup(name, args.len()) else {
                return Err(new_custom_error_span(
                    format!("multisynth: unknown {}-arity symbol {name}", args.len()),
                    empty_span(),
                ));
            };
            // Append closure synth-fun values (in declaration order) so the
            // define-fun's body — which may reference them via Var slots
            // beyond the real arity — has all the bindings it needs.
            arg_vals.extend(closure_arg_values(env, id, args.len(), rhs_s_value, rhs_s_name));
            env.eval_defined(id, args.len(), &arg_vals).map_err(|_| {
                new_custom_error_span(
                    format!("multisynth: divide-by-zero in {name}"),
                    empty_span(),
                )
            })
        }
    }
}

/// Resolve the value of each closure synth-fun the define-fun references.
/// The multisynth path knows only one closure synth-fun (the LFP target);
/// any others are bound to zero as a placeholder (and shouldn't appear in
/// well-formed cyk-style problems).
fn closure_arg_values(
    env: &deffun::Environ,
    id: usize,
    nargs: usize,
    rhs_s_value: &Value,
    rhs_s_name: &str,
) -> Vec<Value> {
    let names = env.closure_args(id, nargs);
    let bits = env.closure_arg_bits(id, nargs);
    names
        .iter()
        .zip(bits.iter())
        .map(|(n, b)| {
            if *n == rhs_s_name {
                rhs_s_value.clone()
            } else {
                Value::from_u64(0, *b)
            }
        })
        .collect()
}

fn empty_span() -> pest::Span<'static> {
    pest::Span::new("", 0, 0).unwrap()
}
