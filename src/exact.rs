use std::collections::hash_map::Entry;
use std::collections::BTreeMap;
use std::time::Instant;

pub mod closure;
mod grammar;
mod relevance;
mod spec;
mod util;

use num_bigint::BigUint;
use num_traits::One;
use rustc_hash::FxHashMap;
use sygus_parser::ast::SyGuSFile;

use crate::{
    debg, info,
    enumerate::{
        expr::OwnedExpr,
        grammar::{build_owned_application, for_each_candidate_tuple, for_each_size_split, MultiConfig, TemplateExpr},
        value::Value,
    },
    parse::{self, deffun, SynthProblem},
};

pub enum NullarySpec {
    Exact(Value),
    BitConstraints {
        bits: usize,
        known_bits: BTreeMap<usize, bool>,
        /// Boolean / BV constraints over the synth function, compiled with
        /// [`OwnedExpr::from_term`] (same path as PBE / ref-impl) and checked via
        /// [`OwnedExpr::eval`]. A constraint holds when evaluation yields zero
        /// (see boolean encoding in `enumerate/expr.rs` `from_term`).
        structural: Vec<OwnedExpr>,
    },
}

/// Evaluate a define-fun, transparently appending closure-arg values when the
/// define-fun's body references closure synth-funs.
///
/// `closure = None` is the direct-mode fast path: a problem with no closure
/// synth-funs at all (every LTL/Reg/FO benchmark) — we bypass the
/// `closure_args` metadata lookup entirely so the hot loop is identical to a
/// direct `eval_defined` call. `closure = Some((name, value))` binds the named
/// closure synth-fun to `value`; any other closure synth-funs the body
/// references fall back to zero (mirroring the original `closure_arg_values`
/// policy).
#[inline]
pub fn eval_defined_with_closure(
    fid: usize,
    nargs: usize,
    args: &[Value],
    closure: Option<(&str, &Value)>,
) -> Result<Value, ()> {
    let Some((closure_name, closure_value)) = closure else {
        return deffun::ENV.eval_defined(fid, nargs, args).map_err(|_| ());
    };
    let names = deffun::ENV.closure_args(fid, nargs);
    if names.is_empty() {
        return deffun::ENV.eval_defined(fid, nargs, args).map_err(|_| ());
    }
    let bits = deffun::ENV.closure_arg_bits(fid, nargs);
    let mut full = Vec::with_capacity(args.len() + names.len());
    full.extend_from_slice(args);
    for (name, b) in names.iter().zip(bits.iter()) {
        if *name == closure_name {
            full.push(closure_value.clone());
        } else {
            full.push(Value::from_u64(0, *b));
        }
    }
    deffun::ENV.eval_defined(fid, nargs, &full).map_err(|_| ())
}

impl NullarySpec {
    pub fn from_file(
        file: &SyGuSFile,
        problem: &SynthProblem<'static>,
    ) -> parse::Result<Option<Self>> {
        if !problem.args.is_empty() {
            return Ok(None);
        }
        if let Some(value) = spec::parse_target_define_fun(file, problem.name)? {
            return Ok(Some(Self::Exact(value)));
        }
        if let Some((known_bits, structural)) =
            spec::parse_bit_constraints(file, problem.name, problem.bits)?
        {
            return Ok(Some(Self::BitConstraints {
                bits: problem.bits,
                known_bits,
                structural,
            }));
        }
        Ok(None)
    }

    fn matches(&self, value: &Value) -> bool {
        match self {
            Self::Exact(expected) => value == expected,
            Self::BitConstraints {
                bits,
                known_bits,
                structural,
            } => {
                if value.bits() != *bits {
                    return false;
                }
                if !known_bits
                    .iter()
                    .all(|(bit, expected)| value.bit(*bit) == *expected)
                {
                    return false;
                }
                structural.iter().all(|expr| {
                    expr.eval(std::slice::from_ref(value))
                        .map(|v| v.as_bool().holds())
                        .unwrap_or(false)
                })
            }
        }
    }
}

impl NullarySpec {
    /// Search the problem grammar for a term matching this spec. Builds the
    /// `ExactGrammar` from `problem`, then drives the multi-NT search loop.
    ///
    /// `fixpoint` selects the evaluation mode:
    /// - `None` — direct mode. Each candidate's value is the bottom-up
    ///   composition of its children's values via `eval_defined`, and
    ///   `spec.matches` is applied directly to that value.
    /// - `Some(closure_name)` — fixpoint mode. The candidate is treated as the
    ///   body of a recursive synth-fun named `closure_name`; sub-NT candidates
    ///   are deduped by their evaluation at closure = 0 (single-sample
    ///   fingerprint), and at the start NT each candidate is materialized,
    ///   iterated to its LFP via Kleene, and only then checked against
    ///   `spec.matches`.
    pub fn search(
        &self,
        problem: &SynthProblem<'static>,
        min: bool,
        fixpoint: Option<&str>,
    ) -> parse::Result<OwnedExpr> {
        let cfg_start = Instant::now();
        let multi = MultiConfig::from_problem(problem)?;
        debg!(
            "exact-nullary multi-config built in {:?}",
            cfg_start.elapsed()
        );
        let grammar_start = Instant::now();
        let grammar = ExactGrammar::from_config(&multi);
        debg!(
            "exact-nullary grammar built in {:?}",
            grammar_start.elapsed()
        );
        search_nullary_multi_nt(&grammar, self, min, fixpoint)
    }
}

pub type NodeId = usize;

pub struct Node {
    pub nt_idx: usize,
    pub rule_idx: usize,
    pub children: Vec<NodeId>,
}

#[derive(Clone)]
pub struct ExactGrammar<'a> {
    pub nts: Vec<(&'a str, Vec<ExactRule>)>,
    pub start: usize,
}

#[derive(Clone)]
pub enum ExactRule {
    Alias(usize),
    Leaf(OwnedExpr),
    Unary {
        fid: usize,
        child_nt: usize,
    },
    Binary {
        fid: usize,
        lhs_nt: usize,
        rhs_nt: usize,
    },
    Nary {
        fid: usize,
        child_nts: Vec<usize>,
    },
    GenericTemplate {
        template: TemplateExpr,
        child_nts: Vec<usize>,
        base_size: usize,
    },
}

#[derive(Default)]
pub struct ExactEvalCache {
    pub leaves: FxHashMap<OwnedExpr, Option<Value>>,
}

impl TemplateExpr {
    /// Evaluate a `TemplateExpr` rule from the exact-search grammar at
    /// concrete argument values. Caches the leaf evaluations because the
    /// same constant leaf appears across many template instantiations.
    pub fn evaluate(
        &self,
        args: &[Value],
        cache: &mut ExactEvalCache,
    ) -> Result<Value, ()> {
        match self {
            TemplateExpr::Slot(i) => Ok(args[*i].clone()),
            TemplateExpr::Leaf(expr) => cache
                .leaves
                .entry(expr.clone())
                .or_insert_with(|| expr.eval(&[]).ok())
                .clone()
                .ok_or(()),
            TemplateExpr::App(id, parts) => {
                let values = parts
                    .iter()
                    .map(|part| part.evaluate(args, cache))
                    .collect::<Result<Vec<_>, _>>()?;
                let const_args = values.into_iter().map(OwnedExpr::Const).collect::<Vec<_>>();
                build_owned_application(id, &const_args)
                    .ok()
                    .and_then(|expr| expr.eval(&[]).ok())
                    .ok_or(())
            }
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct ProjectionKey(Vec<u64>);

enum SeenMode {
    Exact(Vec<FxHashMap<Value, usize>>),
    Projected {
        relevant_bits: Vec<Vec<usize>>,
        maps: Vec<FxHashMap<ProjectionKey, usize>>,
    },
}

#[derive(Clone)]
struct Candidate {
    node: NodeId,
    value: Value,
}

fn search_nullary_multi_nt(
    grammar: &ExactGrammar<'static>,
    spec: &NullarySpec,
    min: bool,
    fixpoint: Option<&str>,
) -> parse::Result<OwnedExpr> {
    // In fixpoint mode every sub-NT eval binds the closure synth-fun to
    // `closure_zero` (all bits cleared). Two sub-terms that produce the same
    // value at this single sample are taken to be equivalent for dedup
    // purposes — a probabilistic fingerprint that catches most equivalences
    // without the O(N²) cost of pairwise SMT equivalence checks. At the start
    // NT we ignore the fingerprint and compute the actual LFP via Kleene.
    let closure_zero: Option<Value> = match (fixpoint, spec) {
        (Some(_), NullarySpec::BitConstraints { bits, .. }) => Some(Value::from_u64(0, *bits)),
        _ => None,
    };
    let closure_binding: Option<(&str, &Value)> = match (fixpoint, &closure_zero) {
        (Some(name), Some(v)) => Some((name, v)),
        _ => None,
    };
    let relevance_disabled = !min;
    let mut eager_relevant_bits = None;
    if relevance_disabled {
        debg!("exact-nullary relevance skipped (--min=false)");
    } else {
        let relevance_start = Instant::now();
        eager_relevant_bits = relevance::compute_relevant_bits_for_spec(grammar, spec);
        debg!(
            "exact-nullary relevance computed in {:?}",
            relevance_start.elapsed()
        );
        if let Some(bits) = &eager_relevant_bits {
            grammar.log_relevance_summary(bits);
        }
    }
    let mut leaf_rules = 0usize;
    let mut alias_rules = 0usize;
    let mut unary_rules = 0usize;
    let mut binary_rules = 0usize;
    let mut nary_rules = 0usize;
    let mut generic_rules = 0usize;
    for (_, rules) in &grammar.nts {
        for rule in rules {
            match rule {
                ExactRule::Alias(_) => alias_rules += 1,
                ExactRule::Leaf(_) => leaf_rules += 1,
                ExactRule::Unary { .. } => unary_rules += 1,
                ExactRule::Binary { .. } => binary_rules += 1,
                ExactRule::Nary { .. } => nary_rules += 1,
                ExactRule::GenericTemplate { .. } => generic_rules += 1,
            }
        }
    }
    debg!(
        "exact-nullary grammar nts={} leaf={} alias={} unary={} binary={} nary={} generic={}",
        grammar.nts.len(),
        leaf_rules,
        alias_rules,
        unary_rules,
        binary_rules,
        nary_rules,
        generic_rules
    );
    let nt_count = grammar.nts.len();
    let mut by_size = vec![vec![Vec::<Candidate>::new()]; nt_count];
    let mut seen = if !relevance_disabled {
        if let Some(relevant_bits) = eager_relevant_bits {
            SeenMode::Projected {
                relevant_bits,
                maps: (0..nt_count)
                    .map(|_| FxHashMap::<ProjectionKey, usize>::default())
                    .collect(),
            }
        } else {
            SeenMode::Exact(vec![FxHashMap::<Value, usize>::default(); nt_count])
        }
    } else {
        SeenMode::Exact(vec![FxHashMap::<Value, usize>::default(); nt_count])
    };
    let mut nodes = Vec::<Node>::new();
    let mut eval_cache = ExactEvalCache::default();

    for size in 1.. {
        let mut eval_attempted = 0usize;
        let mut eval_failed = 0usize;
        for buckets in &mut by_size {
            buckets.push(Vec::new());
        }

        for (nt_idx, (_, rules)) in grammar.nts.iter().enumerate() {
            for (rule_idx, rule) in rules.iter().enumerate() {
                match rule {
                    ExactRule::Alias(_) => {}
                    ExactRule::Leaf(expr) => {
                        if size != 1 {
                            continue;
                        }
                        // In fixpoint mode, a leaf may either (a) be a Var(0)
                        // reference to the closure synth-fun, which the parser
                        // emits because we wrapped the operator's synth-fun
                        // with the closure as its single arg, or (b) be a
                        // 0-arg constructor define-fun whose body extracts
                        // from the closure via the closure-args metadata.
                        // Both need the closure value bound. `eval_with_closure`
                        // handles both: it substitutes `closure_zero` for
                        // Var(0) and appends closure-arg values at each
                        // define-fun call.
                        let leaf_value = match closure_binding {
                            None => expr.eval(&[]).ok(),
                            Some((name, value)) => expr
                                .eval_with_closure(&deffun::ENV, value, name)
                                .ok(),
                        };
                        if let Some(value) = eval_cache
                            .leaves
                            .entry(expr.clone())
                            .or_insert(leaf_value)
                            .clone()
                        {
                            if let Some(found) = insert_multi_nt_candidate(
                                nt_idx,
                                value,
                                size,
                                &grammar,
                                spec,
                                &mut seen,
                                &mut by_size,
                                &mut nodes,
                                fixpoint,
                                || Node {
                                    nt_idx,
                                    rule_idx,
                                    children: Vec::new(),
                                },
                            ) {
                                return Ok(found);
                            }
                        }
                    }
                    ExactRule::Unary { fid, child_nt } => {
                        if size < 2 {
                            continue;
                        }
                        let child_size = size - 1;
                        if by_size[*child_nt].get(child_size).is_none_or(Vec::is_empty) {
                            continue;
                        }
                        let children = by_size[*child_nt]
                            .get(child_size)
                            .map(Vec::as_slice)
                            .unwrap_or(&[][..])
                            .to_vec();
                        for child in &children {
                            eval_attempted += 1;
                            let value = eval_defined_with_closure(
                                *fid,
                                1,
                                std::slice::from_ref(&child.value),
                                closure_binding,
                            );
                            let Ok(value) = value else {
                                eval_failed += 1;
                                continue;
                            };
                            if let Some(found) = insert_multi_nt_candidate(
                                nt_idx,
                                value,
                                size,
                                &grammar,
                                spec,
                                &mut seen,
                                &mut by_size,
                                &mut nodes,
                                fixpoint,
                                || Node {
                                    nt_idx,
                                    rule_idx,
                                    children: vec![child.node],
                                },
                            ) {
                                return Ok(found);
                            }
                        }
                    }
                    ExactRule::Binary {
                        fid,
                        lhs_nt,
                        rhs_nt,
                    } => {
                        if size < 3 {
                            continue;
                        }
                        for lhs_size in 1..(size - 1) {
                            let rhs_size = size - 1 - lhs_size;
                            if by_size[*lhs_nt].get(lhs_size).is_none_or(Vec::is_empty)
                                || by_size[*rhs_nt].get(rhs_size).is_none_or(Vec::is_empty)
                            {
                                continue;
                            }
                            let lhs_pool = by_size[*lhs_nt]
                                .get(lhs_size)
                                .map(Vec::as_slice)
                                .unwrap_or(&[][..])
                                .to_vec();
                            let rhs_pool = by_size[*rhs_nt]
                                .get(rhs_size)
                                .map(Vec::as_slice)
                                .unwrap_or(&[][..])
                                .to_vec();
                            if lhs_pool.is_empty() || rhs_pool.is_empty() {
                                continue;
                            }
                            for lhs in &lhs_pool {
                                for rhs in &rhs_pool {
                                    eval_attempted += 1;
                                    let value = eval_defined_with_closure(
                                        *fid,
                                        2,
                                        &[lhs.value.clone(), rhs.value.clone()],
                                        closure_binding,
                                    );
                                    let Ok(value) = value else {
                                        eval_failed += 1;
                                        continue;
                                    };
                                    if let Some(found) = insert_multi_nt_candidate(
                                        nt_idx,
                                        value,
                                        size,
                                        &grammar,
                                        spec,
                                        &mut seen,
                                        &mut by_size,
                                        &mut nodes,
                                                fixpoint,
                                        || Node {
                                            nt_idx,
                                            rule_idx,
                                            children: vec![lhs.node, rhs.node],
                                        },
                                        ) {
                                            return Ok(found);
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
                        let mut staged = Vec::new();
                        let mut splits = Vec::with_capacity(child_nts.len());
                        for_each_size_split(
                            child_total,
                            child_nts.len(),
                            &mut splits,
                            &mut |sizes| {
                                let pools = child_nts
                                    .iter()
                                    .zip(sizes.iter())
                                    .map(|(child_nt, child_size)| {
                                        by_size[*child_nt]
                                            .get(*child_size)
                                            .map(Vec::as_slice)
                                            .unwrap_or(&[][..])
                                    })
                                    .collect::<Vec<_>>();
                                if pools.iter().any(|pool| pool.is_empty()) {
                                    return;
                                }
                                let mut tuple = Vec::with_capacity(child_nts.len());
                                for_each_candidate_tuple(&pools, &mut tuple, &mut |tuple| {
                                    let child_values = tuple
                                        .iter()
                                        .map(|cand| cand.value.clone())
                                        .collect::<Vec<_>>();
                                    eval_attempted += 1;
                                    let Ok(value) = eval_defined_with_closure(
                                        *fid,
                                        child_values.len(),
                                        &child_values,
                                        closure_binding,
                                    ) else {
                                        eval_failed += 1;
                                        return;
                                    };
                                    let children =
                                        tuple.iter().map(|cand| cand.node).collect::<Vec<_>>();
                                    staged.push((value, children));
                                });
                            },
                        );
                        for (value, children) in staged {
                            if let Some(found) = insert_multi_nt_candidate(
                                nt_idx,
                                value,
                                size,
                                &grammar,
                                spec,
                                &mut seen,
                                &mut by_size,
                                &mut nodes,
                                fixpoint,
                                || Node {
                                    nt_idx,
                                    rule_idx,
                                    children,
                                },
                            ) {
                                return Ok(found);
                            }
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
                            if child_total == 0 {
                                if let Ok(value) =
                                    template.evaluate(&[], &mut eval_cache)
                                {
                                    eval_attempted += 1;
                                    if let Some(found) = insert_multi_nt_candidate(
                                        nt_idx,
                                        value,
                                        size,
                                        &grammar,
                                        spec,
                                        &mut seen,
                                        &mut by_size,
                                        &mut nodes,
                                                fixpoint,
                                        || Node {
                                            nt_idx,
                                            rule_idx,
                                            children: Vec::new(),
                                        },
                                    ) {
                                        return Ok(found);
                                    }
                                } else {
                                    eval_attempted += 1;
                                    eval_failed += 1;
                                }
                            }
                            continue;
                        }
                        if child_total < child_nts.len() {
                            continue;
                        }
                        let mut staged = Vec::new();
                        let mut splits = Vec::with_capacity(child_nts.len());
                        for_each_size_split(
                            child_total,
                            child_nts.len(),
                            &mut splits,
                            &mut |sizes| {
                                let pools = child_nts
                                    .iter()
                                    .zip(sizes.iter())
                                    .map(|(child_nt, child_size)| {
                                        by_size[*child_nt]
                                            .get(*child_size)
                                            .map(Vec::as_slice)
                                            .unwrap_or(&[][..])
                                    })
                                    .collect::<Vec<_>>();
                                if pools.iter().any(|pool| pool.is_empty()) {
                                    return;
                                }
                                let mut tuple = Vec::with_capacity(child_nts.len());
                                for_each_candidate_tuple(&pools, &mut tuple, &mut |tuple| {
                                    let child_values = tuple
                                        .iter()
                                        .map(|cand| cand.value.clone())
                                        .collect::<Vec<_>>();
                                    eval_attempted += 1;
                                    let Ok(value) = template.evaluate(&child_values, &mut eval_cache) else {
                                        eval_failed += 1;
                                        return;
                                    };
                                    let children =
                                        tuple.iter().map(|cand| cand.node).collect::<Vec<_>>();
                                    staged.push((value, children));
                                });
                            },
                        );
                        for (value, children) in staged {
                            if let Some(found) = insert_multi_nt_candidate(
                                nt_idx,
                                value,
                                size,
                                &grammar,
                                spec,
                                &mut seen,
                                &mut by_size,
                                &mut nodes,
                                fixpoint,
                                || Node {
                                    nt_idx,
                                    rule_idx,
                                    children,
                                },
                            ) {
                                return Ok(found);
                            }
                        }
                    }
                }
            }
        }

        loop {
            let mut changed = false;
            for (nt_idx, (_, rules)) in grammar.nts.iter().enumerate() {
                for rule in rules {
                    let ExactRule::Alias(child_nt) = rule else {
                        continue;
                    };
                    let before = by_size[nt_idx][size].len();
                    let staged = by_size[*child_nt][size].clone();
                    for candidate in staged {
                        if let Some(found) = insert_existing_candidate(
                            nt_idx,
                            candidate,
                            size,
                            &grammar,
                            spec,
                            &mut seen,
                            &mut by_size,
                            &nodes,
                            fixpoint,
                        ) {
                            return Ok(found);
                        }
                    }
                    changed |= by_size[nt_idx][size].len() > before;
                }
            }
            if !changed {
                break;
            }
        }
    }

    unreachable!("nullary enumeration should either find a solution or diverge");
}

impl<'a> ExactGrammar<'a> {
    pub fn log_relevance_summary(&self, relevant_bits: &[Vec<usize>]) {
        let total_kept: usize = relevant_bits.iter().map(Vec::len).sum();
        let total_full: usize = self
            .nts
            .iter()
            .map(|(_, rules)| relevance::nt_output_bits(rules))
            .sum();
        info!(
            "exact-nullary relevance: {}/{} bits relevant ({:.1}%)",
            total_kept,
            total_full,
            total_kept as f64 / total_full as f64 * 100.0
        );
        for (i, (bits, (_, rules))) in relevant_bits.iter().zip(self.nts.iter()).enumerate() {
            let nt_total = relevance::nt_output_bits(rules);
            debg!("  nt[{}]: {}/{} bits relevant", i, bits.len(), nt_total);
        }
    }
}

/// Split label bit-indices into the "must be 1" and "must be 0" sets. Used
/// for allocation-free bitwise checks on Kleene iterates — at the typical
/// label counts (single digits per CEGIS round) iterating these slices and
/// calling `Value::bit(i)` is much cheaper than building masks as `Value`s
/// and doing BigUint AND/OR per check.
fn label_indices(spec: &NullarySpec) -> Option<(Vec<usize>, Vec<usize>)> {
    let known_bits = match spec {
        NullarySpec::BitConstraints { known_bits, .. } => known_bits,
        NullarySpec::Exact(_) => return None,
    };
    let mut pos = Vec::new();
    let mut neg = Vec::new();
    for (idx, expected) in known_bits {
        if *expected {
            pos.push(*idx);
        } else {
            neg.push(*idx);
        }
    }
    Some((pos, neg))
}

/// Compute the candidate's LFP via Kleene from `aux = 0`, with two sound
/// early-rejection checks driven by the label masks. Returns
/// `Some((expr, lfp))` if the candidate survives to convergence; `None` if
/// it's rejected before then.
///
/// Both checks are sound by monotonicity of `F`:
///   * **F(top) upper bound.** LFP ≤ GFP ≤ F(top). If F(top) doesn't include
///     a positive-label bit, neither does LFP — reject after one extra eval,
///     before iterating Kleene at all.
///   * **Per-iteration negative-label check.** Every Kleene iterate
///     `aux_n ≤ LFP`. If `aux_n` triggers a negative-label bit, LFP does too
///     — reject without finishing convergence. The first iter rejects the
///     bulk of "trivially-wrong" candidates that flip a forbidden bit
///     immediately, collapsing Kleene from N iters down to 1 for failures.
///
/// Together these turn label-checking from a *post-convergence* test into a
/// *during-search* prune — analogous in spirit to the existing
/// backward-relevance optimization which uses the same labels to shrink the
/// dedup keyspace.
/// Compute the candidate's LFP via Kleene from `aux = 0`, with a sound
/// per-iteration negative-label check. By monotonicity every Kleene iterate
/// `aux_n ≤ LFP`, so if `aux_n` triggers any negative-label bit the LFP
/// triggers it too — reject without running Kleene to convergence. The first
/// iter catches the bulk of "trivially-wrong" candidates that flip a
/// forbidden bit immediately.
///
/// Note: an F(top) upper-bound check for positive labels is also sound
/// (LFP ≤ GFP ≤ F(top)), but in practice adds one extra eval per candidate
/// that outweighs the savings when Kleene already converges in 1-5 iters.
/// We rely on the post-convergence label match instead.
fn materialize_and_kleene(
    node: NodeId,
    grammar: &ExactGrammar<'_>,
    nodes: &[Node],
    spec: &NullarySpec,
    closure_name: &str,
) -> Option<(OwnedExpr, Value)> {
    let expr = materialize_node(node, grammar, nodes)?;
    let bits = match spec {
        NullarySpec::BitConstraints { bits, .. } => *bits,
        NullarySpec::Exact(v) => v.bits(),
    };
    let (_pos_indices, neg_indices) = label_indices(spec)?;
    let env = &deffun::ENV;

    let mut aux = Value::zero(bits);
    for _ in 0..=bits {
        let next = expr.eval_with_closure(env, &aux, closure_name).ok()?;
        if neg_indices.iter().any(|&i| next.bit(i)) {
            return None;
        }
        if next == aux {
            return Some((expr, next));
        }
        aux = next;
    }
    None
}

fn insert_existing_candidate(
    nt_idx: usize,
    candidate: Candidate,
    size: usize,
    grammar: &ExactGrammar<'_>,
    spec: &NullarySpec,
    seen: &mut SeenMode,
    by_size: &mut [Vec<Vec<Candidate>>],
    nodes: &[Node],
    fixpoint: Option<&str>,
) -> Option<OwnedExpr> {
    if nt_idx == grammar.start {
        if let Some(closure_name) = fixpoint {
            let (expr, lfp) =
                materialize_and_kleene(candidate.node, grammar, nodes, spec, closure_name)?;
            if spec.matches(&lfp) {
                return Some(expr);
            }
            if seen_contains_or_insert(seen, nt_idx, &lfp, size) {
                return None;
            }
            by_size[nt_idx][size].push(Candidate { node: candidate.node, value: lfp });
            return None;
        }
        if spec.matches(&candidate.value) {
            return materialize_node(candidate.node, grammar, nodes);
        }
    }
    // In fixpoint mode the sub-NT `value` is a single-sample fingerprint
    // (eval at closure=0). It collapses recursive sub-terms (whose recursion
    // hasn't fired at closure=0) into non-recursive ones — using it as a
    // dedup key drops valid composites and the synthesizer can never
    // assemble recursive answers. Skip the dedup step; pay enumeration cost.
    // This matches the pre-refactor top_down search, which only deduped at
    // the start NT.
    if fixpoint.is_none() && seen_contains_or_insert(seen, nt_idx, &candidate.value, size) {
        return None;
    }
    by_size[nt_idx][size].push(candidate);
    None
}

fn insert_multi_nt_candidate(
    nt_idx: usize,
    value: Value,
    size: usize,
    grammar: &ExactGrammar<'_>,
    spec: &NullarySpec,
    seen: &mut SeenMode,
    by_size: &mut [Vec<Vec<Candidate>>],
    nodes: &mut Vec<Node>,
    fixpoint: Option<&str>,
    build_node: impl FnOnce() -> Node,
) -> Option<OwnedExpr> {
    if nt_idx == grammar.start {
        if let Some(closure_name) = fixpoint {
            // Fixpoint mode at start NT: intern first (Kleene needs the
            // OwnedExpr), then run Kleene to get the actual LFP, then check
            // labels against the LFP. Dedup by LFP — sound, since equivalent
            // LFPs mean semantically equivalent operators.
            let node = intern_node(nodes, build_node());
            let Some((expr, lfp)) =
                materialize_and_kleene(node, grammar, nodes, spec, closure_name)
            else {
                return None;
            };
            if spec.matches(&lfp) {
                return Some(expr);
            }
            if !seen_contains_or_insert(seen, nt_idx, &lfp, size) {
                by_size[nt_idx][size].push(Candidate { node, value: lfp });
            }
            return None;
        }
        if spec.matches(&value) {
            let node = intern_node(nodes, build_node());
            return materialize_node(node, grammar, nodes);
        }
    }
    // See the comment in `insert_existing_candidate` — sub-NT dedup is
    // intentionally skipped in fixpoint mode because the fingerprint is
    // unsound for dedup.
    if fixpoint.is_none() && seen_contains_or_insert(seen, nt_idx, &value, size) {
        return None;
    }
    let node = intern_node(nodes, build_node());
    by_size[nt_idx][size].push(Candidate { node, value });
    None
}

fn seen_contains_or_insert(
    seen: &mut SeenMode,
    nt_idx: usize,
    value: &Value,
    size: usize,
) -> bool {
    match seen {
        SeenMode::Exact(maps) => match maps[nt_idx].entry(value.clone()) {
            Entry::Occupied(_) => true,
            Entry::Vacant(entry) => {
                entry.insert(size);
                false
            }
        },
        SeenMode::Projected {
            relevant_bits,
            maps,
        } => {
            let key = value.project(&relevant_bits[nt_idx]);
            match maps[nt_idx].entry(key) {
                Entry::Occupied(_) => true,
                Entry::Vacant(entry) => {
                    entry.insert(size);
                    false
                }
            }
        }
    }
}

impl Value {
    fn project(&self, bits: &[usize]) -> ProjectionKey {
    ProjectionKey(self.project_bits(bits))
    }
}


pub fn intern_node(nodes: &mut Vec<Node>, node: Node) -> NodeId {
    let id = nodes.len();
    nodes.push(node);
    id
}

pub fn materialize_node(
    id: NodeId,
    grammar: &ExactGrammar<'_>,
    nodes: &[Node],
) -> Option<OwnedExpr> {
    let node = &nodes[id];
    match &grammar.nts[node.nt_idx].1[node.rule_idx] {
        ExactRule::Alias(_) => materialize_node(node.children[0], grammar, nodes),
        ExactRule::Leaf(expr) => Some(expr.clone()),
        ExactRule::Unary { fid, .. } => Some(OwnedExpr::Fop1Dyn(
            *fid,
            Box::new(materialize_node(node.children[0], grammar, nodes)?),
        )),
        ExactRule::Binary { fid, .. } => Some(OwnedExpr::Fop2Dyn(
            *fid,
            Box::new(materialize_node(node.children[0], grammar, nodes)?),
            Box::new(materialize_node(node.children[1], grammar, nodes)?),
        )),
        ExactRule::Nary { fid, .. } => Some(OwnedExpr::FopDyn(
            *fid,
            node.children
                .iter()
                .map(|child| materialize_node(*child, grammar, nodes))
                .collect::<Option<Vec<_>>>()?,
        )),
        ExactRule::GenericTemplate { template, .. } => {
            let child_exprs = node
                .children
                .iter()
                .map(|child| materialize_node(*child, grammar, nodes))
                .collect::<Option<Vec<_>>>()?;
            template.instantiate(&child_exprs).ok()
        }
    }
}
