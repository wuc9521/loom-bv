//! Bottom-up enumeration over the compiled `ExactGrammar`, with value-based
//! dedup. Two modes (selected by `Searcher::closure`):
//!
//! - **Direct** (`closure = None`): each candidate's value is composed from
//!   its children's values via `eval_defined`, deduped on that single
//!   value, and checked against the spec immediately on reaching the
//!   start NT.
//!
//! - **Fixpoint** (`closure = Some(_)`): each sub-NT candidate carries two
//!   evaluations — at `aux=0` and at `aux=top` — and dedups on the pair.
//!   Start-NT candidates run a Kleene LFP iteration via
//!   `Searcher::kleene_lfp`, with the converged value used for both the
//!   spec match and dedup. The Kleene loop also performs a per-iter
//!   negative-label early reject (sound by monotonicity).
//!
//! All fixpoint-vs-direct branching is confined to `Searcher::eval_*`
//! (which return `(value, value_top: Option<Value>)`) and `Searcher::try_push`
//! (which dispatches on `self.closure.is_some()` and `nt_idx == start`).
//! Each rule arm in `Searcher::run` reduces to "build children-eval +
//! call try_push".

use std::time::Instant;

use crate::debg;
use crate::enumerate::{
    expr::OwnedExpr,
    grammar::{for_each_candidate_tuple, for_each_size_split, MultiConfig},
    value::Value,
};
use crate::exact::closure::Closure;
use crate::exact::dedup::SeenMode;
use crate::exact::eval::eval_defined_with_closure;
use crate::exact::stats::DedupStats;
use crate::exact::types::{Candidate, ExactEvalCache, ExactGrammar, ExactRule, Node, NodeId};
use crate::exact::{relevance, NullarySpec};
use crate::parse::{self, deffun, SynthProblem};

pub fn run_search<'a>(
    grammar: ExactGrammar<'a>,
    spec: &NullarySpec,
    min: bool,
    fixpoint: Option<&str>,
) -> parse::Result<OwnedExpr> {
    Searcher::new(grammar, spec, min, fixpoint).run()
}

struct Searcher<'a, 'g> {
    grammar: ExactGrammar<'a>,
    spec: &'g NullarySpec,
    closure: Option<Closure>,
    nodes: Vec<Node>,
    by_size: Vec<Vec<Vec<Candidate>>>,
    seen: SeenMode,
    leaf_cache: ExactEvalCache,
}

impl<'a, 'g> Searcher<'a, 'g> {
    fn new(
        grammar: ExactGrammar<'a>,
        spec: &'g NullarySpec,
        min: bool,
        fixpoint: Option<&str>,
    ) -> Self {
        let closure = match (fixpoint, spec) {
            (Some(name), NullarySpec::BitConstraints { bits, .. }) => {
                Some(Closure::new(name, *bits))
            }
            _ => None,
        };
        let relevance_disabled = !min;
        let eager_relevant_bits = if relevance_disabled {
            debg!("exact-nullary relevance skipped (--min=false)");
            None
        } else {
            let relevance_start = Instant::now();
            let bits = relevance::compute_relevant_bits_for_spec(&grammar, spec);
            debg!(
                "exact-nullary relevance computed in {:?}",
                relevance_start.elapsed()
            );
            if let Some(b) = &bits {
                grammar.log_relevance_summary(b);
            }
            bits
        };
        let nt_count = grammar.nts.len();
        let seen = if closure.is_some() {
            SeenMode::pair(nt_count, grammar.start)
        } else if let Some(relevant_bits) = eager_relevant_bits {
            SeenMode::projected(relevant_bits)
        } else {
            SeenMode::exact(nt_count)
        };
        Self {
            grammar,
            spec,
            closure,
            nodes: Vec::new(),
            by_size: vec![vec![Vec::<Candidate>::new()]; nt_count],
            seen,
            leaf_cache: ExactEvalCache::default(),
        }
    }

    fn run(&mut self) -> parse::Result<OwnedExpr> {
        log_grammar_summary(&self.grammar);
        for size in 1.. {
            for buckets in &mut self.by_size {
                buckets.push(Vec::new());
            }
            for nt_idx in 0..self.grammar.nts.len() {
                for rule_idx in 0..self.grammar.nts[nt_idx].1.len() {
                    if let Some(found) = self.expand_rule(nt_idx, rule_idx, size)? {
                        return Ok(found);
                    }
                }
            }
            // Alias rules form a fixed point at this size: keep promoting
            // child-NT candidates into alias-defining NTs until stable.
            loop {
                let mut changed = false;
                for nt_idx in 0..self.grammar.nts.len() {
                    for rule_idx in 0..self.grammar.nts[nt_idx].1.len() {
                        let ExactRule::Alias(child_nt) =
                            &self.grammar.nts[nt_idx].1[rule_idx]
                        else {
                            continue;
                        };
                        let child_nt = *child_nt;
                        let before = self.by_size[nt_idx][size].len();
                        let staged = self.by_size[child_nt][size].clone();
                        for candidate in staged {
                            if let Some(found) = self.try_push_existing(nt_idx, candidate, size) {
                                return Ok(found);
                            }
                        }
                        changed |= self.by_size[nt_idx][size].len() > before;
                    }
                }
                if !changed {
                    break;
                }
            }
        }
        unreachable!("nullary enumeration should either find a solution or diverge");
    }

    fn expand_rule(
        &mut self,
        nt_idx: usize,
        rule_idx: usize,
        size: usize,
    ) -> parse::Result<Option<OwnedExpr>> {
        // Cloning the rule to release the grammar borrow before mutating
        // by_size / seen / nodes.
        let rule = self.grammar.nts[nt_idx].1[rule_idx].clone();
        match rule {
            ExactRule::Alias(_) => Ok(None),
            ExactRule::Leaf(expr) => {
                if size != 1 {
                    return Ok(None);
                }
                let Some((value, value_top)) = self.eval_leaf(&expr) else {
                    return Ok(None);
                };
                Ok(self.try_push_new(
                    nt_idx,
                    size,
                    value,
                    value_top,
                    || Node { nt_idx, rule_idx, children: Vec::new() },
                ))
            }
            ExactRule::Unary { fid, child_nt } => {
                if size < 2 {
                    return Ok(None);
                }
                let child_size = size - 1;
                let children = self.by_size[child_nt].get(child_size).cloned().unwrap_or_default();
                for child in &children {
                    let Some((value, value_top)) = self.eval_unary(fid, child) else { continue; };
                    let child_node = child.node;
                    if let Some(found) = self.try_push_new(
                        nt_idx,
                        size,
                        value,
                        value_top,
                        || Node { nt_idx, rule_idx, children: vec![child_node] },
                    ) {
                        return Ok(Some(found));
                    }
                }
                Ok(None)
            }
            ExactRule::Binary { fid, lhs_nt, rhs_nt } => {
                if size < 3 {
                    return Ok(None);
                }
                for lhs_size in 1..(size - 1) {
                    let rhs_size = size - 1 - lhs_size;
                    let lhs_pool = self.by_size[lhs_nt].get(lhs_size).cloned().unwrap_or_default();
                    let rhs_pool = self.by_size[rhs_nt].get(rhs_size).cloned().unwrap_or_default();
                    if lhs_pool.is_empty() || rhs_pool.is_empty() {
                        continue;
                    }
                    for lhs in &lhs_pool {
                        for rhs in &rhs_pool {
                            let Some((value, value_top)) = self.eval_binary(fid, lhs, rhs) else {
                                continue;
                            };
                            let (lhs_node, rhs_node) = (lhs.node, rhs.node);
                            if let Some(found) = self.try_push_new(
                                nt_idx,
                                size,
                                value,
                                value_top,
                                || Node {
                                    nt_idx,
                                    rule_idx,
                                    children: vec![lhs_node, rhs_node],
                                },
                            ) {
                                return Ok(Some(found));
                            }
                        }
                    }
                }
                Ok(None)
            }
            ExactRule::Nary { fid, child_nts } => {
                if size <= child_nts.len() {
                    return Ok(None);
                }
                let child_total = size - 1;
                let mut staged: Vec<(Value, Option<Value>, Vec<NodeId>)> = Vec::new();
                let by_size = &self.by_size;
                let closure = self.closure.as_ref();
                let mut splits = Vec::with_capacity(child_nts.len());
                for_each_size_split(
                    child_total,
                    child_nts.len(),
                    &mut splits,
                    &mut |sizes| {
                        let pools: Vec<&[Candidate]> = child_nts
                            .iter()
                            .zip(sizes.iter())
                            .map(|(child_nt, child_size)| {
                                by_size[*child_nt]
                                    .get(*child_size)
                                    .map(Vec::as_slice)
                                    .unwrap_or(&[][..])
                            })
                            .collect();
                        if pools.iter().any(|pool| pool.is_empty()) {
                            return;
                        }
                        let mut tuple = Vec::with_capacity(child_nts.len());
                        for_each_candidate_tuple(&pools, &mut tuple, &mut |tuple| {
                            let Some((value, value_top)) =
                                Self::eval_nary_static(fid, tuple, closure)
                            else {
                                return;
                            };
                            let children = tuple.iter().map(|c| c.node).collect();
                            staged.push((value, value_top, children));
                        });
                    },
                );
                for (value, value_top, children) in staged {
                    if let Some(found) = self.try_push_new(
                        nt_idx,
                        size,
                        value,
                        value_top,
                        || Node { nt_idx, rule_idx, children },
                    ) {
                        return Ok(Some(found));
                    }
                }
                Ok(None)
            }
            ExactRule::GenericTemplate { template, child_nts, base_size } => {
                if base_size > size {
                    return Ok(None);
                }
                let child_total = size - base_size;
                if child_nts.is_empty() {
                    if child_total == 0 {
                        if let Ok(value) = template.evaluate(&[], &mut self.leaf_cache) {
                            return Ok(self.try_push_new(
                                nt_idx,
                                size,
                                value,
                                None,
                                || Node { nt_idx, rule_idx, children: Vec::new() },
                            ));
                        }
                    }
                    return Ok(None);
                }
                if child_total < child_nts.len() {
                    return Ok(None);
                }
                let mut staged: Vec<(Value, Vec<NodeId>)> = Vec::new();
                let by_size = &self.by_size;
                let leaf_cache = &mut self.leaf_cache;
                let mut splits = Vec::with_capacity(child_nts.len());
                for_each_size_split(
                    child_total,
                    child_nts.len(),
                    &mut splits,
                    &mut |sizes| {
                        let pools: Vec<&[Candidate]> = child_nts
                            .iter()
                            .zip(sizes.iter())
                            .map(|(child_nt, child_size)| {
                                by_size[*child_nt]
                                    .get(*child_size)
                                    .map(Vec::as_slice)
                                    .unwrap_or(&[][..])
                            })
                            .collect();
                        if pools.iter().any(|pool| pool.is_empty()) {
                            return;
                        }
                        let mut tuple = Vec::with_capacity(child_nts.len());
                        for_each_candidate_tuple(&pools, &mut tuple, &mut |tuple| {
                            let child_values =
                                tuple.iter().map(|c| c.value.clone()).collect::<Vec<_>>();
                            let Ok(value) = template.evaluate(&child_values, leaf_cache) else {
                                return;
                            };
                            let children = tuple.iter().map(|c| c.node).collect();
                            staged.push((value, children));
                        });
                    },
                );
                for (value, children) in staged {
                    if let Some(found) = self.try_push_new(
                        nt_idx,
                        size,
                        value,
                        None,
                        || Node { nt_idx, rule_idx, children },
                    ) {
                        return Ok(Some(found));
                    }
                }
                Ok(None)
            }
        }
    }

    // ----- Per-rule eval helpers: return (value@0, value@top? in fixpoint mode)

    fn eval_leaf(&mut self, expr: &OwnedExpr) -> Option<(Value, Option<Value>)> {
        let zero_binding = self.closure.as_ref().map(|c| c.binding_zero());
        let leaf_value = match zero_binding {
            None => expr.eval(&[]).ok(),
            Some((name, v)) => expr.eval_with_closure(&deffun::ENV, v, name).ok(),
        };
        let value = self
            .leaf_cache
            .leaves
            .entry(expr.clone())
            .or_insert(leaf_value)
            .clone()?;
        let value_top = if let Some(closure) = self.closure.as_ref() {
            expr.eval_with_closure(&deffun::ENV, &closure.top, &closure.name)
                .ok()
        } else {
            None
        };
        if self.closure.is_some() && value_top.is_none() {
            return None;
        }
        Some((value, value_top))
    }

    fn eval_unary(&self, fid: usize, child: &Candidate) -> Option<(Value, Option<Value>)> {
        let zero_binding = self.closure.as_ref().map(|c| c.binding_zero());
        let value = eval_defined_with_closure(
            fid,
            1,
            std::slice::from_ref(&child.value),
            zero_binding,
        )
        .ok()?;
        let value_top = if let Some(closure) = self.closure.as_ref() {
            let child_top = child.value_top.as_ref()?;
            Some(
                eval_defined_with_closure(
                    fid,
                    1,
                    std::slice::from_ref(child_top),
                    Some(closure.binding_top()),
                )
                .ok()?,
            )
        } else {
            None
        };
        Some((value, value_top))
    }

    fn eval_binary(
        &self,
        fid: usize,
        lhs: &Candidate,
        rhs: &Candidate,
    ) -> Option<(Value, Option<Value>)> {
        let zero_binding = self.closure.as_ref().map(|c| c.binding_zero());
        let value = eval_defined_with_closure(
            fid,
            2,
            &[lhs.value.clone(), rhs.value.clone()],
            zero_binding,
        )
        .ok()?;
        let value_top = if let Some(closure) = self.closure.as_ref() {
            let lt = lhs.value_top.as_ref()?;
            let rt = rhs.value_top.as_ref()?;
            Some(
                eval_defined_with_closure(
                    fid,
                    2,
                    &[lt.clone(), rt.clone()],
                    Some(closure.binding_top()),
                )
                .ok()?,
            )
        } else {
            None
        };
        Some((value, value_top))
    }

    /// Static variant used inside the Nary callback so we don't hold a
    /// mutable borrow of `self` while walking the pools.
    fn eval_nary_static(
        fid: usize,
        tuple: &[&Candidate],
        closure: Option<&Closure>,
    ) -> Option<(Value, Option<Value>)> {
        let zero_binding = closure.map(|c| c.binding_zero());
        let values_zero: Vec<Value> = tuple.iter().map(|c| c.value.clone()).collect();
        let value = eval_defined_with_closure(fid, values_zero.len(), &values_zero, zero_binding)
            .ok()?;
        let value_top = if let Some(closure) = closure {
            let values_top: Option<Vec<Value>> =
                tuple.iter().map(|c| c.value_top.clone()).collect();
            let values_top = values_top?;
            Some(
                eval_defined_with_closure(
                    fid,
                    values_top.len(),
                    &values_top,
                    Some(closure.binding_top()),
                )
                .ok()?,
            )
        } else {
            None
        };
        Some((value, value_top))
    }

    // ----- Push helpers (the only place fixpoint/direct branching happens
    //       beyond the eval_* helpers above)

    fn try_push_new(
        &mut self,
        nt_idx: usize,
        size: usize,
        value: Value,
        value_top: Option<Value>,
        build_node: impl FnOnce() -> Node,
    ) -> Option<OwnedExpr> {
        if nt_idx == self.grammar.start {
            if self.closure.is_some() {
                let node = self.intern_node(build_node());
                return self.start_nt_kleene(node, size);
            }
            if self.spec.matches(&value) {
                let node = self.intern_node(build_node());
                return self.grammar.materialize_node(node, &self.nodes);
            }
        }
        // Sub-NT push (or direct-mode start NT non-match).
        if self.closure.is_none() && self.seen.contains_or_insert(nt_idx, &value, size) {
            return None;
        }
        if let Some(value_top_ref) = value_top.as_ref() {
            if self
                .seen
                .contains_or_insert_pair(nt_idx, &value, value_top_ref, size)
            {
                return None;
            }
        }
        let node = self.intern_node(build_node());
        if let Some(closure) = self.closure.as_ref() {
            DedupStats::record_push(
                nt_idx, size, node, &value, &self.grammar, &self.nodes, &closure.name,
            );
        }
        self.by_size[nt_idx][size].push(Candidate { node, value, value_top });
        None
    }

    fn try_push_existing(
        &mut self,
        nt_idx: usize,
        candidate: Candidate,
        size: usize,
    ) -> Option<OwnedExpr> {
        if nt_idx == self.grammar.start {
            if self.closure.is_some() {
                return self.start_nt_kleene(candidate.node, size);
            }
            if self.spec.matches(&candidate.value) {
                return self.grammar.materialize_node(candidate.node, &self.nodes);
            }
        }
        if self.closure.is_none() && self.seen.contains_or_insert(nt_idx, &candidate.value, size) {
            return None;
        }
        if let Some(value_top) = candidate.value_top.as_ref() {
            if self
                .seen
                .contains_or_insert_pair(nt_idx, &candidate.value, value_top, size)
            {
                return None;
            }
        }
        if let Some(closure) = self.closure.as_ref() {
            DedupStats::record_push(
                nt_idx,
                size,
                candidate.node,
                &candidate.value,
                &self.grammar,
                &self.nodes,
                &closure.name,
            );
        }
        self.by_size[nt_idx][size].push(candidate);
        None
    }

    /// Start-NT fixpoint-mode push: run Kleene, check spec, dedup on LFP.
    fn start_nt_kleene(&mut self, node: NodeId, size: usize) -> Option<OwnedExpr> {
        let closure_name = self
            .closure
            .as_ref()
            .expect("start_nt_kleene called outside fixpoint mode")
            .name
            .clone();
        let (expr, lfp) = self.kleene_lfp(node, &closure_name)?;
        if self.spec.matches(&lfp) {
            return Some(expr);
        }
        if !self.seen.contains_or_insert(self.grammar.start, &lfp, size) {
            self.by_size[self.grammar.start][size].push(Candidate {
                node,
                value: lfp,
                value_top: None,
            });
        }
        None
    }

    fn intern_node(&mut self, node: Node) -> NodeId {
        let id = self.nodes.len();
        self.nodes.push(node);
        id
    }

    /// Compute the candidate's LFP via Kleene from `aux = 0`, with a sound
    /// per-iter negative-label early-reject. Returns `Some((materialized_expr,
    /// lfp))` on convergence; `None` if rejected before convergence.
    ///
    /// By monotonicity every Kleene iterate `aux_n ≤ LFP`. If `aux_n`
    /// triggers a negative-label bit, the LFP triggers it too — reject
    /// without running Kleene to convergence. The first iter rejects the
    /// bulk of "trivially-wrong" candidates that flip a forbidden bit
    /// immediately, collapsing Kleene from N iters down to 1 for failures.
    fn kleene_lfp(
        &self,
        node: NodeId,
        closure_name: &str,
    ) -> Option<(OwnedExpr, Value)> {
        let bits = match self.spec {
            NullarySpec::BitConstraints { bits, .. } => *bits,
            NullarySpec::Exact(v) => v.bits(),
        };
        let (_pos, neg_indices) = self.spec.label_indices()?;
        let mut aux = Value::zero(bits);
        for _ in 0..=bits {
            let next = self
                .grammar
                .eval_node_at(node, &self.nodes, &aux, closure_name)?;
            if neg_indices.iter().any(|&i| next.bit(i)) {
                return None;
            }
            if next == aux {
                let expr = self.grammar.materialize_node(node, &self.nodes)?;
                return Some((expr, next));
            }
            aux = next;
        }
        None
    }
}

fn log_grammar_summary(grammar: &ExactGrammar<'_>) {
    let mut leaf = 0usize;
    let mut alias = 0usize;
    let mut unary = 0usize;
    let mut binary = 0usize;
    let mut nary = 0usize;
    let mut generic = 0usize;
    for (_, rules) in &grammar.nts {
        for rule in rules {
            match rule {
                ExactRule::Alias(_) => alias += 1,
                ExactRule::Leaf(_) => leaf += 1,
                ExactRule::Unary { .. } => unary += 1,
                ExactRule::Binary { .. } => binary += 1,
                ExactRule::Nary { .. } => nary += 1,
                ExactRule::GenericTemplate { .. } => generic += 1,
            }
        }
    }
    debg!(
        "exact-nullary grammar nts={} leaf={} alias={} unary={} binary={} nary={} generic={}",
        grammar.nts.len(),
        leaf,
        alias,
        unary,
        binary,
        nary,
        generic
    );
}

/// Build the `ExactGrammar` and dispatch to the `Searcher`. Replaces the
/// old free-function `search_nullary_multi_nt`.
pub fn search_problem<'a>(
    problem: &'a SynthProblem<'static>,
    spec: &NullarySpec,
    min: bool,
    fixpoint: Option<&'a str>,
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
    run_search(grammar, spec, min, fixpoint)
}
