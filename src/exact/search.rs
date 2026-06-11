//! Bottom-up enumeration over the compiled `Grammar`, with value-based
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
//! (which return `(value, value_top: Option<BitVec>)`) and `Searcher::try_push`
//! (which dispatches on `self.closure.is_some()` and `nt_idx == start`).
//! Each rule arm in `Searcher::run` reduces to "build children-eval +
//! call try_push".

use std::time::Instant;

use crate::{debg, info};
use crate::enumerate::{
    expr::OwnedExpr,
    grammar::{for_each_candidate_tuple, for_each_size_split, Config},
    value::BitVec,
};
use crate::exact::bitspec::Constraint;
use crate::exact::closure::Bindings;
use crate::exact::dedup::SeenMode;
use crate::exact::stats::DedupStats;
use crate::exact::types::{Candidate, ExactEvalCache, Grammar, ExactRule, Node, NodeId};
use crate::parse::{self, deffun, SynthProblem};
use crate::parse::deffun::BitCircuitPlan;

pub fn run_search<'a>(
    grammar: Grammar<'a>,
    spec: &Constraint,
    min: bool,
    fixpoint: Option<&str>,
    enable_decomp: bool,
) -> parse::Result<OwnedExpr> {
    Searcher::new(grammar, spec, min, fixpoint, enable_decomp).run()
}

pub fn enumerate_start<'a>(
    grammar: Grammar<'a>,
    spec: &Constraint,
    min: bool,
    max_size: usize,
    mut callback: impl FnMut(&OwnedExpr, &[BitVec]) -> Result<(), ()>,
) -> parse::Result<()> {
    let mut searcher = Searcher::new(grammar, spec, min, None, false);
    searcher.run_with_callback(max_size, &mut callback)
}

struct Searcher<'a, 'g> {
    grammar: Grammar<'a>,
    spec: &'g Constraint,
    num_examples: usize,
    closure: Option<Bindings>,
    nodes: Vec<Node>,
    by_size: Vec<Vec<Vec<Candidate>>>,
    seen: SeenMode,
    leaf_cache: ExactEvalCache,
    pruned_plans: rustc_hash::FxHashMap<(usize, usize), std::rc::Rc<BitCircuitPlan>>,
    value_index: Vec<rustc_hash::FxHashMap<Vec<u64>, Vec<NodeId>>>,
    enable_compose: bool,
}

impl<'a, 'g> Searcher<'a, 'g> {
    fn new(
        grammar: Grammar<'a>,
        spec: &'g Constraint,
        min: bool,
        fixpoint: Option<&str>,
        enable_decomp: bool,
    ) -> Self {
        let num_examples = spec.num_examples();
        let closure = match fixpoint {
            Some(name) => Some(Bindings::single(name, spec.bits)),
            None => None,
        };
        let relevance_disabled = !min;
        let eager_relevant_bits = if relevance_disabled {
            debg!("exact relevance skipped (--min=false)");
            None
        } else {
            let relevance_start = Instant::now();
            let bits = spec.compute_relevant_bits(&grammar);
            debg!(
                "exact relevance computed in {:?}",
                relevance_start.elapsed()
            );
            if let Some(b) = &bits {
                grammar.log_relevance_summary(b, num_examples, spec.bits);
            }
            bits
        };
        let mut pruned_plans: rustc_hash::FxHashMap<(usize, usize), std::rc::Rc<BitCircuitPlan>> =
            rustc_hash::FxHashMap::default();
        if let Some(ref relevant_bits) = eager_relevant_bits {
            for (nt_idx, (_, rules)) in grammar.nts.iter().enumerate() {
                let nt_relevant = &relevant_bits[nt_idx];
                for rule in rules {
                    let fid = match rule {
                        ExactRule::Op { fid, .. } => *fid,
                        _ => continue,
                    };
                    if pruned_plans.contains_key(&(nt_idx, fid)) {
                        continue;
                    }
                    let Some(plan) = deffun::ENV.deffun(fid).bit_circuit_plan() else {
                        continue;
                    };
                    if let Some(pruned) = plan.pruned(nt_relevant) {
                        debg!(
                            "COI: nt[{}] fid={} pruned {}/{} bindings, inputs {}/{}",
                            nt_idx, fid, pruned.bindings.len(), plan.bindings.len(),
                            pruned.input_slots.len(), plan.input_slots.len()
                        );
                        pruned_plans.insert((nt_idx, fid), std::rc::Rc::new(pruned));
                    }
                }
            }
        }
        let nt_count = grammar.nts.len();
        let seen = if closure.is_some() {
            SeenMode::pair(nt_count)
        } else if let Some(relevant_bits) = eager_relevant_bits {
            SeenMode::multi_projected(relevant_bits, num_examples)
        } else {
            SeenMode::multi_exact(nt_count, num_examples)
        };
        let enable_compose = enable_decomp && closure.is_none();
        Self {
            grammar,
            spec,
            num_examples,
            closure,
            nodes: Vec::new(),
            by_size: vec![vec![Vec::<Candidate>::new()]; nt_count],
            seen,
            leaf_cache: ExactEvalCache::default(),
            pruned_plans,
            value_index: vec![rustc_hash::FxHashMap::default(); nt_count],
            enable_compose,
        }
    }

    fn run(&mut self) -> parse::Result<OwnedExpr> {
        log_grammar_summary(&self.grammar);
        let run_start = std::time::Instant::now();
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
            if self.enable_compose {
                if let Some(composed) = self.try_compose() {
                    info!("compose: found at size={}", size);
                    return Ok(composed);
                }
            }
            let per_nt: Vec<usize> = self
                .by_size
                .iter()
                .map(|buckets| buckets.get(size).map(|b| b.len()).unwrap_or(0))
                .collect();
            let total: usize = self
                .by_size
                .iter()
                .map(|buckets| buckets.iter().map(|b| b.len()).sum::<usize>())
                .sum();
            debg!(
                "size={}: per-nt={:?} total={} Δ={:?}",
                size,
                per_nt,
                total,
                run_start.elapsed()
            );
            DedupStats::snapshot_line(&format!("dedup@size={}", size));
        }
        unreachable!("nullary enumeration should either find a solution or diverge");
    }

    fn run_with_callback(
        &mut self,
        max_size: usize,
        callback: &mut impl FnMut(&OwnedExpr, &[BitVec]) -> Result<(), ()>,
    ) -> parse::Result<()> {
        log_grammar_summary(&self.grammar);
        for size in 1..=max_size {
            for buckets in &mut self.by_size {
                buckets.push(Vec::new());
            }
            for nt_idx in 0..self.grammar.nts.len() {
                for rule_idx in 0..self.grammar.nts[nt_idx].1.len() {
                    self.expand_rule(nt_idx, rule_idx, size)?;
                }
            }
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
                            self.try_push_existing(nt_idx, candidate, size);
                        }
                        changed |= self.by_size[nt_idx][size].len() > before;
                    }
                }
                if !changed {
                    break;
                }
            }
            let start_nt = self.grammar.start;
            for cand in &self.by_size[start_nt][size] {
                if let Some(expr) = self.grammar.materialize_node(cand.node, &self.nodes) {
                    if callback(&expr, &cand.values).is_err() {
                        return Ok(());
                    }
                }
            }
        }
        Ok(())
    }

    fn expand_rule(
        &mut self,
        nt_idx: usize,
        rule_idx: usize,
        size: usize,
    ) -> parse::Result<Option<OwnedExpr>> {
        let rule = self.grammar.nts[nt_idx].1[rule_idx].clone();
        match rule {
            ExactRule::Alias(_) => Ok(None),
            ExactRule::Leaf(expr) => {
                if size != 1 {
                    return Ok(None);
                }
                let Some((values, values_top)) = self.eval_leaf(&expr) else {
                    return Ok(None);
                };
                Ok(self.try_push_new(
                    nt_idx,
                    size,
                    values,
                    values_top,
                    || Node { nt_idx, rule_idx, children: Vec::new() },
                ))
            }
            ExactRule::Op { fid, child_nts, class } => {
                if size <= child_nts.len() {
                    return Ok(None);
                }
                let child_total = size - 1;
                let mut staged: Vec<(Vec<BitVec>, Option<Vec<BitVec>>, Vec<NodeId>)> = Vec::new();
                let by_size = &self.by_size;
                let closure = self.closure.as_ref();
                let num_examples = self.num_examples;
                let nodes = &self.nodes;
                let assoc_skip_lhs = class.associative
                    && child_nts.len() == 2
                    && child_nts[0] == child_nts[1];
                let nary_pruned = self.pruned_plans.get(&(nt_idx, fid)).cloned();
                let nary_batch_plan: Option<&BitCircuitPlan> = if closure.is_none() {
                    nary_pruned.as_deref()
                        .or_else(|| deffun::ENV.deffun(fid).bit_circuit_plan())
                } else {
                    None
                };
                let use_batch = nary_batch_plan.is_some_and(|p| p.bindings.len() > 256);
                let mut splits = Vec::with_capacity(child_nts.len());
                if use_batch {
                    let plan = nary_batch_plan.unwrap();
                    let k = num_examples;
                    let nargs = child_nts.len();
                    let mut batch_nodes: Vec<Vec<NodeId>> = Vec::with_capacity(64);
                    let mut batch_args: Vec<Vec<BitVec>> = Vec::with_capacity(64);

                    let flush_batch = |batch_nodes: &mut Vec<Vec<NodeId>>,
                                       batch_args: &mut Vec<Vec<BitVec>>,
                                       staged: &mut Vec<(Vec<BitVec>, Option<Vec<BitVec>>, Vec<NodeId>)>,
                                       plan: &BitCircuitPlan,
                                       k: usize| {
                        let count = batch_nodes.len();
                        if count == 0 { return; }

                        let staged_base = staged.len();
                        for j in 0..count {
                            staged.push((Vec::with_capacity(k), None, batch_nodes[j].clone()));
                        }
                        let refs: Vec<&[BitVec]> = batch_args.iter().map(|a| a.as_slice()).collect();
                        for i in 0..k {
                            let example_refs: Vec<&[BitVec]> = (0..count)
                                .map(|j| refs[j * k + i])
                                .collect();
                            let results = plan.eval_batch(&example_refs, count);
                            for (j, val) in results.into_iter().enumerate() {
                                staged[staged_base + j].0.push(val);
                            }
                        }

                        batch_nodes.clear();
                        batch_args.clear();
                    };

                    let enqueue_tuple = |tuple: &[&Candidate],
                                              batch_nodes: &mut Vec<Vec<NodeId>>,
                                              batch_args: &mut Vec<Vec<BitVec>>,
                                              staged: &mut Vec<(Vec<BitVec>, Option<Vec<BitVec>>, Vec<NodeId>)>,
                                              plan: &BitCircuitPlan,
                                              k: usize| {
                        if assoc_skip_lhs && nodes[tuple[0].node].rule_idx == rule_idx {
                            return;
                        }
                        let children: Vec<NodeId> = tuple.iter().map(|c| c.node).collect();
                        for i in 0..k {
                            let args: Vec<BitVec> = tuple.iter().map(|c| c.values[i].clone()).collect();
                            batch_args.push(args);
                        }
                        batch_nodes.push(children);
                        if batch_nodes.len() == 64 {
                            flush_batch(batch_nodes, batch_args, staged, plan, k);
                        }
                    };

                    let is_binary_same_nt = nargs == 2 && child_nts[0] == child_nts[1];
                    if is_binary_same_nt && class.commutative {
                        let nt = child_nts[0];
                        for lhs_size in 1..=child_total / 2 {
                            let rhs_size = child_total - lhs_size;
                            let lhs_pool = by_size[nt].get(lhs_size).map(Vec::as_slice).unwrap_or(&[]);
                            let rhs_pool = by_size[nt].get(rhs_size).map(Vec::as_slice).unwrap_or(&[]);
                            if lhs_pool.is_empty() || rhs_pool.is_empty() { continue; }
                            if lhs_size == rhs_size {
                                for (i, lhs) in lhs_pool.iter().enumerate() {
                                    let start = if class.idempotent { i + 1 } else { i };
                                    for rhs in &rhs_pool[start..] {
                                        enqueue_tuple(&[lhs, rhs], &mut batch_nodes, &mut batch_args, &mut staged, plan, k);
                                    }
                                }
                            } else {
                                for lhs in lhs_pool {
                                    for rhs in rhs_pool {
                                        enqueue_tuple(&[lhs, rhs], &mut batch_nodes, &mut batch_args, &mut staged, plan, k);
                                    }
                                }
                            }
                        }
                    } else {
                        for_each_size_split(
                            child_total,
                            nargs,
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
                                let mut tuple = Vec::with_capacity(nargs);
                                for_each_candidate_tuple(&pools, &mut tuple, &mut |tuple| {
                                    if assoc_skip_lhs && nodes[tuple[0].node].rule_idx == rule_idx {
                                        return;
                                    }
                                    let children: Vec<NodeId> = tuple.iter().map(|c| c.node).collect();
                                    for i in 0..k {
                                        let args: Vec<BitVec> = tuple.iter().map(|c| c.values[i].clone()).collect();
                                        batch_args.push(args);
                                    }
                                    batch_nodes.push(children);

                                    if batch_nodes.len() == 64 {
                                        flush_batch(&mut batch_nodes, &mut batch_args, &mut staged, plan, k);
                                    }
                                });
                            },
                        );
                    }
                    // flush remaining
                    flush_batch(&mut batch_nodes, &mut batch_args, &mut staged, plan, k);
                } else {
                    let is_binary_same_nt = child_nts.len() == 2 && child_nts[0] == child_nts[1];

                    if class.shift_rhs_literal && child_nts.len() == 2 && child_total >= 1 {
                        let lhs_nt = child_nts[0];
                        let rhs_nt = child_nts[1];
                        let lhs_size = child_total - 1;
                        if lhs_size >= 1 {
                            let lhs_pool = by_size[lhs_nt].get(lhs_size).map(Vec::as_slice).unwrap_or(&[]);
                            let rhs_pool = by_size[rhs_nt].get(1).map(Vec::as_slice).unwrap_or(&[]);
                            if !lhs_pool.is_empty() && !rhs_pool.is_empty() {
                                for lhs in lhs_pool {

                                    for rhs in rhs_pool {

                                        let tuple: &[&Candidate] = &[lhs, rhs];
                                        let Some((values, values_top)) =
                                            Self::eval_nary_with_plan(fid, tuple, closure, num_examples, nary_pruned.as_deref())
                                        else { continue };
                                        let children = vec![lhs.node, rhs.node];
                                        staged.push((values, values_top, children));
                                    }
                                }
                            }
                        }
                    } else if is_binary_same_nt && class.commutative {
                        // Commutative: only enumerate lhs_size <= rhs_size
                        let nt = child_nts[0];
                        for lhs_size in 1..=child_total / 2 {
                            let rhs_size = child_total - lhs_size;
                            let lhs_pool = by_size[nt].get(lhs_size).map(Vec::as_slice).unwrap_or(&[]);
                            let rhs_pool = by_size[nt].get(rhs_size).map(Vec::as_slice).unwrap_or(&[]);
                            if lhs_pool.is_empty() || rhs_pool.is_empty() { continue; }

                            if lhs_size == rhs_size {
                                for (i, lhs) in lhs_pool.iter().enumerate() {
                                    if assoc_skip_lhs && self.nodes[lhs.node].rule_idx == rule_idx { continue; }
                                    let start = if class.idempotent { i + 1 } else { i };
                                    for rhs in &rhs_pool[start..] {

                                        if class.nonzero_rhs && rhs.values.iter().all(|v| v.is_zero()) { continue; }
                                        let tuple: &[&Candidate] = &[lhs, rhs];
                                        let Some((values, values_top)) =
                                            Self::eval_nary_with_plan(fid, tuple, closure, num_examples, nary_pruned.as_deref())
                                        else { continue };
                                        let children = vec![lhs.node, rhs.node];
                                        staged.push((values, values_top, children));
                                    }
                                }
                            } else {
                                // Off-diagonal: full cross-product (lhs_size < rhs_size already ensures no dup)
                                for lhs in lhs_pool {
                                    if assoc_skip_lhs && self.nodes[lhs.node].rule_idx == rule_idx { continue; }
                                    for rhs in rhs_pool {
                                        if class.nonzero_rhs && rhs.values.iter().all(|v| v.is_zero()) { continue; }
                                        let tuple: &[&Candidate] = &[lhs, rhs];
                                        let Some((values, values_top)) =
                                            Self::eval_nary_with_plan(fid, tuple, closure, num_examples, nary_pruned.as_deref())
                                        else { continue };
                                        let children = vec![lhs.node, rhs.node];
                                        staged.push((values, values_top, children));
                                    }
                                }
                            }
                        }
                    } else {
                        // General case: full cross-product
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
                                    if assoc_skip_lhs && self.nodes[tuple[0].node].rule_idx == rule_idx {
                                        return;
                                    }
                                    if class.nonzero_rhs && child_nts.len() == 2 {
                                        if tuple[1].values.iter().all(|v| v.is_zero()) { return; }
                                    }
                                    let Some((values, values_top)) =
                                        Self::eval_nary_with_plan(fid, tuple, closure, num_examples, nary_pruned.as_deref())
                                    else {
                                        return;
                                    };
                                    let children = tuple.iter().map(|c| c.node).collect();
                                    staged.push((values, values_top, children));
                                });
                            },
                        );
                    }
                }

                for (values, values_top, children) in staged {
                    if let Some(found) = self.try_push_new(
                        nt_idx,
                        size,
                        values,
                        values_top,
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
                        let k = self.num_examples;
                        let mut values = Vec::with_capacity(k);
                        let mut ok = true;
                        for i in 0..k {
                            let args = &self.spec.examples[i].args;
                            match template.evaluate_with_args(args, &mut self.leaf_cache) {
                                Ok(v) => values.push(v),
                                Err(_) => { ok = false; break; }
                            }
                        }
                        if ok {
                            return Ok(self.try_push_new(
                                nt_idx,
                                size,
                                values,
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
                let mut staged: Vec<(Vec<BitVec>, Vec<NodeId>)> = Vec::new();
                let by_size = &self.by_size;
                let leaf_cache = &mut self.leaf_cache;
                let num_examples = self.num_examples;
                let spec_examples = &self.spec.examples;
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
                            let mut all_values = Vec::with_capacity(num_examples);
                            let mut ok = true;
                            for i in 0..num_examples {
                                let child_values: Vec<BitVec> =
                                    tuple.iter().map(|c| c.values[i].clone()).collect();
                                match template.evaluate_with_args_and_children(
                                    &spec_examples[i].args,
                                    &child_values,
                                    leaf_cache,
                                ) {
                                    Ok(v) => all_values.push(v),
                                    Err(_) => { ok = false; break; }
                                }
                            }
                            if ok {
                                let children = tuple.iter().map(|c| c.node).collect();
                                staged.push((all_values, children));
                            }
                        });
                    },
                );
                for (values, children) in staged {
                    if let Some(found) = self.try_push_new(
                        nt_idx,
                        size,
                        values,
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

    // ----- Per-rule eval helpers: return (values@0, values_top? in fixpoint mode)
    //       For multi-example: values has K entries (one per example).
    //       For LFP mode (always K=1): values_top has K entries at aux=top.

    fn eval_leaf(&mut self, expr: &OwnedExpr) -> Option<(Vec<BitVec>, Option<Vec<BitVec>>)> {
        if self.closure.is_some() {
            let closure = self.closure.as_ref().unwrap();
            let zero_bindings = closure.bindings_zero();
            let top_bindings = closure.bindings_top();
            // Legacy LFP path uses Var(0) for self-reference; thread the
            // primary aux's value through `args` for that, while passing
            // the full bindings for any closure_args inside Func calls.
            let v = closure.zero(0).clone();
            let value = self
                .leaf_cache
                .leaves
                .entry(expr.clone())
                .or_insert_with(|| {
                    expr.eval_with_bindings(&[v.clone()], &zero_bindings).ok()
                })
                .clone()?;
            let top = closure.top(0).clone();
            let value_top = expr
                .eval_with_bindings(&[top], &top_bindings)
                .ok()?;
            return Some((vec![value], Some(vec![value_top])));
        }
        let k = self.num_examples;
        let mut values = Vec::with_capacity(k);
        for i in 0..k {
            let args = &self.spec.examples[i].args;
            let v = expr.eval(args).ok()?;
            values.push(v);
        }
        Some((values, None))
    }

    fn eval_nary_with_plan(
        fid: usize,
        tuple: &[&Candidate],
        closure: Option<&Bindings>,
        num_examples: usize,
        pruned_plan: Option<&BitCircuitPlan>,
    ) -> Option<(Vec<BitVec>, Option<Vec<BitVec>>)> {
        if let Some(closure) = closure {
            let args_zero: Vec<BitVec> = tuple.iter().map(|c| c.values[0].clone()).collect();
            let zero_bindings = closure.bindings_zero();
            let value = deffun::ENV
                .eval_defined(fid, &args_zero, &zero_bindings)
                .ok()?;
            let args_top: Option<Vec<BitVec>> = tuple.iter().map(|c| {
                c.values_top.as_ref().map(|vt| vt[0].clone())
            }).collect();
            let args_top = args_top?;
            let top_bindings = closure.bindings_top();
            let value_top = deffun::ENV
                .eval_defined(fid, &args_top, &top_bindings)
                .ok()?;
            return Some((vec![value], Some(vec![value_top])));
        }
        let k = num_examples;
        let mut values = Vec::with_capacity(k);
        for i in 0..k {
            let args: Vec<BitVec> = tuple.iter().map(|c| c.values[i].clone()).collect();
            let v = if let Some(plan) = pruned_plan {
                plan.eval(&args).ok()?
            } else {
                deffun::ENV.eval_defined(fid, &args, &[]).ok()?
            };
            values.push(v);
        }
        Some((values, None))
    }

    // ----- Push helpers

    fn try_push_new(
        &mut self,
        nt_idx: usize,
        size: usize,
        values: Vec<BitVec>,
        values_top: Option<Vec<BitVec>>,
        build_node: impl FnOnce() -> Node,
    ) -> Option<OwnedExpr> {
        if nt_idx == self.grammar.start && self.closure.is_some() {
            let node = self.intern_node(build_node());
            return self.start_nt_kleene(node, size);
        }
        let matches_spec = nt_idx == self.grammar.start
            && self.closure.is_none()
            && self.spec.matches(&values);
        if self.closure.is_none()
            && self.seen.contains_or_insert_multi(nt_idx, &values, size)
        {
            return None;
        }
        if let Some(vt) = values_top.as_ref() {
            if self.seen.contains_or_insert_pair(nt_idx, &vt[0], &vt[0], size) {
                return None;
            }
        }
        let node = self.intern_node(build_node());
        if let Some(closure) = self.closure.as_ref() {
            DedupStats::record_push(
                nt_idx, size, node, &values[0], &self.grammar, &self.nodes, closure.name(0),
            );
        }
        let vi_key: Vec<u64> = values.iter().map(|v| v.first_u64_word()).collect();
        self.value_index[nt_idx].entry(vi_key).or_default().push(node);
        self.by_size[nt_idx][size].push(Candidate { node, values, values_top });
        if matches_spec {
            return self.grammar.materialize_node(node, &self.nodes);
        }
        None
    }

    fn try_push_existing(
        &mut self,
        nt_idx: usize,
        candidate: Candidate,
        size: usize,
    ) -> Option<OwnedExpr> {
        if nt_idx == self.grammar.start && self.closure.is_some() {
            return self.start_nt_kleene(candidate.node, size);
        }
        let matches_spec = nt_idx == self.grammar.start
            && self.closure.is_none()
            && self.spec.matches(&candidate.values);
        if self.closure.is_none()
            && self.seen.contains_or_insert_multi(nt_idx, &candidate.values, size)
        {
            return None;
        }
        if let Some(vt) = candidate.values_top.as_ref() {
            if self.seen.contains_or_insert_pair(nt_idx, &vt[0], &vt[0], size) {
                return None;
            }
        }
        if let Some(closure) = self.closure.as_ref() {
            DedupStats::record_push(
                nt_idx, size, candidate.node,
                &candidate.values[0], &self.grammar, &self.nodes, closure.name(0),
            );
        }
        let node = candidate.node;
        self.by_size[nt_idx][size].push(candidate);
        if matches_spec {
            return self.grammar.materialize_node(node, &self.nodes);
        }
        None
    }

    fn start_nt_kleene(&mut self, node: NodeId, size: usize) -> Option<OwnedExpr> {
        let closure_name = self
            .closure
            .as_ref()
            .expect("start_nt_kleene called outside fixpoint mode")
            .name(0)
            .to_string();
        let (expr, lfp) = self.kleene_lfp(node, &closure_name)?;
        if self.spec.matches(std::slice::from_ref(&lfp)) {
            return Some(expr);
        }
        if !self.seen.contains_or_insert_lfp(&lfp, size) {
            self.by_size[self.grammar.start][size].push(Candidate {
                node,
                values: vec![lfp],
                values_top: None,
            });
        }
        None
    }

    fn intern_node(&mut self, node: Node) -> NodeId {
        let id = self.nodes.len();
        self.nodes.push(node);
        id
    }

    fn kleene_lfp(
        &self,
        node: NodeId,
        closure_name: &str,
    ) -> Option<(OwnedExpr, BitVec)> {
        let bits = self.spec.bits;
        let (_pos, neg_indices) = self.spec.label_indices()?;
        let mut aux = BitVec::zero(bits);
        for _ in 0..=bits {
            let next = self
                .grammar
                .eval_node_at(node, &self.nodes, &[(closure_name, &aux)])?;
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

    // ── Composition via partial evaluation ────────────────────────────

    fn try_compose(&mut self) -> Option<OwnedExpr> {
        use crate::parse::deffun::PartialBit;
        let start = self.grammar.start;
        let targets: Vec<BitVec> = self.spec.examples.iter()
            .map(|e| e.output.clone())
            .collect();
        let masks: Vec<BitVec> = self.spec.examples.iter()
            .map(|e| e.mask.clone())
            .collect();
        // One-time diagnostic: check invertibility of first candidate on first rule
        if self.by_size[start].iter().map(|b| b.len()).sum::<usize>() == 5 {
            for rule in &self.grammar.nts[start].1 {
                let ExactRule::Op { fid, child_nts, .. } = rule else { continue };
                if child_nts.len() != 2 { continue }
                let plan = self.pruned_plans.get(&(start, *fid))
                    .map(|rc| rc.as_ref())
                    .or_else(|| deffun::ENV.deffun(*fid).bit_circuit_plan());
                let Some(plan) = plan else { continue };
                if let Some(c1) = self.by_size[child_nts[0]].iter().flat_map(|b| b.iter()).next() {
                    let pe = plan.partial_eval(0, &c1.values[0]);
                    let mut n_const = 0;
                    let mut n_input = 0;
                    let mut n_complex = 0;
                    for b in 0..self.spec.bits {
                        match pe[b] {
                            PartialBit::Const(_) => n_const += 1,
                            PartialBit::Input { .. } => n_input += 1,
                            PartialBit::Complex => n_complex += 1,
                        }
                    }
                    info!(
                        "compose diag: fid={} ({}) bindings={} pe: {} const, {} input, {} complex / {} total",
                        fid, deffun::ENV.name(*fid), plan.bindings.len(),
                        n_const, n_input, n_complex, self.spec.bits
                    );
                }
            }
        }
        self.compose_value(start, &targets, Some(&masks), 4)
    }

    fn compose_value(
        &self,
        nt: usize,
        targets: &[BitVec],
        masks: Option<&[BitVec]>,
        depth: usize,
    ) -> Option<OwnedExpr> {
        let k = targets.len();

        // Direct lookup in value_index
        let vi_key: Vec<u64> = targets.iter().map(|v| v.first_u64_word()).collect();
        if let Some(nodes) = self.value_index[nt].get(&vi_key) {
            for &node_id in nodes {
                let c = self.by_size[nt].iter()
                    .flat_map(|b| b.iter())
                    .find(|c| c.node == node_id);
                let Some(c) = c else { continue };
                let ok = (0..k).all(|ex| {
                    match masks {
                        Some(m) => c.values[ex].matches_masked(&targets[ex], &m[ex]),
                        None => c.values[ex] == targets[ex],
                    }
                });
                if ok {
                    return self.grammar.materialize_node(node_id, &self.nodes);
                }
            }
        }

        // Also scan pool for masked match when masks are present
        // (value_index key might miss due to mask alignment)
        if let Some(masks) = masks {
            'scan: for bucket in &self.by_size[nt] {
                for c in bucket {
                    for ex in 0..k {
                        if !c.values[ex].matches_masked(&targets[ex], &masks[ex]) {
                            continue 'scan;
                        }
                    }
                    return self.grammar.materialize_node(c.node, &self.nodes);
                }
            }
        }

        if depth == 0 { return None; }

        // Try composing via each binary rule for this NT
        for rule in &self.grammar.nts[nt].1 {
            let ExactRule::Op { fid, child_nts, .. } = rule else { continue };
            if child_nts.len() != 2 { continue }
            let plan = self.pruned_plans.get(&(nt, *fid))
                .map(|rc| rc.as_ref())
                .or_else(|| deffun::ENV.deffun(*fid).bit_circuit_plan());
            let Some(plan) = plan else { continue };
            let arg_bits = deffun::ENV.arg_bits(*fid);
            let out_bits = deffun::ENV.ret_bits(*fid);

            for fixed_pos in 0..2 {
                let other_pos = 1 - fixed_pos;
                let other_bits = arg_bits[other_pos];
                let n_other_words = other_bits.div_ceil(64);

                for bucket in &self.by_size[child_nts[fixed_pos]] {
                    for c1 in bucket {
                        if let Some(sub_targets) = self.invert_for_other(
                            plan, fixed_pos, other_pos, c1, targets, masks,
                            k, out_bits, other_bits, n_other_words,
                        ) {
                            // Try finding or composing the sub-target
                            let other_nt = child_nts[other_pos];
                            if let Some(sub_expr) = self.compose_value(
                                other_nt, &sub_targets, None, depth - 1,
                            ) {
                                let mut child_exprs = vec![OwnedExpr::Const(BitVec::zero(1)); 2];
                                child_exprs[fixed_pos] = self.grammar.materialize_node(c1.node, &self.nodes)?;
                                child_exprs[other_pos] = sub_expr;
                                info!(
                                    "compose: fid={} ({}) fixed_pos={} depth={}",
                                    fid, deffun::ENV.name(*fid), fixed_pos, depth
                                );
                                return Some(OwnedExpr::Func(*fid, child_exprs));
                            }
                        }
                    }
                }
            }
        }
        None
    }

    fn invert_for_other(
        &self,
        plan: &BitCircuitPlan,
        fixed_pos: usize,
        other_pos: usize,
        c1: &Candidate,
        targets: &[BitVec],
        masks: Option<&[BitVec]>,
        k: usize,
        out_bits: usize,
        other_bits: usize,
        n_other_words: usize,
    ) -> Option<Vec<BitVec>> {
        use crate::parse::deffun::PartialBit;

        let mut result = Vec::with_capacity(k);
        for ex in 0..k {
            let pe = plan.partial_eval(fixed_pos, &c1.values[ex]);
            let mut tw = vec![0u64; n_other_words];
            for b in 0..out_bits {
                let demanded = masks.map_or(true, |m| m[ex].bit(b));
                if !demanded { continue; }
                match pe[b] {
                    PartialBit::Const(v) => {
                        if v != targets[ex].bit(b) {
                            return None;
                        }
                    }
                    PartialBit::Input { arg, bit, negated } if arg == other_pos && bit < other_bits => {
                        let required = targets[ex].bit(b) ^ negated;
                        if required {
                            tw[bit / 64] |= 1u64 << (bit % 64);
                        }
                    }
                    _ => return None,
                }
            }
            result.push(BitVec::from_u64_words(&tw, other_bits));
        }
        Some(result)
    }
}


fn log_grammar_summary(grammar: &Grammar<'_>) {
    let mut leaf = 0usize;
    let mut alias = 0usize;
    let mut op = 0usize;
    let mut generic = 0usize;
    for (_, rules) in &grammar.nts {
        for rule in rules {
            match rule {
                ExactRule::Alias(_) => alias += 1,
                ExactRule::Leaf(_) => leaf += 1,
                ExactRule::Op { .. } => op += 1,
                ExactRule::GenericTemplate { .. } => generic += 1,
            }
        }
    }
    debg!(
        "exact-nullary grammar nts={} leaf={} alias={} op={} generic={}",
        grammar.nts.len(),
        leaf,
        alias,
        op,
        generic
    );
}

// (Old BitDep-guided decomposition removed — replaced by general
// composition via BitCircuitPlan::partial_eval in Searcher::try_compose.)
// The removed code: BitOwner, DecompRule, analyze_decomposable_rules,
// probe_polarity, solve_sub, decompose, find_match, spec_masks.

/// Build the `Grammar` and dispatch to the `Searcher`. Replaces the
/// old free-function `search_nullary_multi_nt`.
pub fn search_problem<'a>(
    problem: &'a SynthProblem<'static>,
    spec: &Constraint,
    min: bool,
    fixpoint: Option<&'a str>,
    enable_decomp: bool,
) -> parse::Result<OwnedExpr> {
    let cfg_start = Instant::now();
    let multi = Config::from_problem(problem)?;
    debg!(
        "exact multi-config built in {:?}",
        cfg_start.elapsed()
    );
    let grammar_start = Instant::now();
    let grammar = Grammar::from_config(&multi);
    debg!(
        "exact grammar built in {:?}",
        grammar_start.elapsed()
    );
    run_search(grammar, spec, min, fixpoint, enable_decomp)
}
