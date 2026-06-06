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
use crate::exact::bitspec::BitSpec;
use crate::exact::closure::Closure;
use crate::exact::dedup::SeenMode;
use crate::exact::eval::eval_defined_with_closure;
use crate::exact::stats::DedupStats;
use crate::exact::types::{Candidate, ExactEvalCache, ExactGrammar, ExactRule, Node, NodeId};
use crate::parse::{self, deffun, SynthProblem};
use crate::parse::deffun::BitCircuitPlan;

pub fn run_search<'a>(
    grammar: ExactGrammar<'a>,
    spec: &BitSpec,
    min: bool,
    fixpoint: Option<&str>,
) -> parse::Result<OwnedExpr> {
    Searcher::new(grammar, spec, min, fixpoint).run()
}

struct Searcher<'a, 'g> {
    grammar: ExactGrammar<'a>,
    spec: &'g BitSpec,
    num_examples: usize,
    closure: Option<Closure>,
    nodes: Vec<Node>,
    by_size: Vec<Vec<Vec<Candidate>>>,
    seen: SeenMode,
    leaf_cache: ExactEvalCache,
    pruned_plans: rustc_hash::FxHashMap<(usize, usize), BitCircuitPlan>,
}

impl<'a, 'g> Searcher<'a, 'g> {
    fn new(
        grammar: ExactGrammar<'a>,
        spec: &'g BitSpec,
        min: bool,
        fixpoint: Option<&str>,
    ) -> Self {
        let num_examples = spec.num_examples();
        let closure = match fixpoint {
            Some(name) => Some(Closure::new(name, spec.bits)),
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
        let pruned_plans: rustc_hash::FxHashMap<(usize, usize), BitCircuitPlan> =
            rustc_hash::FxHashMap::default();
        // TODO: cone-of-influence pruning for start-NT. The infrastructure
        // (BitCircuitPlan::pruned) is ready but needs proper integration
        // testing with wide bitvectors before enabling.
        let nt_count = grammar.nts.len();
        let seen = if closure.is_some() {
            SeenMode::pair(nt_count, grammar.start)
        } else if let Some(relevant_bits) = eager_relevant_bits {
            SeenMode::multi_projected(relevant_bits, num_examples)
        } else {
            SeenMode::multi_exact(nt_count, num_examples)
        };
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
                "search size={}: per-nt={:?} total={} elapsed={:?}",
                size,
                per_nt,
                total,
                run_start.elapsed()
            );
            DedupStats::snapshot_line(&format!("dedup@size={}", size));
        }
        unreachable!("nullary enumeration should either find a solution or diverge");
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
            ExactRule::Unary { fid, child_nt } => {
                if size < 2 {
                    return Ok(None);
                }
                let child_size = size - 1;
                let children = self.by_size[child_nt].get(child_size).cloned().unwrap_or_default();
                let owned_pruned = self.pruned_plans.get(&(nt_idx, fid)).cloned();
                let batch_plan = if self.closure.is_none() {
                    owned_pruned.as_ref()
                        .or_else(|| deffun::ENV.deffun(fid, 1).bit_circuit_plan())
                } else {
                    None
                };
                let use_batch = batch_plan.is_some_and(|p| p.bindings.len() > 256);
                if use_batch {
                    let plan = batch_plan.unwrap();
                    let k = self.num_examples;
                    let total = children.len();
                    let mut idx = 0;
                    while idx < total {
                        let batch_end = (idx + 64).min(total);
                        let count = batch_end - idx;
                        let mut all_values: Vec<Vec<Value>> =
                            (0..count).map(|_| Vec::with_capacity(k)).collect();
                        for i in 0..k {
                            let args_batch: Vec<[Value; 1]> = (idx..batch_end)
                                .map(|ci| [children[ci].values[i].clone()])
                                .collect();
                            let refs: Vec<&[Value]> =
                                args_batch.iter().map(|a| a.as_slice()).collect();
                            let results = plan.eval_batch(&refs, count);
                            for (j, val) in results.into_iter().enumerate() {
                                all_values[j].push(val);
                            }
                        }
                        for (batch_idx, ci) in (idx..batch_end).enumerate() {
                            let values = std::mem::take(&mut all_values[batch_idx]);
                            let child_node = children[ci].node;
                            if let Some(found) = self.try_push_new(
                                nt_idx,
                                size,
                                values,
                                None,
                                || Node { nt_idx, rule_idx, children: vec![child_node] },
                            ) {
                                return Ok(Some(found));
                            }
                        }
                        idx = batch_end;
                    }
                } else {
                    for child in &children {
                        let Some((values, values_top)) = self.eval_unary(fid, child) else { continue; };
                        let child_node = child.node;
                        if let Some(found) = self.try_push_new(
                            nt_idx,
                            size,
                            values,
                            values_top,
                            || Node { nt_idx, rule_idx, children: vec![child_node] },
                        ) {
                            return Ok(Some(found));
                        }
                    }
                }
                Ok(None)
            }
            ExactRule::Binary { fid, lhs_nt, rhs_nt } => {
                if size < 3 {
                    return Ok(None);
                }
                let owned_pruned = self.pruned_plans.get(&(nt_idx, fid)).cloned();
                let batch_plan = if self.closure.is_none() {
                    owned_pruned.as_ref()
                        .or_else(|| deffun::ENV.deffun(fid, 2).bit_circuit_plan())
                } else {
                    None
                };
                let use_batch = batch_plan.is_some_and(|p| p.bindings.len() > 256);
                for lhs_size in 1..(size - 1) {
                    let rhs_size = size - 1 - lhs_size;
                    let lhs_pool = self.by_size[lhs_nt].get(lhs_size).cloned().unwrap_or_default();
                    let rhs_pool = self.by_size[rhs_nt].get(rhs_size).cloned().unwrap_or_default();
                    if lhs_pool.is_empty() || rhs_pool.is_empty() {
                        continue;
                    }
                    if use_batch {
                        let plan = batch_plan.unwrap();
                        let k = self.num_examples;
                        let total_pairs = lhs_pool.len() * rhs_pool.len();
                        let mut pair_idx = 0;
                        while pair_idx < total_pairs {
                            let batch_end = (pair_idx + 64).min(total_pairs);
                            let count = batch_end - pair_idx;
                            let mut all_values: Vec<Vec<Value>> =
                                (0..count).map(|_| Vec::with_capacity(k)).collect();
                            let mut batch_indices: Vec<(usize, usize)> = Vec::with_capacity(count);
                            for flat in pair_idx..batch_end {
                                let li = flat / rhs_pool.len();
                                let ri = flat % rhs_pool.len();
                                batch_indices.push((li, ri));
                            }
                            for i in 0..k {
                                let args_batch: Vec<[Value; 2]> = batch_indices
                                    .iter()
                                    .map(|(li, ri)| {
                                        [
                                            lhs_pool[*li].values[i].clone(),
                                            rhs_pool[*ri].values[i].clone(),
                                        ]
                                    })
                                    .collect();
                                let refs: Vec<&[Value]> =
                                    args_batch.iter().map(|a| a.as_slice()).collect();
                                let results = plan.eval_batch(&refs, count);
                                for (j, val) in results.into_iter().enumerate() {
                                    all_values[j].push(val);
                                }
                            }
                            for (batch_idx, (li, ri)) in batch_indices.iter().enumerate() {
                                let values = std::mem::take(&mut all_values[batch_idx]);
                                let (lhs_node, rhs_node) =
                                    (lhs_pool[*li].node, rhs_pool[*ri].node);
                                if let Some(found) = self.try_push_new(
                                    nt_idx,
                                    size,
                                    values,
                                    None,
                                    || Node {
                                        nt_idx,
                                        rule_idx,
                                        children: vec![lhs_node, rhs_node],
                                    },
                                ) {
                                    return Ok(Some(found));
                                }
                            }
                            pair_idx = batch_end;
                        }
                    } else {
                        for lhs in &lhs_pool {
                            for rhs in &rhs_pool {
                                let Some((values, values_top)) = self.eval_binary(fid, lhs, rhs) else {
                                    continue;
                                };
                                let (lhs_node, rhs_node) = (lhs.node, rhs.node);
                                if let Some(found) = self.try_push_new(
                                    nt_idx,
                                    size,
                                    values,
                                    values_top,
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
                }
                Ok(None)
            }
            ExactRule::Nary { fid, child_nts } => {
                if size <= child_nts.len() {
                    return Ok(None);
                }
                let child_total = size - 1;
                let mut staged: Vec<(Vec<Value>, Option<Vec<Value>>, Vec<NodeId>)> = Vec::new();
                let by_size = &self.by_size;
                let closure = self.closure.as_ref();
                let num_examples = self.num_examples;
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
                            let Some((values, values_top)) =
                                Self::eval_nary_static(fid, tuple, closure, num_examples)
                            else {
                                return;
                            };
                            let children = tuple.iter().map(|c| c.node).collect();
                            staged.push((values, values_top, children));
                        });
                    },
                );
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
                let mut staged: Vec<(Vec<Value>, Vec<NodeId>)> = Vec::new();
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
                                let child_values: Vec<Value> =
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

    fn eval_leaf(&mut self, expr: &OwnedExpr) -> Option<(Vec<Value>, Option<Vec<Value>>)> {
        if self.closure.is_some() {
            let closure = self.closure.as_ref().unwrap();
            let (name, v) = closure.binding_zero();
            let value = self
                .leaf_cache
                .leaves
                .entry(expr.clone())
                .or_insert_with(|| expr.eval_with_closure(&deffun::ENV, v, name).ok())
                .clone()?;
            let value_top = expr
                .eval_with_closure(&deffun::ENV, &closure.top, &closure.name)
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

    fn eval_unary(&self, fid: usize, child: &Candidate) -> Option<(Vec<Value>, Option<Vec<Value>>)> {
        if self.closure.is_some() {
            let closure = self.closure.as_ref().unwrap();
            let value = eval_defined_with_closure(
                fid, 1, std::slice::from_ref(&child.values[0]),
                Some(closure.binding_zero()),
            ).ok()?;
            let child_top = child.values_top.as_ref()?;
            let value_top = eval_defined_with_closure(
                fid, 1, std::slice::from_ref(&child_top[0]),
                Some(closure.binding_top()),
            ).ok()?;
            return Some((vec![value], Some(vec![value_top])));
        }
        let k = self.num_examples;
        let mut values = Vec::with_capacity(k);
        for i in 0..k {
            let v = eval_defined_with_closure(
                fid, 1, std::slice::from_ref(&child.values[i]), None,
            ).ok()?;
            values.push(v);
        }
        Some((values, None))
    }

    fn eval_binary(
        &self,
        fid: usize,
        lhs: &Candidate,
        rhs: &Candidate,
    ) -> Option<(Vec<Value>, Option<Vec<Value>>)> {
        if self.closure.is_some() {
            let closure = self.closure.as_ref().unwrap();
            let value = eval_defined_with_closure(
                fid, 2,
                &[lhs.values[0].clone(), rhs.values[0].clone()],
                Some(closure.binding_zero()),
            ).ok()?;
            let lt = &lhs.values_top.as_ref()?[0];
            let rt = &rhs.values_top.as_ref()?[0];
            let value_top = eval_defined_with_closure(
                fid, 2, &[lt.clone(), rt.clone()],
                Some(closure.binding_top()),
            ).ok()?;
            return Some((vec![value], Some(vec![value_top])));
        }
        let k = self.num_examples;
        let mut values = Vec::with_capacity(k);
        for i in 0..k {
            let v = eval_defined_with_closure(
                fid, 2,
                &[lhs.values[i].clone(), rhs.values[i].clone()],
                None,
            ).ok()?;
            values.push(v);
        }
        Some((values, None))
    }

    fn eval_nary_static(
        fid: usize,
        tuple: &[&Candidate],
        closure: Option<&Closure>,
        num_examples: usize,
    ) -> Option<(Vec<Value>, Option<Vec<Value>>)> {
        if let Some(closure) = closure {
            let args_zero: Vec<Value> = tuple.iter().map(|c| c.values[0].clone()).collect();
            let value = eval_defined_with_closure(
                fid, args_zero.len(), &args_zero, Some(closure.binding_zero()),
            ).ok()?;
            let args_top: Option<Vec<Value>> = tuple.iter().map(|c| {
                c.values_top.as_ref().map(|vt| vt[0].clone())
            }).collect();
            let args_top = args_top?;
            let value_top = eval_defined_with_closure(
                fid, args_top.len(), &args_top, Some(closure.binding_top()),
            ).ok()?;
            return Some((vec![value], Some(vec![value_top])));
        }
        let k = num_examples;
        let mut values = Vec::with_capacity(k);
        for i in 0..k {
            let args: Vec<Value> = tuple.iter().map(|c| c.values[i].clone()).collect();
            let v = eval_defined_with_closure(fid, args.len(), &args, None).ok()?;
            values.push(v);
        }
        Some((values, None))
    }

    // ----- Push helpers

    fn try_push_new(
        &mut self,
        nt_idx: usize,
        size: usize,
        values: Vec<Value>,
        values_top: Option<Vec<Value>>,
        build_node: impl FnOnce() -> Node,
    ) -> Option<OwnedExpr> {
        if nt_idx == self.grammar.start {
            if self.closure.is_some() {
                let node = self.intern_node(build_node());
                return self.start_nt_kleene(node, size);
            }
            if self.spec.matches(&values) {
                let node = self.intern_node(build_node());
                return self.grammar.materialize_node(node, &self.nodes);
            }
        }
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
                nt_idx, size, node, &values[0], &self.grammar, &self.nodes, &closure.name,
            );
        }
        self.by_size[nt_idx][size].push(Candidate { node, values, values_top });
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
            if self.spec.matches(&candidate.values) {
                return self.grammar.materialize_node(candidate.node, &self.nodes);
            }
        }
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
                &candidate.values[0], &self.grammar, &self.nodes, &closure.name,
            );
        }
        self.by_size[nt_idx][size].push(candidate);
        None
    }

    fn start_nt_kleene(&mut self, node: NodeId, size: usize) -> Option<OwnedExpr> {
        let closure_name = self
            .closure
            .as_ref()
            .expect("start_nt_kleene called outside fixpoint mode")
            .name
            .clone();
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
    ) -> Option<(OwnedExpr, Value)> {
        let bits = self.spec.bits;
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
    spec: &BitSpec,
    min: bool,
    fixpoint: Option<&'a str>,
) -> parse::Result<OwnedExpr> {
    let cfg_start = Instant::now();
    let multi = MultiConfig::from_problem(problem)?;
    debg!(
        "exact multi-config built in {:?}",
        cfg_start.elapsed()
    );
    let grammar_start = Instant::now();
    let grammar = ExactGrammar::from_config(&multi);
    debg!(
        "exact grammar built in {:?}",
        grammar_start.elapsed()
    );
    run_search(grammar, spec, min, fixpoint)
}
