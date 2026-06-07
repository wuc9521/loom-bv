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

use crate::debg;
use crate::enumerate::{
    expr::OwnedExpr,
    grammar::{for_each_candidate_tuple, for_each_size_split, Config},
    value::BitVec,
};
use crate::exact::bitspec::Constraint;
use crate::exact::closure::Closure;
use crate::exact::dedup::SeenMode;
use crate::exact::eval::eval_defined_with_closure;
use crate::exact::stats::DedupStats;
use crate::exact::types::{Candidate, ExactEvalCache, Grammar, ExactRule, Node, NodeId};
use crate::parse::{self, deffun, SynthProblem};
use crate::parse::deffun::BitCircuitPlan;

pub fn run_search<'a>(
    grammar: Grammar<'a>,
    spec: &Constraint,
    min: bool,
    fixpoint: Option<&str>,
) -> parse::Result<OwnedExpr> {
    Searcher::new(grammar, spec, min, fixpoint).run()
}

struct Searcher<'a, 'g> {
    grammar: Grammar<'a>,
    spec: &'g Constraint,
    num_examples: usize,
    closure: Option<Closure>,
    nodes: Vec<Node>,
    by_size: Vec<Vec<Vec<Candidate>>>,
    seen: SeenMode,
    leaf_cache: ExactEvalCache,
    pruned_plans: rustc_hash::FxHashMap<(usize, usize), std::rc::Rc<BitCircuitPlan>>,
}

impl<'a, 'g> Searcher<'a, 'g> {
    fn new(
        grammar: Grammar<'a>,
        spec: &'g Constraint,
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
            ExactRule::Op { fid, child_nts } => {
                if size <= child_nts.len() {
                    return Ok(None);
                }
                let child_total = size - 1;
                let mut staged: Vec<(Vec<BitVec>, Option<Vec<BitVec>>, Vec<NodeId>)> = Vec::new();
                let by_size = &self.by_size;
                let closure = self.closure.as_ref();
                let num_examples = self.num_examples;
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
                    // flush remaining
                    flush_batch(&mut batch_nodes, &mut batch_args, &mut staged, plan, k);
                } else {
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

    fn eval_nary_with_plan(
        fid: usize,
        tuple: &[&Candidate],
        closure: Option<&Closure>,
        num_examples: usize,
        pruned_plan: Option<&BitCircuitPlan>,
    ) -> Option<(Vec<BitVec>, Option<Vec<BitVec>>)> {
        if let Some(closure) = closure {
            let args_zero: Vec<BitVec> = tuple.iter().map(|c| c.values[0].clone()).collect();
            let value = eval_defined_with_closure(
                fid, &args_zero, Some(closure.binding_zero()),
            ).ok()?;
            let args_top: Option<Vec<BitVec>> = tuple.iter().map(|c| {
                c.values_top.as_ref().map(|vt| vt[0].clone())
            }).collect();
            let args_top = args_top?;
            let value_top = eval_defined_with_closure(
                fid, &args_top, Some(closure.binding_top()),
            ).ok()?;
            return Some((vec![value], Some(vec![value_top])));
        }
        let k = num_examples;
        let mut values = Vec::with_capacity(k);
        for i in 0..k {
            let args: Vec<BitVec> = tuple.iter().map(|c| c.values[i].clone()).collect();
            let v = if let Some(plan) = pruned_plan {
                plan.eval(&args).ok()?
            } else {
                eval_defined_with_closure(fid, &args, None).ok()?
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
    ) -> Option<(OwnedExpr, BitVec)> {
        let bits = self.spec.bits;
        let (_pos, neg_indices) = self.spec.label_indices()?;
        let mut aux = BitVec::zero(bits);
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

/// Build the `Grammar` and dispatch to the `Searcher`. Replaces the
/// old free-function `search_nullary_multi_nt`.
pub fn search_problem<'a>(
    problem: &'a SynthProblem<'static>,
    spec: &Constraint,
    min: bool,
    fixpoint: Option<&'a str>,
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
    run_search(grammar, spec, min, fixpoint)
}
