use std::collections::hash_map::Entry;
use std::collections::BTreeMap;
use std::time::Instant;

pub mod closure;
mod grammar;
mod relevance;
mod spec;
mod util;

use rustc_hash::FxHashMap;
use sygus_parser::ast::SyGuSFile;

use crate::{
    enumerate::{
        expr::OwnedExpr,
        grammar::{build_owned_application, for_each_candidate_tuple, for_each_size_split, MultiConfig, TemplateExpr},
        value::Value,
    },
    info,
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
    pub fn search(
        &self,
        problem: &SynthProblem<'static>,
        min: bool,
        mitm: bool,
    ) -> parse::Result<OwnedExpr> {
        let cfg_start = Instant::now();
        let multi = MultiConfig::from_problem(problem)?;
        info!(
            "exact-nullary setup multi-config completed in {:?}",
            cfg_start.elapsed()
        );
        let grammar_start = Instant::now();
        let grammar = ExactGrammar::from_config(&multi);
        info!(
            "exact-nullary setup exact-grammar completed in {:?}",
            grammar_start.elapsed()
        );
        search_nullary_multi_nt(&grammar, self, min, mitm)
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

#[derive(Default)]
struct RefinementPressure {
    inserted: usize,
    collisions: usize,
}

impl RefinementPressure {
    fn credits(&self) -> usize {
        self.inserted.saturating_add(self.collisions)
    }
}

fn search_nullary_multi_nt(
    grammar: &ExactGrammar<'static>,
    spec: &NullarySpec,
    min: bool,
    mitm: bool,
) -> parse::Result<OwnedExpr> {
    let relevance_disabled = !min;
    let interactive_relevance = min && mitm;
    let mut eager_relevant_bits = None;
    let mut lazy_relevance = None;
    if relevance_disabled {
        info!(
            "exact-nullary setup relevance skipped in {:?} (--min=false)",
            Instant::now().elapsed()
        );
    } else if interactive_relevance {
        lazy_relevance = relevance::LazyRelevance::new(grammar, spec).map(|engine| (Instant::now(), engine));
        info!("exact-nullary setup relevance initialized lazily (--mitm)");
    } else {
        let relevance_start = Instant::now();
        eager_relevant_bits = relevance::compute_relevant_bits_for_spec(grammar, spec);
        info!(
            "exact-nullary setup relevance completed in {:?}",
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
    info!(
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
    let mut seen = if !relevance_disabled && !interactive_relevance {
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
    let mut relevance_credit = 0usize;

    for size in 1.. {
        let mut eval_attempted = 0usize;
        let mut eval_failed = 0usize;
        let mut pressure = RefinementPressure::default();
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
                        if let Some(value) = eval_cache
                            .leaves
                            .entry(expr.clone())
                            .or_insert_with(|| expr.eval(&[]).ok())
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
                                &mut pressure,
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
                            let value = deffun::ENV
                                .eval_defined(*fid, 1, std::slice::from_ref(&child.value))
                                .map_err(|_| ());
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
                                &mut pressure,
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
                                    let value = deffun::ENV
                                        .eval_defined(*fid, 2, &[lhs.value.clone(), rhs.value.clone()])
                                        .map_err(|_| ());
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
                                        &mut pressure,
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
                                    let Ok(value) = deffun::ENV
                                        .eval_defined(*fid, child_values.len(), &child_values)
                                        .map_err(|_| ())
                                    else {
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
                                &mut pressure,
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
                                        &mut pressure,
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
                                &mut pressure,
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
                            &mut pressure,
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
        relevance_credit = relevance_credit.saturating_add(pressure.credits());
        maybe_refine_lazy_relevance(
            grammar,
            &mut lazy_relevance,
            &mut seen,
            &by_size,
            &mut relevance_credit,
        );
    }

    unreachable!("nullary enumeration should either find a solution or diverge");
}

fn maybe_refine_lazy_relevance(
    grammar: &ExactGrammar<'_>,
    lazy_relevance: &mut Option<(Instant, relevance::LazyRelevance<'_>)>,
    seen: &mut SeenMode,
    by_size: &[Vec<Vec<Candidate>>],
    relevance_credit: &mut usize,
) {
    let Some((_start, engine)) = lazy_relevance.as_mut() else {
        return;
    };
    if *relevance_credit == 0 {
        return;
    }
    loop {
        if engine.advance(1) {
            break;
        }
        *relevance_credit = relevance_credit.saturating_sub(1);
        if *relevance_credit == 0 {
            return;
        }
    }
    *relevance_credit = 0;
    let (start, engine) = lazy_relevance.take().unwrap();
    let Some(relevant_bits) = engine.finish() else {
        info!(
            "exact-nullary setup relevance completed lazily in {:?} (no reduction)",
            start.elapsed()
        );
        return;
    };
    info!(
        "exact-nullary setup relevance completed lazily in {:?}",
        start.elapsed()
    );
    grammar.log_relevance_summary(&relevant_bits);
    *seen = build_projected_seen(by_size, &relevant_bits);
}

fn build_projected_seen(
    by_size: &[Vec<Vec<Candidate>>],
    relevant_bits: &[Vec<usize>],
) -> SeenMode {
    let mut maps = (0..by_size.len())
        .map(|_| FxHashMap::<ProjectionKey, usize>::default())
        .collect::<Vec<_>>();
    for (nt_idx, size_buckets) in by_size.iter().enumerate() {
        for (size, bucket) in size_buckets.iter().enumerate() {
            for candidate in bucket {
                let key = candidate.value.project(&relevant_bits[nt_idx]);
                maps[nt_idx].entry(key).or_insert(size);
            }
        }
    }
    SeenMode::Projected {
        relevant_bits: relevant_bits.to_vec(),
        maps,
    }
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
            info!("  nt[{}]: {}/{} bits relevant", i, bits.len(), nt_total);
        }
    }
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
    pressure: &mut RefinementPressure,
) -> Option<OwnedExpr> {
    if nt_idx == grammar.start && spec.matches(&candidate.value) {
        return materialize_node(candidate.node, grammar, nodes);
    }
    if seen_contains_or_insert(seen, nt_idx, &candidate.value, size, pressure) {
        return None;
    }
    by_size[nt_idx][size].push(candidate);
    pressure.inserted += 1;
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
    pressure: &mut RefinementPressure,
    build_node: impl FnOnce() -> Node,
) -> Option<OwnedExpr> {
    if nt_idx == grammar.start && spec.matches(&value) {
        let node = intern_node(nodes, build_node());
        return materialize_node(node, grammar, nodes);
    }
    if seen_contains_or_insert(seen, nt_idx, &value, size, pressure) {
        None
    } else {
        let node = intern_node(nodes, build_node());
        by_size[nt_idx][size].push(Candidate { node, value });
        pressure.inserted += 1;
        None
    }
}

fn seen_contains_or_insert(
    seen: &mut SeenMode,
    nt_idx: usize,
    value: &Value,
    size: usize,
    pressure: &mut RefinementPressure,
) -> bool {
    match seen {
        SeenMode::Exact(maps) => match maps[nt_idx].entry(value.clone()) {
            Entry::Occupied(_) => {
                pressure.collisions += 1;
                true
            }
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
                Entry::Occupied(_) => {
                    pressure.collisions += 1;
                    true
                }
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
