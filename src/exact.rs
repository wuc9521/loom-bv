use std::collections::hash_map::Entry;
use std::collections::BTreeMap;
use std::time::Instant;

mod eval;
mod grammar;
mod relevance;
mod spec;

use rustc_hash::FxHashMap;
use sygus_parser::ast::SyGuSFile;

use crate::{
    enumerate::{
        expr::OwnedExpr,
        grammar::{for_each_candidate_tuple, for_each_size_split, MultiConfig, TemplateExpr},
        value::Value,
    },
    info,
    parse::{self, SynthProblem},
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
                        .map(|v| v.is_zero())
                        .unwrap_or(false)
                })
            }
        }
    }
}

pub fn search_nullary(
    problem: &SynthProblem<'static>,
    spec: &NullarySpec,
) -> parse::Result<OwnedExpr> {
    let cfg_start = Instant::now();
    let multi = MultiConfig::from_problem(problem)?;
    info!(
        "exact-nullary setup multi-config completed in {:?}",
        cfg_start.elapsed()
    );
    let grammar_start = Instant::now();
    let grammar = grammar::compile_exact_grammar(&multi);
    info!(
        "exact-nullary setup exact-grammar completed in {:?}",
        grammar_start.elapsed()
    );
    search_nullary_multi_nt(&grammar, spec)
}

type NodeId = usize;

struct Node {
    nt_idx: usize,
    rule_idx: usize,
    children: Vec<NodeId>,
}

#[derive(Clone)]
struct ExactGrammar<'a> {
    nts: Vec<(&'a str, Vec<ExactRule>)>,
    start: usize,
}

#[derive(Clone)]
enum ExactRule {
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
struct ExactEvalCache {
    leaves: FxHashMap<OwnedExpr, Option<Value>>,
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
) -> parse::Result<OwnedExpr> {
    let relevance_start = Instant::now();
    let seen_relevant_bits = relevance::compute_relevant_bits_for_spec(grammar, spec);
    info!(
        "exact-nullary setup relevance completed in {:?}",
        relevance_start.elapsed()
    );
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
    let mut seen = match seen_relevant_bits {
        Some(relevant_bits) => SeenMode::Projected {
            maps: (0..nt_count).map(|_| FxHashMap::default()).collect(),
            relevant_bits,
        },
        None => SeenMode::Exact(vec![FxHashMap::<Value, usize>::default(); nt_count]),
    };
    if let SeenMode::Projected { relevant_bits, .. } = &seen {
        let total_kept = relevant_bits.iter().map(Vec::len).sum::<usize>();
        let total_full = grammar
            .nts
            .iter()
            .map(|(_, rules)| relevance::nt_output_bits(rules))
            .sum::<usize>();
        info!(
            "exact-nullary projected-seen nts={} kept_bits={} total_bits={}",
            relevant_bits.len(),
            total_kept,
            total_full
        );
    }
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
                            let value = eval::evaluate_fop1(*fid, &child.value);
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
                                    let value =
                                        eval::evaluate_fop2(*fid, &lhs.value, &rhs.value);
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
                                    let Ok(value) = eval::evaluate_fopn(*fid, &child_values) else {
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
                                    eval::evaluate_template_value(template, &[], &mut eval_cache)
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
                                    let Ok(value) = eval::evaluate_template_value(
                                        template,
                                        &child_values,
                                        &mut eval_cache,
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

fn insert_existing_candidate(
    nt_idx: usize,
    candidate: Candidate,
    size: usize,
    grammar: &ExactGrammar<'_>,
    spec: &NullarySpec,
    seen: &mut SeenMode,
    by_size: &mut [Vec<Vec<Candidate>>],
    nodes: &[Node],
) -> Option<OwnedExpr> {
    if nt_idx == grammar.start && spec.matches(&candidate.value) {
        return materialize_node(candidate.node, grammar, nodes);
    }
    if seen_contains_or_insert(seen, nt_idx, &candidate.value, size) {
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
    build_node: impl FnOnce() -> Node,
) -> Option<OwnedExpr> {
    if nt_idx == grammar.start && spec.matches(&value) {
        let node = intern_node(nodes, build_node());
        return materialize_node(node, grammar, nodes);
    }
    if seen_contains_or_insert(seen, nt_idx, &value, size) {
        None
    } else {
        let node = intern_node(nodes, build_node());
        by_size[nt_idx][size].push(Candidate { node, value });
        None
    }
}

fn seen_contains_or_insert(seen: &mut SeenMode, nt_idx: usize, value: &Value, size: usize) -> bool {
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
            let key = project_value(value, &relevant_bits[nt_idx]);
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

fn project_value(value: &Value, bits: &[usize]) -> ProjectionKey {
    ProjectionKey(value.project_bits(bits))
}

fn intern_node(nodes: &mut Vec<Node>, node: Node) -> NodeId {
    let id = nodes.len();
    nodes.push(node);
    id
}

fn materialize_node(id: NodeId, grammar: &ExactGrammar<'_>, nodes: &[Node]) -> Option<OwnedExpr> {
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
