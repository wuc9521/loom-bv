use std::cmp::Reverse;
use std::collections::hash_map::Entry;
use std::collections::BTreeMap;

use num_bigint::BigUint;
use num_traits::One;
use pest::Span;
use rustc_hash::FxHashMap;
use sygus_parser::ast::{Identifier, Literal as SyGuSLiteral, SyGuSCmd, SyGuSFile, SyGuSTerm};

use crate::{
    enumerate::{
        expr::OwnedExpr,
        grammar::{
            build_owned_application, for_each_candidate_tuple, for_each_size_split, MultiConfig,
            MultiRule, TemplateExpr,
        },
        value::Value,
    },
    info,
    parse::{
        self,
        deffun,
        new_custom_error_span,
        SynthProblem,
    },
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
        if let Some(value) = parse_target_define_fun(file, problem.name)? {
            return Ok(Some(Self::Exact(value)));
        }
        if let Some((known_bits, structural)) =
            parse_bit_constraints(file, problem.name, problem.bits)?
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
    let grammar = compile_exact_grammar(&MultiConfig::from_problem(problem)?);
    search_nullary_multi_nt(&grammar, spec, problem.bits)
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
    fop1: FxHashMap<(usize, Value), Option<Value>>,
    fop2: FxHashMap<(usize, Value, Value), Option<Value>>,
    fopn: FxHashMap<(usize, Vec<Value>), Option<Value>>,
}

#[derive(Clone)]
struct AbsValue {
    may_one: Value,
    may_zero: Value,
}

impl AbsValue {
    fn bits(&self) -> usize {
        self.may_one.bits()
    }

    fn top(bits: usize) -> Self {
        let ones = Value::from_biguint((BigUint::one() << bits) - BigUint::one(), bits);
        Self {
            may_one: ones.clone(),
            may_zero: ones,
        }
    }

    fn exact(value: &Value) -> Self {
        Self {
            may_one: value.clone(),
            may_zero: value.clone().bitnot(),
        }
    }

    fn can_be_zero(&self) -> bool {
        (0..self.bits()).all(|bit| self.may_zero.bit(bit))
    }

    fn is_forced_zero(&self) -> bool {
        self.can_be_zero() && (0..self.bits()).all(|bit| !self.may_one.bit(bit))
    }

    fn can_be_nonzero(&self) -> bool {
        (0..self.bits()).any(|bit| self.may_one.bit(bit))
    }

    fn union(self, other: Self) -> Self {
        Self {
            may_one: self.may_one.bitor(other.may_one),
            may_zero: self.may_zero.bitor(other.may_zero),
        }
    }
}

#[derive(Clone)]
struct GoalObligation {
    known_bits: Vec<(usize, bool)>,
    structural: Vec<OwnedExpr>,
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct ProjectionKey(Vec<u64>);

#[derive(Clone)]
struct BitDep {
    per_arg: Vec<Vec<usize>>,
}

enum SeenMode {
    Exact(Vec<FxHashMap<Value, usize>>),
    Projected {
        relevant_bits: Vec<Vec<usize>>,
        maps: Vec<FxHashMap<ProjectionKey, usize>>,
    },
}

impl SeenMode {
    fn bucket_len(&self, nt_idx: usize) -> usize {
        match self {
            SeenMode::Exact(maps) => maps[nt_idx].len(),
            SeenMode::Projected { maps, .. } => maps[nt_idx].len(),
        }
    }

    fn total_len(&self) -> usize {
        match self {
            SeenMode::Exact(maps) => maps.iter().map(FxHashMap::len).sum(),
            SeenMode::Projected { maps, .. } => maps.iter().map(FxHashMap::len).sum(),
        }
    }
}

#[derive(Clone)]
struct Candidate {
    node: NodeId,
    value: Value,
}

impl GoalObligation {
    fn from_spec(spec: &NullarySpec) -> Self {
        match spec {
            NullarySpec::Exact(expected) => Self {
                known_bits: (0..expected.bits())
                    .map(|bit| (bit, expected.bit(bit)))
                    .collect(),
                structural: Vec::new(),
            },
            NullarySpec::BitConstraints {
                known_bits,
                structural,
                ..
            } => Self {
                known_bits: known_bits.iter().map(|(bit, value)| (*bit, *value)).collect(),
                structural: structural.clone(),
            },
        }
    }

    fn score(&self, value: &Value) -> usize {
        let known_bit_score = self
            .known_bits
            .iter()
            .filter(|(bit, expected)| value.bit(*bit) == *expected)
            .count();
        let structural_score = self
            .structural
            .iter()
            .filter(|expr| {
                expr.eval(std::slice::from_ref(value))
                    .map(|v| v.is_zero())
                    .unwrap_or(false)
            })
            .count();
        known_bit_score + structural_score
    }

    fn abstract_rank(&self, abs: &AbsValue) -> Option<usize> {
        let mut forced = 0usize;
        for (bit, expected) in &self.known_bits {
            let possible = if *expected {
                abs.may_one.bit(*bit)
            } else {
                abs.may_zero.bit(*bit)
            };
            if !possible {
                return None;
            }
            let forced_ok = if *expected {
                abs.may_one.bit(*bit) && !abs.may_zero.bit(*bit)
            } else {
                abs.may_zero.bit(*bit) && !abs.may_one.bit(*bit)
            };
            if forced_ok {
                forced += 1;
            }
        }
        for expr in &self.structural {
            let expr_abs = eval_owned_abs(expr, std::slice::from_ref(abs), abs.bits(), 0);
            if !expr_abs.can_be_zero() {
                return None;
            }
            if expr_abs.is_forced_zero() {
                forced += 1;
            }
        }
        Some(forced)
    }
}

impl BitDep {
    fn empty(nargs: usize) -> Self {
        Self {
            per_arg: (0..nargs).map(|_| Vec::new()).collect(),
        }
    }

    fn single_slot(nargs: usize, arg_idx: usize, bit: usize) -> Self {
        let mut dep = Self::empty(nargs);
        dep.per_arg[arg_idx].push(bit);
        dep
    }

    fn union(&self, other: &Self) -> Self {
        let mut per_arg = Vec::with_capacity(self.per_arg.len());
        for (lhs, rhs) in self.per_arg.iter().zip(other.per_arg.iter()) {
            let mut merged = lhs.clone();
            for bit in rhs {
                if !merged.contains(bit) {
                    merged.push(*bit);
                }
            }
            merged.sort_unstable();
            per_arg.push(merged);
        }
        Self { per_arg }
    }
}

fn search_nullary_multi_nt(
    grammar: &ExactGrammar<'static>,
    spec: &NullarySpec,
    synth_bits: usize,
) -> parse::Result<OwnedExpr> {
    let goal = GoalObligation::from_spec(spec);
    let seen_relevant_bits = compute_relevant_bits_for_spec(grammar, spec);
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
            .map(|(_, rules)| nt_output_bits(rules))
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
    let mut goal_score_cache = FxHashMap::<Value, usize>::default();
    // Regression isolation: disable the abstract goal-ordering path and keep
    // the nullary solver on plain bottom-up exact enumeration order.
    let use_goal_ordering = false;
    let mut best_goal_score = 0usize;

    for size in 1.. {
        let mut inserted_this_size = 0usize;
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
                        if by_size[*child_nt]
                            .get(child_size)
                            .is_none_or(Vec::is_empty)
                        {
                            continue;
                        }
                            let mut children = by_size[*child_nt]
                                .get(child_size)
                                .map(Vec::as_slice)
                                .unwrap_or(&[][..])
                                .to_vec();
                        if use_goal_ordering {
                            filter_and_sort_unary_children(
                                *fid,
                                &mut children,
                                &goal,
                                synth_bits,
                            );
                        }
                        for child in &children {
                            eval_attempted += 1;
                            let value = evaluate_fop1(*fid, &child.value, &mut eval_cache);
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
                            if by_size[*lhs_nt]
                                .get(lhs_size)
                                .is_none_or(Vec::is_empty)
                                || by_size[*rhs_nt]
                                    .get(rhs_size)
                                    .is_none_or(Vec::is_empty)
                            {
                                continue;
                            }
                            let mut lhs_pool = by_size[*lhs_nt]
                                .get(lhs_size)
                                .map(Vec::as_slice)
                                .unwrap_or(&[][..])
                                .to_vec();
                            let mut rhs_pool = by_size[*rhs_nt]
                                .get(rhs_size)
                                .map(Vec::as_slice)
                                .unwrap_or(&[][..])
                                .to_vec();
                            if use_goal_ordering {
                                filter_and_sort_binary_children(
                                    *fid,
                                    0,
                                    &mut lhs_pool,
                                    &goal,
                                    synth_bits,
                                );
                                filter_and_sort_binary_children(
                                    *fid,
                                    1,
                                    &mut rhs_pool,
                                    &goal,
                                    synth_bits,
                                );
                            }
                            if lhs_pool.is_empty() || rhs_pool.is_empty() {
                                continue;
                            }
                            if use_goal_ordering {
                                for (lhs_idx, rhs_idx) in
                                    filter_and_rank_binary_pairs(
                                        *fid,
                                        &lhs_pool,
                                        &rhs_pool,
                                        &goal,
                                    )
                                {
                                    let lhs = &lhs_pool[lhs_idx];
                                    let rhs = &rhs_pool[rhs_idx];
                                    eval_attempted += 1;
                                    let value = evaluate_fop2(
                                        *fid,
                                        &lhs.value,
                                        &rhs.value,
                                        &mut eval_cache,
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
                                        || Node {
                                            nt_idx,
                                            rule_idx,
                                            children: vec![lhs.node, rhs.node],
                                        },
                                    ) {
                                        return Ok(found);
                                    }
                                }
                            } else {
                                for lhs in &lhs_pool {
                                    for rhs in &rhs_pool {
                                        eval_attempted += 1;
                                        let value = evaluate_fop2(
                                            *fid,
                                            &lhs.value,
                                            &rhs.value,
                                            &mut eval_cache,
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
                                    let Ok(value) =
                                        evaluate_fopn(*fid, &child_values, &mut eval_cache)
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
                        if use_goal_ordering {
                            staged.sort_by_key(|(value, _)| {
                                Reverse(cached_goal_score(value, &goal, &mut goal_score_cache))
                            });
                        }
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
                                    evaluate_template_value(template, &[], &mut eval_cache)
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
                                    let Ok(value) = evaluate_template_value(
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
                        if use_goal_ordering {
                            staged.sort_by_key(|(value, _)| {
                                Reverse(cached_goal_score(value, &goal, &mut goal_score_cache))
                            });
                        }
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

        for nt in 0..nt_count {
            inserted_this_size += by_size[nt][size].len();
            if nt == grammar.start && use_goal_ordering {
                for candidate in &by_size[nt][size] {
                    let score =
                        cached_goal_score(&candidate.value, &goal, &mut goal_score_cache);
                    if score > best_goal_score {
                        best_goal_score = score;
                    }
                }
            }
        }
        info!(
            "exact-nullary size={} inserted={} seen_start={} seen_total={} best_goal={}/{}",
            size,
            inserted_this_size,
            seen.bucket_len(grammar.start),
            seen.total_len(),
            best_goal_score,
            goal.known_bits.len()
        );
        info!(
            "exact-nullary eval size={} attempted={} failed={}",
            size,
            eval_attempted,
            eval_failed
        );
    }

    unreachable!("nullary enumeration should either find a solution or diverge");
}

fn cached_goal_score(
    value: &Value,
    goal: &GoalObligation,
    score_cache: &mut FxHashMap<Value, usize>,
) -> usize {
    if let Some(score) = score_cache.get(value) {
        return *score;
    }
    let score = goal.score(value);
    score_cache.insert(value.clone(), score);
    score
}

fn filter_and_sort_unary_children(
    fid: usize,
    children: &mut Vec<Candidate>,
    goal: &GoalObligation,
    synth_bits: usize,
) {
    let mut ranked = children
        .drain(..)
        .filter_map(|child| {
            let rank = rule_goal_rank(fid, &[Some(&child.value)], 1, goal, synth_bits)?;
            Some((rank, child))
        })
        .collect::<Vec<_>>();
    ranked.sort_by_key(|(rank, child)| (Reverse(*rank), Reverse(goal.score(&child.value))));
    children.extend(ranked.into_iter().map(|(_, child)| child));
}

fn filter_and_sort_binary_children(
    fid: usize,
    known_index: usize,
    children: &mut Vec<Candidate>,
    goal: &GoalObligation,
    synth_bits: usize,
) {
    let mut ranked = children
        .drain(..)
        .filter_map(|child| {
            let args = if known_index == 0 {
                [Some(&child.value), None]
            } else {
                [None, Some(&child.value)]
            };
            let rank = rule_goal_rank(fid, &args, 2, goal, synth_bits)?;
            Some((rank, child))
        })
        .collect::<Vec<_>>();
    ranked.sort_by_key(|(rank, child)| (Reverse(*rank), Reverse(goal.score(&child.value))));
    children.extend(ranked.into_iter().map(|(_, child)| child));
}

fn filter_and_rank_binary_pairs(
    fid: usize,
    lhs_pool: &[Candidate],
    rhs_pool: &[Candidate],
    goal: &GoalObligation,
) -> Vec<(usize, usize)> {
    let mut ranked = Vec::new();
    for (lhs_idx, lhs) in lhs_pool.iter().enumerate() {
        for (rhs_idx, rhs) in rhs_pool.iter().enumerate() {
            let Some(rank) = rule_goal_rank_exact(fid, &[&lhs.value, &rhs.value], 2, goal) else {
                continue;
            };
            ranked.push((
                rank,
                goal.score(&lhs.value) + goal.score(&rhs.value),
                lhs_idx,
                rhs_idx,
            ));
        }
    }
    ranked.sort_by_key(|(rank, child_score, lhs_idx, rhs_idx)| {
        (
            Reverse(*rank),
            Reverse(*child_score),
            *lhs_idx,
            *rhs_idx,
        )
    });
    ranked
        .into_iter()
        .map(|(_, _, lhs_idx, rhs_idx)| (lhs_idx, rhs_idx))
        .collect()
}

fn rule_goal_rank(
    fid: usize,
    known_args: &[Option<&Value>],
    nargs: usize,
    goal: &GoalObligation,
    default_bits: usize,
) -> Option<usize> {
    let arg_bits = deffun::ENV.arg_bits(fid, nargs);
    let abs_args = known_args
        .iter()
        .enumerate()
        .map(|(idx, arg)| {
            let bits = arg_bits.get(idx).copied().unwrap_or(default_bits);
            arg.map(AbsValue::exact)
                .unwrap_or_else(|| AbsValue::top(bits))
        })
        .collect::<Vec<_>>();
    let abs = eval_fop_abs(fid, nargs, &abs_args);
    goal.abstract_rank(&abs)
}

fn rule_goal_rank_exact(
    fid: usize,
    args: &[&Value],
    nargs: usize,
    goal: &GoalObligation,
) -> Option<usize> {
    let abs_args = args.iter().map(|arg| AbsValue::exact(arg)).collect::<Vec<_>>();
    let abs = eval_fop_abs(fid, nargs, &abs_args);
    goal.abstract_rank(&abs)
}

fn eval_fop_abs(fid: usize, nargs: usize, args: &[AbsValue]) -> AbsValue {
    let body = deffun::ENV.apply(fid, nargs);
    let fallback_bits = deffun::ENV.ret_bits(fid, nargs);
    eval_owned_abs(body, args, fallback_bits, 0)
}

fn eval_owned_abs(expr: &OwnedExpr, vars: &[AbsValue], fallback_bits: usize, depth: usize) -> AbsValue {
    if depth > 64 {
        return AbsValue::top(fallback_bits.max(1));
    }
    match expr {
        OwnedExpr::Var(i) => vars
            .get(*i)
            .cloned()
            .unwrap_or_else(|| AbsValue::top(fallback_bits.max(1))),
        OwnedExpr::Const(v) => AbsValue::exact(v),
        OwnedExpr::Not(a) | OwnedExpr::Neg(a) => {
            let child = eval_owned_abs(a, vars, fallback_bits, depth + 1);
            AbsValue {
                may_one: child.may_zero,
                may_zero: child.may_one,
            }
        }
        OwnedExpr::And(a, b) => {
            let lhs = eval_owned_abs(a, vars, fallback_bits, depth + 1);
            let rhs = eval_owned_abs(b, vars, fallback_bits, depth + 1);
            AbsValue {
                may_one: lhs.may_one.bitand(rhs.may_one),
                may_zero: lhs.may_zero.bitor(rhs.may_zero),
            }
        }
        OwnedExpr::Or(a, b) => {
            let lhs = eval_owned_abs(a, vars, fallback_bits, depth + 1);
            let rhs = eval_owned_abs(b, vars, fallback_bits, depth + 1);
            AbsValue {
                may_one: lhs.may_one.bitor(rhs.may_one),
                may_zero: lhs.may_zero.bitand(rhs.may_zero),
            }
        }
        OwnedExpr::Xor(a, b) => {
            let lhs = eval_owned_abs(a, vars, fallback_bits, depth + 1);
            let rhs = eval_owned_abs(b, vars, fallback_bits, depth + 1);
            let may_one = lhs
                .may_one
                .clone()
                .bitand(rhs.may_zero.clone())
                .bitor(lhs.may_zero.clone().bitand(rhs.may_one.clone()));
            let may_zero = lhs
                .may_one
                .bitand(rhs.may_one)
                .bitor(lhs.may_zero.bitand(rhs.may_zero));
            AbsValue { may_one, may_zero }
        }
        OwnedExpr::Concat(a, b) => {
            let lhs = eval_owned_abs(a, vars, fallback_bits, depth + 1);
            let rhs = eval_owned_abs(b, vars, fallback_bits, depth + 1);
            let rhs_bits = rhs.bits();
            AbsValue {
                may_one: concat_value(lhs.may_one, rhs.may_one, rhs_bits),
                may_zero: concat_value(lhs.may_zero, rhs.may_zero, rhs_bits),
            }
        }
        OwnedExpr::Extract(a, hi, lo) => {
            let child = eval_owned_abs(a, vars, fallback_bits, depth + 1);
            AbsValue {
                may_one: extract_value(child.may_one, *hi, *lo),
                may_zero: extract_value(child.may_zero, *hi, *lo),
            }
        }
        OwnedExpr::Ite(c, a, b) => {
            let cond = eval_owned_abs(c, vars, 1, depth + 1);
            let then_abs = eval_owned_abs(a, vars, fallback_bits, depth + 1);
            let else_abs = eval_owned_abs(b, vars, fallback_bits, depth + 1);
            let zero_branch = cond.can_be_zero().then_some(then_abs.clone());
            let nonzero_branch = cond.can_be_nonzero().then_some(else_abs.clone());
            match (zero_branch, nonzero_branch) {
                (Some(zero), Some(nonzero)) => zero.union(nonzero),
                (Some(zero), None) => zero,
                (None, Some(nonzero)) => nonzero,
                (None, None) => AbsValue::top(fallback_bits.max(1)),
            }
        }
        OwnedExpr::Fop0Dyn(id) => eval_fop_abs(*id, 0, &[]),
        OwnedExpr::Fop1Dyn(id, a) => {
            let child = eval_owned_abs(a, vars, fallback_bits, depth + 1);
            eval_fop_abs(*id, 1, &[child])
        }
        OwnedExpr::Fop2Dyn(id, a, b) => {
            let lhs = eval_owned_abs(a, vars, fallback_bits, depth + 1);
            let rhs = eval_owned_abs(b, vars, fallback_bits, depth + 1);
            eval_fop_abs(*id, 2, &[lhs, rhs])
        }
        OwnedExpr::FopDyn(id, args) => {
            let args = args
                .iter()
                .map(|arg| eval_owned_abs(arg, vars, fallback_bits, depth + 1))
                .collect::<Vec<_>>();
            eval_fop_abs(*id, args.len(), &args)
        }
        _ => AbsValue::top(owned_expr_width(expr).max(fallback_bits).max(1)),
    }
}

fn owned_expr_width(expr: &OwnedExpr) -> usize {
    match expr {
        OwnedExpr::Concat(a, b) => owned_expr_width(a) + owned_expr_width(b),
        OwnedExpr::Extract(_, hi, lo) => (hi - lo + 1) as usize,
        OwnedExpr::Fop0Dyn(id) => deffun::ENV.ret_bits(*id, 0),
        OwnedExpr::FopDyn(id, args) => deffun::ENV.ret_bits(*id, args.len()),
        OwnedExpr::Const(v) => v.bits(),
        OwnedExpr::Var(_) => 64,
        OwnedExpr::Not(a) | OwnedExpr::Neg(a) | OwnedExpr::Fop1Dyn(_, a) => owned_expr_width(a),
        OwnedExpr::Add(a, _)
        | OwnedExpr::Xor(a, _)
        | OwnedExpr::And(a, _)
        | OwnedExpr::Or(a, _)
        | OwnedExpr::Mul(a, _)
        | OwnedExpr::Sub(a, _)
        | OwnedExpr::Fop2Dyn(_, a, _)
        | OwnedExpr::LShr(a, _)
        | OwnedExpr::AShr(a, _)
        | OwnedExpr::Shl(a, _)
        | OwnedExpr::UDiv(a, _)
        | OwnedExpr::URem(a, _)
        | OwnedExpr::SDiv(a, _)
        | OwnedExpr::SRem(a, _) => owned_expr_width(a),
        OwnedExpr::Ite(_, a, _) => owned_expr_width(a),
    }
}

fn extract_value(value: Value, hi: u64, lo: u64) -> Value {
    let width = (hi - lo + 1) as usize;
    let shifted = value.to_biguint() >> (lo as usize);
    let mask = (BigUint::one() << width) - BigUint::one();
    Value::from_biguint(shifted & mask, width)
}

fn concat_value(lhs: Value, rhs: Value, rhs_bits: usize) -> Value {
    let total_bits = lhs.bits() + rhs_bits;
    let raw = (lhs.to_biguint() << rhs_bits) | rhs.to_biguint();
    Value::from_biguint(raw, total_bits)
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
    let mut words = Vec::with_capacity(bits.len().div_ceil(64));
    let mut current = 0u64;
    for (idx, bit) in bits.iter().enumerate() {
        if value.bit(*bit) {
            current |= 1u64 << (idx % 64);
        }
        if idx % 64 == 63 {
            words.push(current);
            current = 0;
        }
    }
    if !bits.len().is_multiple_of(64) {
        words.push(current);
    }
    ProjectionKey(words)
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

fn compile_exact_grammar(grammar: &MultiConfig<'static>) -> ExactGrammar<'static> {
    let nts = grammar
        .nts
        .iter()
        .map(|(name, rules)| {
            let compiled = rules
                .iter()
                .map(|rule| match rule {
                    MultiRule::Alias(nt) => ExactRule::Alias(*nt),
                    MultiRule::Template {
                        template,
                        child_nts,
                        base_size,
                        ..
                    } => compile_exact_rule(template, child_nts, *base_size),
                })
                .collect();
            (*name, compiled)
        })
        .collect();
    ExactGrammar {
        nts,
        start: grammar.start,
    }
}

fn compute_relevant_bits_for_spec(
    grammar: &ExactGrammar<'_>,
    spec: &NullarySpec,
) -> Option<Vec<Vec<usize>>> {
    let NullarySpec::BitConstraints {
        bits,
        known_bits,
        structural,
    } = spec
    else {
        return None;
    };
    if !structural.is_empty() {
        return None;
    }
    if known_bits.is_empty() {
        return None;
    }
    let nt_bits = grammar
        .nts
        .iter()
        .map(|(_, rules)| nt_output_bits(rules))
        .collect::<Vec<_>>();
    if nt_bits.get(grammar.start).copied() != Some(*bits) {
        return None;
    }
    let mut dep_cache = FxHashMap::<(usize, usize), Option<Vec<BitDep>>>::default();
    let mut relevant = nt_bits
        .iter()
        .map(|bits| vec![false; *bits])
        .collect::<Vec<_>>();
    for bit in known_bits.keys() {
        if *bit < relevant[grammar.start].len() {
            relevant[grammar.start][*bit] = true;
        }
    }
    let mut changed = true;
    while changed {
        changed = false;
        for (nt_idx, (_, rules)) in grammar.nts.iter().enumerate() {
            let parent_relevant = relevant[nt_idx]
                .iter()
                .enumerate()
                .filter_map(|(bit, is_rel)| is_rel.then_some(bit))
                .collect::<Vec<_>>();
            if parent_relevant.is_empty() {
                continue;
            }
            for rule in rules {
                match rule {
                    ExactRule::Alias(child_nt) => {
                        for bit in &parent_relevant {
                            if *bit < relevant[*child_nt].len() && !relevant[*child_nt][*bit] {
                                relevant[*child_nt][*bit] = true;
                                changed = true;
                            }
                        }
                    }
                    ExactRule::Leaf(_) => {}
                    ExactRule::Unary { fid, child_nt } => {
                        let Some(summary) =
                            get_deffun_dep_summary(*fid, 1, &mut dep_cache)
                        else {
                            return None;
                        };
                        propagate_relevant_bits(
                            &parent_relevant,
                            &summary,
                            0,
                            &mut relevant[*child_nt],
                            &mut changed,
                        );
                    }
                    ExactRule::Binary {
                        fid,
                        lhs_nt,
                        rhs_nt,
                    } => {
                        let Some(summary) =
                            get_deffun_dep_summary(*fid, 2, &mut dep_cache)
                        else {
                            return None;
                        };
                        propagate_relevant_bits(
                            &parent_relevant,
                            &summary,
                            0,
                            &mut relevant[*lhs_nt],
                            &mut changed,
                        );
                        propagate_relevant_bits(
                            &parent_relevant,
                            &summary,
                            1,
                            &mut relevant[*rhs_nt],
                            &mut changed,
                        );
                    }
                    ExactRule::Nary { fid, child_nts } => {
                        let Some(summary) =
                            get_deffun_dep_summary(*fid, child_nts.len(), &mut dep_cache)
                        else {
                            return None;
                        };
                        for (arg_idx, child_nt) in child_nts.iter().enumerate() {
                            propagate_relevant_bits(
                                &parent_relevant,
                                &summary,
                                arg_idx,
                                &mut relevant[*child_nt],
                                &mut changed,
                            );
                        }
                    }
                    ExactRule::GenericTemplate { template, child_nts, .. } => {
                        let Some(summary) = get_template_dep_summary(
                            template,
                            &child_nts
                                .iter()
                                .map(|child_nt| nt_bits[*child_nt])
                                .collect::<Vec<_>>(),
                            &mut dep_cache,
                        ) else {
                            return None;
                        };
                        for (arg_idx, child_nt) in child_nts.iter().enumerate() {
                            propagate_relevant_bits(
                                &parent_relevant,
                                &summary,
                                arg_idx,
                                &mut relevant[*child_nt],
                                &mut changed,
                            );
                        }
                    }
                }
            }
        }
    }
    let relevant_bits = relevant
        .into_iter()
        .map(|bits| {
            bits.into_iter()
                .enumerate()
                .filter_map(|(idx, relevant)| relevant.then_some(idx))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let reduced_any = relevant_bits
        .iter()
        .zip(nt_bits.iter())
        .any(|(rel, bits)| rel.len() < *bits);
    reduced_any.then_some(relevant_bits)
}

fn propagate_relevant_bits(
    parent_relevant: &[usize],
    summary: &[BitDep],
    arg_idx: usize,
    child_relevant: &mut [bool],
    changed: &mut bool,
) {
    for bit in parent_relevant {
        let Some(dep) = summary.get(*bit) else {
            continue;
        };
        let Some(arg_deps) = dep.per_arg.get(arg_idx) else {
            continue;
        };
        for child_bit in arg_deps {
            if *child_bit < child_relevant.len() && !child_relevant[*child_bit] {
                child_relevant[*child_bit] = true;
                *changed = true;
            }
        }
    }
}

fn nt_output_bits(rules: &[ExactRule]) -> usize {
    for rule in rules {
        match rule {
            ExactRule::Alias(_) => {}
            ExactRule::Leaf(expr) => return owned_expr_width(expr),
            ExactRule::Unary { fid, .. } => return deffun::ENV.ret_bits(*fid, 1),
            ExactRule::Binary { fid, .. } => return deffun::ENV.ret_bits(*fid, 2),
            ExactRule::Nary { fid, child_nts } => return deffun::ENV.ret_bits(*fid, child_nts.len()),
            ExactRule::GenericTemplate { template, .. } => {
                return template_output_bits(template)
            }
        }
    }
    1
}

fn template_output_bits(template: &TemplateExpr) -> usize {
    match template {
        TemplateExpr::Slot(_) => 1,
        TemplateExpr::Leaf(expr) => owned_expr_width(expr),
        TemplateExpr::App(id, parts) => deffun::ENV
            .lookup(id.get_name(), parts.len())
            .map(|fid| deffun::ENV.ret_bits(fid, parts.len()))
            .unwrap_or(1),
    }
}

fn get_deffun_dep_summary(
    fid: usize,
    nargs: usize,
    cache: &mut FxHashMap<(usize, usize), Option<Vec<BitDep>>>,
) -> Option<Vec<BitDep>> {
    if let Some(summary) = cache.get(&(fid, nargs)) {
        return summary.clone();
    }
    let arg_bits = deffun::ENV.arg_bits(fid, nargs).to_vec();
    let summary = compute_expr_dep_summary(deffun::ENV.apply(fid, nargs), &arg_bits, cache);
    cache.insert((fid, nargs), summary.clone());
    summary
}

fn get_template_dep_summary(
    template: &TemplateExpr,
    slot_bits: &[usize],
    cache: &mut FxHashMap<(usize, usize), Option<Vec<BitDep>>>,
) -> Option<Vec<BitDep>> {
    compute_template_dep_summary(template, slot_bits, cache)
}

fn compute_template_dep_summary(
    template: &TemplateExpr,
    slot_bits: &[usize],
    cache: &mut FxHashMap<(usize, usize), Option<Vec<BitDep>>>,
) -> Option<Vec<BitDep>> {
    match template {
        TemplateExpr::Slot(slot) => {
            let bits = *slot_bits.get(*slot)?;
            Some(
                (0..bits)
                    .map(|bit| BitDep::single_slot(slot_bits.len(), *slot, bit))
                    .collect(),
            )
        }
        TemplateExpr::Leaf(expr) => compute_expr_dep_summary(expr, slot_bits, cache),
        TemplateExpr::App(id, parts) => {
            let fid = deffun::ENV.lookup(id.get_name(), parts.len())?;
            let f_summary = get_deffun_dep_summary(fid, parts.len(), cache)?;
            let part_summaries = parts
                .iter()
                .map(|part| compute_template_dep_summary(part, slot_bits, cache))
                .collect::<Option<Vec<_>>>()?;
            compose_dep_summaries(&f_summary, &part_summaries, slot_bits.len())
        }
    }
}

fn compute_expr_dep_summary(
    expr: &OwnedExpr,
    arg_bits: &[usize],
    cache: &mut FxHashMap<(usize, usize), Option<Vec<BitDep>>>,
) -> Option<Vec<BitDep>> {
    match expr {
        OwnedExpr::Const(value) => Some((0..value.bits()).map(|_| BitDep::empty(arg_bits.len())).collect()),
        OwnedExpr::Var(idx) => {
            let bits = *arg_bits.get(*idx)?;
            Some(
                (0..bits)
                    .map(|bit| BitDep::single_slot(arg_bits.len(), *idx, bit))
                    .collect(),
            )
        }
        OwnedExpr::Extract(inner, hi, lo) => {
            let deps = compute_expr_dep_summary(inner, arg_bits, cache)?;
            Some(deps.get(*lo as usize..=*hi as usize)?.to_vec())
        }
        OwnedExpr::Concat(high, low) => {
            let mut res = compute_expr_dep_summary(low, arg_bits, cache)?;
            res.extend(compute_expr_dep_summary(high, arg_bits, cache)?);
            Some(res)
        }
        OwnedExpr::Not(inner) | OwnedExpr::Neg(inner) => compute_expr_dep_summary(inner, arg_bits, cache),
        OwnedExpr::And(lhs, rhs)
        | OwnedExpr::Or(lhs, rhs)
        | OwnedExpr::Xor(lhs, rhs) => {
            let lhs_deps = compute_expr_dep_summary(lhs, arg_bits, cache)?;
            let rhs_deps = compute_expr_dep_summary(rhs, arg_bits, cache)?;
            union_pointwise_deps(&lhs_deps, &rhs_deps)
        }
        OwnedExpr::Ite(cond, then_expr, else_expr) => {
            let cond_deps = compute_expr_dep_summary(cond, arg_bits, cache)?;
            if cond_deps.len() != 1 {
                return None;
            }
            let then_deps = compute_expr_dep_summary(then_expr, arg_bits, cache)?;
            let else_deps = compute_expr_dep_summary(else_expr, arg_bits, cache)?;
            if then_deps.len() != else_deps.len() {
                return None;
            }
            Some(
                then_deps
                    .into_iter()
                    .zip(else_deps)
                    .map(|(a, b)| a.union(&b).union(&cond_deps[0]))
                    .collect(),
            )
        }
        OwnedExpr::Fop0Dyn(fid) => get_deffun_dep_summary(*fid, 0, cache),
        OwnedExpr::Fop1Dyn(fid, arg) => {
            let f_summary = get_deffun_dep_summary(*fid, 1, cache)?;
            let arg_summary = compute_expr_dep_summary(arg, arg_bits, cache)?;
            compose_dep_summaries(&f_summary, &[arg_summary], arg_bits.len())
        }
        OwnedExpr::Fop2Dyn(fid, lhs, rhs) => {
            let f_summary = get_deffun_dep_summary(*fid, 2, cache)?;
            let lhs_summary = compute_expr_dep_summary(lhs, arg_bits, cache)?;
            let rhs_summary = compute_expr_dep_summary(rhs, arg_bits, cache)?;
            compose_dep_summaries(&f_summary, &[lhs_summary, rhs_summary], arg_bits.len())
        }
        OwnedExpr::FopDyn(fid, args) => {
            let f_summary = get_deffun_dep_summary(*fid, args.len(), cache)?;
            let arg_summaries = args
                .iter()
                .map(|arg| compute_expr_dep_summary(arg, arg_bits, cache))
                .collect::<Option<Vec<_>>>()?;
            compose_dep_summaries(&f_summary, &arg_summaries, arg_bits.len())
        }
        other => Some(top_dep_summary(owned_expr_width(other), arg_bits)),
    }
}

fn union_pointwise_deps(lhs: &[BitDep], rhs: &[BitDep]) -> Option<Vec<BitDep>> {
    if lhs.len() != rhs.len() {
        return None;
    }
    Some(
        lhs.iter()
            .zip(rhs.iter())
            .map(|(a, b)| a.union(b))
            .collect(),
    )
}

fn compose_dep_summaries(
    outer: &[BitDep],
    inner: &[Vec<BitDep>],
    nargs: usize,
) -> Option<Vec<BitDep>> {
    let mut result = Vec::with_capacity(outer.len());
    for out_dep in outer {
        let mut combined = BitDep::empty(nargs);
        for (arg_idx, bits) in out_dep.per_arg.iter().enumerate() {
            let arg_summary = inner.get(arg_idx)?;
            for bit in bits {
                let bit_dep = arg_summary.get(*bit)?;
                combined = combined.union(bit_dep);
            }
        }
        result.push(combined);
    }
    Some(result)
}

fn top_dep_summary(width: usize, arg_bits: &[usize]) -> Vec<BitDep> {
    let full = BitDep {
        per_arg: arg_bits
            .iter()
            .map(|bits| (0..*bits).collect::<Vec<_>>())
            .collect(),
    };
    (0..width).map(|_| full.clone()).collect()
}

fn compile_exact_rule(template: &TemplateExpr, child_nts: &[usize], base_size: usize) -> ExactRule {
    if child_nts.is_empty() {
        if let TemplateExpr::Leaf(expr) = template {
            return ExactRule::Leaf(expr.clone());
        }
    }
    let TemplateExpr::App(id, parts) = template else {
        return ExactRule::GenericTemplate {
            template: template.clone(),
            child_nts: child_nts.to_vec(),
            base_size,
        };
    };
    if parts.len() != child_nts.len() {
        return ExactRule::GenericTemplate {
            template: template.clone(),
            child_nts: child_nts.to_vec(),
            base_size,
        };
    }
    if !parts
        .iter()
        .enumerate()
        .all(|(idx, part)| matches!(part, TemplateExpr::Slot(slot) if *slot == idx))
    {
        return ExactRule::GenericTemplate {
            template: template.clone(),
            child_nts: child_nts.to_vec(),
            base_size,
        };
    }
    let Some(fid) = deffun::ENV.lookup(id.get_name(), parts.len()) else {
        return ExactRule::GenericTemplate {
            template: template.clone(),
            child_nts: child_nts.to_vec(),
            base_size,
        };
    };
    match parts.len() {
        1 => ExactRule::Unary {
            fid,
            child_nt: child_nts[0],
        },
        2 => ExactRule::Binary {
            fid,
            lhs_nt: child_nts[0],
            rhs_nt: child_nts[1],
        },
        _ => ExactRule::Nary {
            fid,
            child_nts: child_nts.to_vec(),
        },
    }
}

fn evaluate_template_value(
    template: &TemplateExpr,
    args: &[Value],
    cache: &mut ExactEvalCache,
) -> Result<Value, ()> {
    match template {
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
                .map(|part| evaluate_template_value(part, args, cache))
                .collect::<Result<Vec<_>, _>>()?;
            let const_args = values
                .iter()
                .cloned()
                .map(OwnedExpr::Const)
                .collect::<Vec<_>>();
            build_owned_application(id, &const_args)
                .ok()
                .and_then(|expr| expr.eval(&[]).ok())
                .ok_or(())
        }
    }
}

fn evaluate_fop1(fid: usize, arg: &Value, cache: &mut ExactEvalCache) -> Result<Value, ()> {
    cache
        .fop1
        .entry((fid, arg.clone()))
        .or_insert_with(|| {
            deffun::ENV
                .apply(fid, 1)
                .eval(std::slice::from_ref(arg))
                .ok()
        })
        .clone()
        .ok_or(())
}

fn evaluate_fop2(
    fid: usize,
    lhs: &Value,
    rhs: &Value,
    cache: &mut ExactEvalCache,
) -> Result<Value, ()> {
    let args = [lhs.clone(), rhs.clone()];
    cache
        .fop2
        .entry((fid, lhs.clone(), rhs.clone()))
        .or_insert_with(|| deffun::ENV.apply(fid, 2).eval(&args).ok())
        .clone()
        .ok_or(())
}

fn evaluate_fopn(fid: usize, args: &[Value], cache: &mut ExactEvalCache) -> Result<Value, ()> {
    cache
        .fopn
        .entry((fid, args.to_vec()))
        .or_insert_with(|| deffun::ENV.apply(fid, args.len()).eval(args).ok())
        .clone()
        .ok_or(())
}

fn parse_target_define_fun(file: &SyGuSFile, target_name: &str) -> parse::Result<Option<Value>> {
    for cmd in &file.cmds {
        if let SyGuSCmd::DefineFun(name, args, _, body) = cmd {
            if name == target_name && args.is_empty() {
                let expr = OwnedExpr::from_term(body, &[])?;
                let value = expr.eval(&[]).map_err(|_| {
                    new_custom_error_span(
                        format!("failed to evaluate nullary define-fun {}", target_name),
                        empty_span(),
                    )
                })?;
                return Ok(Some(value));
            }
        }
    }
    Ok(None)
}

fn constraint_mentions_target(term: &SyGuSTerm, target_name: &str) -> bool {
    match term {
        SyGuSTerm::Identifier(id) => id.get_name() == target_name,
        SyGuSTerm::Annotated(inner, _) => constraint_mentions_target(inner, target_name),
        SyGuSTerm::Application(_, args) => args
            .iter()
            .any(|a| constraint_mentions_target(a, target_name)),
        SyGuSTerm::Let(bindings, body) => {
            bindings
                .iter()
                .any(|b| constraint_mentions_target(&b.term, target_name))
                || constraint_mentions_target(body, target_name)
        }
        SyGuSTerm::Forall(_, body) | SyGuSTerm::Exists(_, body) => {
            constraint_mentions_target(body, target_name)
        }
        _ => false,
    }
}

fn validate_structural_shape(term: &SyGuSTerm, target: &str) -> parse::Result<()> {
    match term {
        SyGuSTerm::Annotated(inner, _) => validate_structural_shape(inner, target),
        SyGuSTerm::Literal(SyGuSLiteral::Bool(_)) => Ok(()),
        SyGuSTerm::Literal(SyGuSLiteral::Numeral(n)) if *n == 0 || *n == 1 => Ok(()),
        SyGuSTerm::Literal(SyGuSLiteral::BinConst(s)) => {
            let bits: String = s.chars().filter(|c| *c == '0' || *c == '1').collect();
            if bits.is_empty() {
                Err(new_custom_error_span(
                    "structural constraints: expected #b... bitvector literal".into(),
                    empty_span(),
                ))
            } else {
                Ok(())
            }
        }
        SyGuSTerm::Literal(_) => Err(new_custom_error_span(
            "structural constraints: unsupported literal".into(),
            empty_span(),
        )),
        SyGuSTerm::Identifier(id) => {
            let n = id.get_name();
            if n == target || n.eq_ignore_ascii_case("true") || n.eq_ignore_ascii_case("false") {
                Ok(())
            } else {
                Err(new_custom_error_span(
                    format!("structural constraints: unsupported identifier `{n}`"),
                    empty_span(),
                ))
            }
        }
        SyGuSTerm::Application(id, args) => match id.get_name() {
            "not" if args.len() == 1 => validate_structural_shape(&args[0], target),
            "and" | "or" => args
                .iter()
                .try_for_each(|a| validate_structural_shape(a, target)),
            "=" if args.len() == 2 => {
                validate_structural_shape(&args[0], target)?;
                validate_structural_shape(&args[1], target)?;
                Ok(())
            }
            _ if extract_on_phi_range(term, target).is_some() => Ok(()),
            _ => Err(new_custom_error_span(
                format!(
                    "structural constraints: unsupported operator `{}`",
                    id.get_name()
                ),
                empty_span(),
            )),
        },
        _ => Err(new_custom_error_span(
            "structural constraints: unsupported SyGuS term shape".into(),
            empty_span(),
        )),
    }
}

/// Map SyGuS boolean constants to the 1-bit encoding used by [`OwnedExpr::from_term`]
/// (`and` / `or` / `not` / `ite`): zero means true, non-zero means false.
fn rewrite_constraint_literals_for_owned_eval(term: &SyGuSTerm) -> SyGuSTerm {
    fn xor_b0_b0() -> SyGuSTerm {
        SyGuSTerm::Application(
            Identifier::Symbol("xor".into()),
            vec![
                SyGuSTerm::Literal(SyGuSLiteral::BinConst("0".into())),
                SyGuSTerm::Literal(SyGuSLiteral::BinConst("0".into())),
            ],
        )
    }
    fn xor_b0_b1() -> SyGuSTerm {
        SyGuSTerm::Application(
            Identifier::Symbol("xor".into()),
            vec![
                SyGuSTerm::Literal(SyGuSLiteral::BinConst("0".into())),
                SyGuSTerm::Literal(SyGuSLiteral::BinConst("1".into())),
            ],
        )
    }
    match term {
        SyGuSTerm::Identifier(id) if id.get_name().eq_ignore_ascii_case("true") => xor_b0_b0(),
        SyGuSTerm::Identifier(id) if id.get_name().eq_ignore_ascii_case("false") => xor_b0_b1(),
        SyGuSTerm::Literal(SyGuSLiteral::Bool(true)) => xor_b0_b0(),
        SyGuSTerm::Literal(SyGuSLiteral::Bool(false)) => xor_b0_b1(),
        SyGuSTerm::Literal(SyGuSLiteral::Numeral(0)) => xor_b0_b1(),
        SyGuSTerm::Literal(SyGuSLiteral::Numeral(1)) => xor_b0_b0(),
        SyGuSTerm::Annotated(inner, attrs) => SyGuSTerm::Annotated(
            Box::new(rewrite_constraint_literals_for_owned_eval(inner)),
            attrs.clone(),
        ),
        SyGuSTerm::Application(id, args) => SyGuSTerm::Application(
            id.clone(),
            args.iter()
                .map(rewrite_constraint_literals_for_owned_eval)
                .collect(),
        ),
        SyGuSTerm::Exists(_, _) | SyGuSTerm::Forall(_, _) | SyGuSTerm::Let(_, _) => term.clone(),
        _ => term.clone(),
    }
}

fn index_numeral(idx: &sygus_parser::ast::Index) -> Option<usize> {
    match idx {
        sygus_parser::ast::Index::Numeral(v) => Some(*v),
        sygus_parser::ast::Index::Symbol(_) => None,
    }
}

fn extract_indices_from_identifier(id: &Identifier) -> Option<(usize, usize)> {
    match id {
        Identifier::Indexed(sym, idxs) if sym == "extract" && idxs.len() >= 2 => {
            match (index_numeral(&idxs[0]), index_numeral(&idxs[1])) {
                (Some(hi), Some(lo)) => Some((hi, lo)),
                _ => None,
            }
        }
        Identifier::Indexed(sym, idxs) if sym == "_" && idxs.len() >= 3 => {
            match (&idxs[0], index_numeral(&idxs[1]), index_numeral(&idxs[2])) {
                (sygus_parser::ast::Index::Symbol(op), Some(hi), Some(lo)) if op == "extract" => {
                    Some((hi, lo))
                }
                _ => None,
            }
        }
        _ => None,
    }
    .or_else(|| {
        let text = id.to_string();
        let parts = text
            .trim_matches(|c| c == '(' || c == ')')
            .split_whitespace()
            .collect::<Vec<_>>();
        match parts.as_slice() {
            ["_", "extract", hi, lo] => match (hi.parse::<usize>(), lo.parse::<usize>()) {
                (Ok(hi), Ok(lo)) => Some((hi, lo)),
                _ => None,
            },
            ["extract", hi, lo] => match (hi.parse::<usize>(), lo.parse::<usize>()) {
                (Ok(hi), Ok(lo)) => Some((hi, lo)),
                _ => None,
            },
            _ => None,
        }
    })
}

fn extract_on_phi_range(term: &SyGuSTerm, target: &str) -> Option<(usize, usize)> {
    match term {
        SyGuSTerm::Annotated(inner, _) => extract_on_phi_range(inner, target),
        SyGuSTerm::Application(id, args) if args.len() == 1 => {
            if !matches!(&args[0], SyGuSTerm::Identifier(var) if var.get_name() == target) {
                return None;
            }
            extract_indices_from_identifier(id)
        }
        _ => None,
    }
}

fn parse_bit_constraints(
    file: &SyGuSFile,
    target_name: &str,
    target_bits: usize,
) -> parse::Result<Option<(BTreeMap<usize, bool>, Vec<OwnedExpr>)>> {
    let mut known_bits = BTreeMap::<usize, bool>::new();
    let mut structural = Vec::new();
    let synth_env = [(target_name, target_bits as u64)];
    let mut found_any = false;

    for cmd in &file.cmds {
        if let SyGuSCmd::Constraint(c) = cmd {
            if let Some((bit, value)) = parse_bit_constraint(c, target_name) {
                if bit >= target_bits {
                    continue;
                }
                found_any = true;
                if let Some(old) = known_bits.get(&bit).copied() {
                    if old != value {
                        return Err(new_custom_error_span(
                            format!("Conflicting constraints on bit {} of {}", bit, target_name),
                            empty_span(),
                        ));
                    }
                } else {
                    known_bits.insert(bit, value);
                }
            } else if constraint_mentions_target(c, target_name) {
                validate_structural_shape(c, target_name)?;
                let rewritten = rewrite_constraint_literals_for_owned_eval(c);
                structural.push(OwnedExpr::from_term(&rewritten, &synth_env)?);
                found_any = true;
            }
        } else if let SyGuSCmd::Assume(c) = cmd {
            if constraint_mentions_target(c, target_name) {
                validate_structural_shape(c, target_name)?;
                let rewritten = rewrite_constraint_literals_for_owned_eval(c);
                structural.push(OwnedExpr::from_term(&rewritten, &synth_env)?);
                found_any = true;
            }
        }
    }

    Ok(found_any.then_some((known_bits, structural)))
}

fn parse_bit_constraint(term: &SyGuSTerm, target_name: &str) -> Option<(usize, bool)> {
    if let SyGuSTerm::Annotated(inner, _) = term {
        return parse_bit_constraint(inner, target_name);
    }
    let SyGuSTerm::Application(eq, args) = term else {
        return None;
    };
    if eq.get_name() != "=" || args.len() != 2 {
        return None;
    }
    extract_bit_of_target(&args[0], target_name)
        .zip(bit_literal(&args[1]))
        .or_else(|| extract_bit_of_target(&args[1], target_name).zip(bit_literal(&args[0])))
}

fn bit_literal(term: &SyGuSTerm) -> Option<bool> {
    match term {
        SyGuSTerm::Annotated(inner, _) => bit_literal(inner),
        SyGuSTerm::Identifier(id) => {
            let name = id.get_name();
            if name.eq_ignore_ascii_case("true") {
                Some(true)
            } else if name.eq_ignore_ascii_case("false") {
                Some(false)
            } else {
                let bits: String = name.chars().filter(|c| *c == '0' || *c == '1').collect();
                if bits.is_empty() {
                    None
                } else {
                    Some(bits.chars().last().unwrap() == '1')
                }
            }
        }
        SyGuSTerm::Literal(SyGuSLiteral::Bool(v)) => Some(*v),
        SyGuSTerm::Literal(SyGuSLiteral::Numeral(v)) => match *v {
            0 => Some(false),
            1 => Some(true),
            _ => None,
        },
        SyGuSTerm::Literal(SyGuSLiteral::BinConst(v)) => {
            let bits: String = v.chars().filter(|c| *c == '0' || *c == '1').collect();
            if bits.is_empty() {
                None
            } else {
                Some(bits.chars().last().unwrap() == '1')
            }
        }
        _ => None,
    }
}

fn extract_bit_of_target(term: &SyGuSTerm, target_name: &str) -> Option<usize> {
    let (hi, lo) = extract_on_phi_range(term, target_name)?;
    (hi == lo).then_some(hi)
}

fn empty_span() -> Span<'static> {
    Span::new("", 0, 0).expect("empty span should be valid")
}

#[cfg(test)]
mod tests {
    use super::{search_nullary, NullarySpec};
    use crate::parse::{deffun, SynthProblem};
    use sygus_parser::ast::SyGuSFile;

    #[test]
    fn recursive_nullary_search_finds_non_leaf_solution() {
        let file = SyGuSFile::from_str(
            r#"
(set-logic BV)
(define-fun c1 () (_ BitVec 2) #b01)
(define-fun c2 () (_ BitVec 2) #b10)
(define-fun both ((x (_ BitVec 2)) (y (_ BitVec 2))) (_ BitVec 2) (bvor x y))
(synth-fun f () (_ BitVec 2)
  ((Start (_ BitVec 2)))
  ((Start (_ BitVec 2) (c1 c2 (both Start Start)))))
(constraint (= ((_ extract 0 0) f) #b1))
(constraint (= ((_ extract 1 1) f) #b1))
(check-synth)
"#,
        )
        .expect("test sygus file should parse");

        deffun::ENV.clear();
        deffun::ENV
            .parse_from_file(&file)
            .expect("define-funs should parse");
        let problem = SynthProblem::parse_from_file(&file).expect("problem should parse");
        let spec = NullarySpec::from_file(&file, &problem)
            .expect("nullary spec should parse")
            .expect("fixture should be recognized as nullary");

        let expr = search_nullary(&problem, &spec).expect("recursive nullary search should work");
        let value = expr.eval(&[]).expect("result should evaluate");

        assert_eq!(value.to_smt_hex(), "#x3");
        assert!(expr.to_string().contains("both"));
    }
}
