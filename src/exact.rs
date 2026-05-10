use std::cmp::Reverse;
use std::collections::hash_map::Entry;
use std::collections::BTreeMap;
use std::time::{Duration, Instant};

mod eval;
mod grammar;
mod relevance;
mod spec;

use num_bigint::BigUint;
use num_traits::One;
use rustc_hash::FxHashMap;
use sygus_parser::ast::SyGuSFile;

use crate::{
    enumerate::{
        expr::OwnedExpr,
        grammar::{for_each_candidate_tuple, for_each_size_split, MultiConfig, TemplateExpr},
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
    profile: FxHashMap<(usize, usize), EvalProfile>,
}

#[derive(Clone, Default)]
struct EvalProfile {
    calls: usize,
    hits: usize,
    misses: usize,
    total: Duration,
    miss_total: Duration,
}

impl ExactEvalCache {
    fn record_eval(&mut self, arity: usize, fid: usize, hit: bool, elapsed: Duration) {
        let profile = self.profile.entry((arity, fid)).or_default();
        profile.calls += 1;
        profile.total += elapsed;
        if hit {
            profile.hits += 1;
        } else {
            profile.misses += 1;
            profile.miss_total += elapsed;
        }
    }

    fn top_profiles(&self, limit: usize) -> Vec<String> {
        let mut entries = self
            .profile
            .iter()
            .map(|((arity, fid), profile)| (*arity, *fid, profile.clone()))
            .collect::<Vec<_>>();
        entries.sort_by_key(|(_, _, profile)| Reverse(profile.total));
        entries
            .into_iter()
            .take(limit)
            .map(|(arity, fid, profile)| {
                let avg_us = if profile.calls == 0 {
                    0
                } else {
                    profile.total.as_micros() / profile.calls as u128
                };
                format!(
                    "{}[{}]: calls={}, hits={}, misses={}, total={:?}, miss_total={:?}, avg={}us",
                    deffun::ENV.name(fid, arity),
                    arity,
                    profile.calls,
                    profile.hits,
                    profile.misses,
                    profile.total,
                    profile.miss_total,
                    avg_us
                )
            })
            .collect()
    }
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
                known_bits: known_bits
                    .iter()
                    .map(|(bit, value)| (*bit, *value))
                    .collect(),
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

fn search_nullary_multi_nt(
    grammar: &ExactGrammar<'static>,
    spec: &NullarySpec,
    synth_bits: usize,
) -> parse::Result<OwnedExpr> {
    let goal = GoalObligation::from_spec(spec);
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
    let mut goal_score_cache = FxHashMap::<Value, usize>::default();
    // Regression isolation: disable the abstract goal-ordering path and keep
    // the nullary solver on plain bottom-up exact enumeration order.
    let use_goal_ordering = false;
    let mut best_goal_score = 0usize;
    let mut last_progress_log = Instant::now();

    for size in 1.. {
        let size_start = Instant::now();
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
                        if by_size[*child_nt].get(child_size).is_none_or(Vec::is_empty) {
                            continue;
                        }
                        let mut children = by_size[*child_nt]
                            .get(child_size)
                            .map(Vec::as_slice)
                            .unwrap_or(&[][..])
                            .to_vec();
                        if use_goal_ordering {
                            filter_and_sort_unary_children(*fid, &mut children, &goal, synth_bits);
                        }
                        for child in &children {
                            eval_attempted += 1;
                            let value = eval::evaluate_fop1(*fid, &child.value, &mut eval_cache);
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
                            if last_progress_log.elapsed() >= Duration::from_secs(5) {
                                info!(
                                    "exact-nullary progress size={} phase=unary attempted={} inserted={} elapsed={:?}",
                                    size,
                                    eval_attempted,
                                    inserted_this_size,
                                    size_start.elapsed()
                                );
                                for line in eval_cache.top_profiles(4) {
                                    info!("exact-nullary hot {}", line);
                                }
                                last_progress_log = Instant::now();
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
                                    filter_and_rank_binary_pairs(*fid, &lhs_pool, &rhs_pool, &goal)
                                {
                                    let lhs = &lhs_pool[lhs_idx];
                                    let rhs = &rhs_pool[rhs_idx];
                                    eval_attempted += 1;
                                    let value = eval::evaluate_fop2(
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
                                    if last_progress_log.elapsed() >= Duration::from_secs(5) {
                                        info!(
                                            "exact-nullary progress size={} phase=binary attempted={} inserted={} elapsed={:?}",
                                            size,
                                            eval_attempted,
                                            inserted_this_size,
                                            size_start.elapsed()
                                        );
                                        for line in eval_cache.top_profiles(4) {
                                            info!("exact-nullary hot {}", line);
                                        }
                                        last_progress_log = Instant::now();
                                    }
                                }
                            } else {
                                for lhs in &lhs_pool {
                                    for rhs in &rhs_pool {
                                        eval_attempted += 1;
                                        let value = eval::evaluate_fop2(
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
                                        if last_progress_log.elapsed()
                                            >= Duration::from_secs(5)
                                        {
                                            info!(
                                                "exact-nullary progress size={} phase=binary attempted={} inserted={} elapsed={:?}",
                                                size,
                                                eval_attempted,
                                                inserted_this_size,
                                                size_start.elapsed()
                                            );
                                            for line in eval_cache.top_profiles(4) {
                                                info!("exact-nullary hot {}", line);
                                            }
                                            last_progress_log = Instant::now();
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
                                        eval::evaluate_fopn(*fid, &child_values, &mut eval_cache)
                                    else {
                                        eval_failed += 1;
                                        return;
                                    };
                                    let children =
                                        tuple.iter().map(|cand| cand.node).collect::<Vec<_>>();
                                    staged.push((value, children));
                                    if last_progress_log.elapsed() >= Duration::from_secs(5) {
                                        info!(
                                            "exact-nullary progress size={} phase=nary attempted={} inserted={} elapsed={:?}",
                                            size,
                                            eval_attempted,
                                            inserted_this_size,
                                            size_start.elapsed()
                                        );
                                        for line in eval_cache.top_profiles(4) {
                                            info!("exact-nullary hot {}", line);
                                        }
                                        last_progress_log = Instant::now();
                                    }
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
                                    if last_progress_log.elapsed() >= Duration::from_secs(5) {
                                        info!(
                                            "exact-nullary progress size={} phase=generic attempted={} inserted={} elapsed={:?}",
                                            size,
                                            eval_attempted,
                                            inserted_this_size,
                                            size_start.elapsed()
                                        );
                                        for line in eval_cache.top_profiles(4) {
                                            info!("exact-nullary hot {}", line);
                                        }
                                        last_progress_log = Instant::now();
                                    }
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
                    let score = cached_goal_score(&candidate.value, &goal, &mut goal_score_cache);
                    if score > best_goal_score {
                        best_goal_score = score;
                    }
                }
            }
        }
        info!(
            "exact-nullary size={} inserted={} seen_start={} seen_total={} best_goal={}/{} elapsed={:?}",
            size,
            inserted_this_size,
            seen.bucket_len(grammar.start),
            seen.total_len(),
            best_goal_score,
            goal.known_bits.len(),
            size_start.elapsed()
        );
        info!(
            "exact-nullary eval size={} attempted={} failed={}",
            size, eval_attempted, eval_failed
        );
        for line in eval_cache.top_profiles(4) {
            info!("exact-nullary hot {}", line);
        }
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
        (Reverse(*rank), Reverse(*child_score), *lhs_idx, *rhs_idx)
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
    let abs_args = args
        .iter()
        .map(|arg| AbsValue::exact(arg))
        .collect::<Vec<_>>();
    let abs = eval_fop_abs(fid, nargs, &abs_args);
    goal.abstract_rank(&abs)
}

fn eval_fop_abs(fid: usize, nargs: usize, args: &[AbsValue]) -> AbsValue {
    let body = deffun::ENV.apply(fid, nargs);
    let fallback_bits = deffun::ENV.ret_bits(fid, nargs);
    eval_owned_abs(body, args, fallback_bits, 0)
}

fn eval_owned_abs(
    expr: &OwnedExpr,
    vars: &[AbsValue],
    fallback_bits: usize,
    depth: usize,
) -> AbsValue {
    if depth > 64 {
        return AbsValue::top(fallback_bits.max(1));
    }
    match expr {
        OwnedExpr::Var(i) => vars
            .get(*i)
            .cloned()
            .unwrap_or_else(|| AbsValue::top(fallback_bits.max(1))),
        OwnedExpr::Const(v) => AbsValue::exact(v),
        OwnedExpr::Let(_, _, _) => {
            let mut scoped = vars.to_vec();
            let mut current = expr;
            loop {
                match current {
                    OwnedExpr::Let(_, value, body) => {
                        let bound = eval_owned_abs(value, &scoped, fallback_bits, depth + 1);
                        scoped.push(bound);
                        current = body;
                    }
                    other => return eval_owned_abs(other, &scoped, fallback_bits, depth + 1),
                }
            }
        }
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
        OwnedExpr::Let(_, _, body) => owned_expr_width(body),
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
    if width == 1 {
        return Value::from_u64(value.bit(lo as usize) as u64, 1);
    }
    if value.bits() <= 64 {
        return Value::from_u64(value.as_u64_lossy() >> lo, width);
    }
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
