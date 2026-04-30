use std::collections::hash_map::Entry;
use std::collections::BTreeMap;

use rustc_hash::FxHashMap;

use sygus_parser::ast::{Identifier, Literal as SyGuSLiteral, SyGuSCmd, SyGuSFile, SyGuSTerm};

use crate::{
    enumerate::{
        config::{Config, Rule},
        expr::OwnedExpr,
        op,
        value::Value,
    },
    parse::{self, new_custom_error_span, SynthProblem},
};

pub enum NullarySpec {
    Exact(Value),
    BitConstraints {
        bits: usize,
        known_bits: BTreeMap<usize, bool>,
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
        if let Some(known_bits) = parse_bit_constraints(file, problem.name, problem.bits)? {
            return Ok(Some(Self::BitConstraints {
                bits: problem.bits,
                known_bits,
            }));
        }
        Ok(None)
    }

    fn matches(&self, value: &Value) -> bool {
        match self {
            Self::Exact(expected) => value == expected,
            Self::BitConstraints { bits, known_bits } => {
                if value.bits() != *bits {
                    return false;
                }
                known_bits.iter().all(|(bit, expected)| {
                    let actual = value.bit(*bit);
                    actual == *expected
                })
            }
        }
    }
}

pub fn search_nullary(
    problem: &SynthProblem<'static>,
    spec: &NullarySpec,
) -> parse::Result<OwnedExpr> {
    if problem.cfg.len() > 1 {
        return search_nullary_multi_nt(problem, spec);
    }
    search_nullary_single_nt(problem, spec)
}

fn search_nullary_single_nt(
    problem: &SynthProblem<'static>,
    spec: &NullarySpec,
) -> parse::Result<OwnedExpr> {
    let config = Config::<1>::from_problem(problem, true)?;
    let mut by_size: Vec<Vec<Candidate>> = vec![Vec::new(), Vec::new()];
    let mut seen = FxHashMap::<Value, usize>::default();
    let mut stats = vec![RuleStats::default(); config.len()];

    for (rule_idx, rule) in config.iter().enumerate() {
        if !rule.is_atom() {
            continue;
        }
        let Some(expr) = build_atom(rule) else {
            continue;
        };
        let value = expr.eval(&[]).map_err(|_| {
            new_custom_error_span(
                format!("Nullary exact search failed to evaluate candidate {}", expr),
                pest::Span::new("", 0, 0).unwrap(),
            )
        })?;
        match insert_single_nt_candidate_lazy(value, 1, spec, &mut seen, &mut by_size, || expr)? {
            InsertOutcome::Found(found) => return Ok(found),
            InsertOutcome::Inserted => stats[rule_idx].novel += 1,
            InsertOutcome::Duplicate => {}
        }
        stats[rule_idx].attempts += 1;
    }

    let mut size = 2;
    loop {
        by_size.push(Vec::new());
        let mut order = (0..config.len()).collect::<Vec<_>>();
        order.sort_by(|&a, &b| {
            rule_priority(&config[a], stats[a])
                .cmp(&rule_priority(&config[b], stats[b]))
                .reverse()
        });
        for rule_idx in order {
            let rule = &config[rule_idx];
            match rule {
                Rule::Var(_) | Rule::Const(_) | Rule::Fop0(_) => {}
                Rule::Not | Rule::Neg | Rule::LShrC(_) | Rule::ShlC(_) | Rule::Fop1(_) => {
                    let children_len = by_size[size - 1].len();
                    for idx in 0..children_len {
                        let child = &by_size[size - 1][idx];
                        let Some(value) = eval_unary_rule(rule, &child.value, problem.bits) else {
                            continue;
                        };
                        let child_expr = child.expr.clone();
                        match insert_single_nt_candidate_lazy(
                            value,
                            size,
                            spec,
                            &mut seen,
                            &mut by_size,
                            || build_unary(rule, &child_expr, problem.bits).unwrap(),
                        )? {
                            InsertOutcome::Found(found) => return Ok(found),
                            InsertOutcome::Inserted => stats[rule_idx].novel += 1,
                            InsertOutcome::Duplicate => {}
                        }
                        stats[rule_idx].attempts += 1;
                    }
                }
                Rule::Add
                | Rule::Xor
                | Rule::And
                | Rule::Or
                | Rule::Sub
                | Rule::Mul
                | Rule::UDiv
                | Rule::LShr
                | Rule::Shl
                | Rule::SDiv
                | Rule::URem
                | Rule::SRem
                | Rule::AShr
                | Rule::Fop2(_) => {
                    if size < 3 {
                        continue;
                    }
                    for lhs_size in 1..=(size - 2) {
                        let rhs_size = size - 1 - lhs_size;
                        let lhs_len = by_size[lhs_size].len();
                        let rhs_len = by_size[rhs_size].len();
                        for lhs_idx in 0..lhs_len {
                            for rhs_idx in 0..rhs_len {
                                let lhs = &by_size[lhs_size][lhs_idx];
                                let rhs = &by_size[rhs_size][rhs_idx];
                                let Some(value) = eval_binary_rule(rule, &lhs.value, &rhs.value)
                                else {
                                    continue;
                                };
                                let lhs_expr = lhs.expr.clone();
                                let rhs_expr = rhs.expr.clone();
                                match insert_single_nt_candidate_lazy(
                                    value,
                                    size,
                                    spec,
                                    &mut seen,
                                    &mut by_size,
                                    || build_binary(rule, &lhs_expr, &rhs_expr).unwrap(),
                                )? {
                                    InsertOutcome::Found(found) => return Ok(found),
                                    InsertOutcome::Inserted => stats[rule_idx].novel += 1,
                                    InsertOutcome::Duplicate => {}
                                }
                                stats[rule_idx].attempts += 1;
                            }
                        }
                    }
                }
                Rule::Ite => {
                    if size < 4 {
                        continue;
                    }
                    for cond_size in 1..=(size - 3) {
                        for then_size in 1..=(size - 2 - cond_size) {
                            let else_size = size - 1 - cond_size - then_size;
                            if else_size == 0 {
                                continue;
                            }
                            let cond_len = by_size[cond_size].len();
                            let then_len = by_size[then_size].len();
                            let else_len = by_size[else_size].len();
                            for cond_idx in 0..cond_len {
                                for then_idx in 0..then_len {
                                    for else_idx in 0..else_len {
                                        let cond = &by_size[cond_size][cond_idx];
                                        let then_expr = &by_size[then_size][then_idx];
                                        let else_expr = &by_size[else_size][else_idx];
                                        let value = op::ite(
                                            cond.value.clone(),
                                            then_expr.value.clone(),
                                            else_expr.value.clone(),
                                        );
                                        let cond_owned = cond.expr.clone();
                                        let then_owned = then_expr.expr.clone();
                                        let else_owned = else_expr.expr.clone();
                                        match insert_single_nt_candidate_lazy(
                                            value,
                                            size,
                                            spec,
                                            &mut seen,
                                            &mut by_size,
                                            || {
                                                OwnedExpr::Ite(
                                                    Box::new(cond_owned),
                                                    Box::new(then_owned),
                                                    Box::new(else_owned),
                                                )
                                            },
                                        )? {
                                            InsertOutcome::Found(found) => return Ok(found),
                                            InsertOutcome::Inserted => stats[rule_idx].novel += 1,
                                            InsertOutcome::Duplicate => {}
                                        }
                                        stats[rule_idx].attempts += 1;
                                    }
                                }
                            }
                        }
                    }
                }
                Rule::ChatGPT(_, _) => {}
            }
        }
        size += 1;
    }
}

#[derive(Clone, Copy, Default)]
struct RuleStats {
    attempts: usize,
    novel: usize,
}

fn rule_priority(rule: &Rule<1>, stats: RuleStats) -> (usize, usize, usize) {
    let base = match rule {
        Rule::Fop2(_) => 5,
        Rule::Fop1(_) => 4,
        Rule::Ite => 0,
        Rule::Add
        | Rule::Xor
        | Rule::And
        | Rule::Or
        | Rule::Sub
        | Rule::Mul
        | Rule::UDiv
        | Rule::LShr
        | Rule::Shl
        | Rule::SDiv
        | Rule::URem
        | Rule::SRem
        | Rule::AShr => 1,
        Rule::Not | Rule::Neg | Rule::LShrC(_) | Rule::ShlC(_) => 2,
        Rule::Const(_) | Rule::Fop0(_) => 3,
        Rule::Var(_) | Rule::ChatGPT(_, _) => 0,
    };
    let yield_score = if stats.attempts == 0 {
        usize::MAX / 4
    } else {
        (stats.novel * 1024) / stats.attempts.max(1)
    };
    (base, yield_score, stats.novel)
}

#[derive(Clone)]
enum MultiNtRule {
    Atom(OwnedExpr),
    Alias(usize),
    Apply(usize, Vec<usize>),
    Ite(usize, usize, usize),
}

#[derive(Clone)]
struct MultiNtGrammar<'a> {
    nts: Vec<(&'a str, Vec<MultiNtRule>)>,
    start: usize,
}

#[derive(Clone)]
struct Candidate {
    expr: OwnedExpr,
    value: Value,
}

fn instantiate_defined_fun(fid: usize, args: &[OwnedExpr]) -> OwnedExpr {
    match args {
        [] => OwnedExpr::Fop0Dyn(fid),
        [a] => OwnedExpr::Fop1Dyn(fid, Box::new(a.clone())),
        [a, b] => OwnedExpr::Fop2Dyn(fid, Box::new(a.clone()), Box::new(b.clone())),
        _ => OwnedExpr::FopDyn(fid, args.to_vec()),
    }
}

fn for_each_size_split(
    total: usize,
    arity: usize,
    sizes: &mut Vec<usize>,
    f: &mut impl FnMut(&[usize]),
) {
    if arity == 0 {
        if total == 0 {
            f(sizes);
        }
        return;
    }
    if arity == 1 {
        sizes.push(total);
        f(sizes);
        sizes.pop();
        return;
    }
    let min_rest = arity - 1;
    for first in 1..=(total - min_rest) {
        sizes.push(first);
        for_each_size_split(total - first, arity - 1, sizes, f);
        sizes.pop();
    }
}

fn for_each_candidate_tuple<'a>(
    candidate_pools: &[&'a [Candidate]],
    tuple: &mut Vec<&'a Candidate>,
    f: &mut impl FnMut(&[&'a Candidate]),
) {
    if tuple.len() == candidate_pools.len() {
        f(tuple);
        return;
    }
    let idx = tuple.len();
    for candidate in candidate_pools[idx] {
        tuple.push(candidate);
        for_each_candidate_tuple(candidate_pools, tuple, f);
        tuple.pop();
    }
}

fn evaluate_apply_value(applied: &OwnedExpr, tuple: &[&Candidate]) -> Result<Value, ()> {
    let mut values = Vec::with_capacity(tuple.len());
    for candidate in tuple {
        values.push(candidate.value.clone());
    }
    applied.eval(&values).map_err(|_| ())
}

fn search_nullary_multi_nt(
    problem: &SynthProblem<'static>,
    spec: &NullarySpec,
) -> parse::Result<OwnedExpr> {
    let grammar = build_multi_nt_grammar(problem)?;
    let nt_count = grammar.nts.len();
    let mut by_size = vec![vec![Vec::<Candidate>::new(); 2]; nt_count];
    let mut seen = vec![FxHashMap::<Value, usize>::default(); nt_count];

    for (nt_idx, (_, rules)) in grammar.nts.iter().enumerate() {
        for rule in rules {
            let MultiNtRule::Atom(expr) = rule else {
                continue;
            };
            let value = expr.eval(&[]).map_err(|_| {
                new_custom_error_span(
                    format!("Nullary exact search failed to evaluate candidate {}", expr),
                    pest::Span::new("", 0, 0).unwrap(),
                )
            })?;
            if let Some(found) = insert_multi_nt_candidate_lazy(
                nt_idx,
                value,
                1,
                &grammar,
                spec,
                &mut seen,
                &mut by_size,
                || expr.clone(),
            )? {
                return Ok(found);
            }
        }
    }

    let mut size = 2;
    loop {
        for buckets in &mut by_size {
            buckets.push(Vec::new());
        }
        for (nt_idx, (_, rules)) in grammar.nts.iter().enumerate() {
            for rule in rules {
                match *rule {
                    MultiNtRule::Atom(_) => {}
                    MultiNtRule::Alias(child_nt) => {
                        let children_len = by_size[child_nt][size].len();
                        for idx in 0..children_len {
                            let child = &by_size[child_nt][size][idx];
                            let child_value = child.value.clone();
                            let child_expr = child.expr.clone();
                            if let Some(found) = insert_multi_nt_candidate_lazy(
                                nt_idx,
                                child_value,
                                size,
                                &grammar,
                                spec,
                                &mut seen,
                                &mut by_size,
                                || child_expr,
                            )? {
                                return Ok(found);
                            }
                        }
                    }
                    MultiNtRule::Apply(fid, ref child_nts) => {
                        if size <= child_nts.len() {
                            continue;
                        }
                        let total_child_size = size - 1;
                        let mut found = None;
                        let mut pending_error = None;
                        let mut size_args = Vec::with_capacity(child_nts.len());
                        for_each_size_split(
                            total_child_size,
                            child_nts.len(),
                            &mut size_args,
                            &mut |size_args| {
                                if found.is_some() || pending_error.is_some() {
                                    return;
                                }
                                let candidate_pools = child_nts
                                    .iter()
                                    .zip(size_args.iter())
                                    .map(|(child_nt, child_size)| {
                                        by_size[*child_nt][*child_size].as_slice()
                                    })
                                    .collect::<Vec<_>>();
                                let applied = crate::parse::deffun::ENV.apply(fid, child_nts.len());
                                let mut tuple = Vec::with_capacity(child_nts.len());
                                let mut staged = FxHashMap::<Value, Vec<OwnedExpr>>::default();
                                for_each_candidate_tuple(
                                    &candidate_pools,
                                    &mut tuple,
                                    &mut |tuple| {
                                        if found.is_some() || pending_error.is_some() {
                                            return;
                                        }
                                        let value = match evaluate_apply_value(&applied, tuple) {
                                            Ok(value) => value,
                                            Err(()) => return,
                                        };
                                        if nt_idx == grammar.start && spec.matches(&value) {
                                            let expr_args = tuple
                                                .iter()
                                                .map(|candidate| candidate.expr.clone())
                                                .collect::<Vec<_>>();
                                            found = Some(instantiate_defined_fun(fid, &expr_args));
                                            return;
                                        }
                                        if seen[nt_idx].contains_key(&value)
                                            || staged.contains_key(&value)
                                        {
                                            return;
                                        }
                                        let expr_args = tuple
                                            .iter()
                                            .map(|candidate| candidate.expr.clone())
                                            .collect::<Vec<_>>();
                                        staged.insert(value, expr_args);
                                    },
                                );
                                for (value, expr_args) in staged.drain() {
                                    match insert_multi_nt_candidate_lazy(
                                        nt_idx,
                                        value,
                                        size,
                                        &grammar,
                                        spec,
                                        &mut seen,
                                        &mut by_size,
                                        || instantiate_defined_fun(fid, &expr_args),
                                    ) {
                                        Ok(Some(expr)) => found = Some(expr),
                                        Ok(None) => {}
                                        Err(err) => {
                                            pending_error = Some(err);
                                            break;
                                        }
                                    }
                                }
                            },
                        );
                        if let Some(err) = pending_error {
                            return Err(err);
                        }
                        if let Some(found) = found {
                            return Ok(found);
                        }
                    }
                    MultiNtRule::Ite(cond_nt, then_nt, else_nt) => {
                        if size < 4 {
                            continue;
                        }
                        for cond_size in 1..=(size - 3) {
                            for then_size in 1..=(size - 2 - cond_size) {
                                let else_size = size - 1 - cond_size - then_size;
                                if else_size == 0 {
                                    continue;
                                }
                                let cond_len = by_size[cond_nt][cond_size].len();
                                let then_len = by_size[then_nt][then_size].len();
                                let else_len = by_size[else_nt][else_size].len();
                                let mut staged =
                                    FxHashMap::<Value, (OwnedExpr, OwnedExpr, OwnedExpr)>::default(
                                    );
                                for cond_idx in 0..cond_len {
                                    let cond = &by_size[cond_nt][cond_size][cond_idx];
                                    for then_idx in 0..then_len {
                                        let then_expr = &by_size[then_nt][then_size][then_idx];
                                        for else_idx in 0..else_len {
                                            let else_expr = &by_size[else_nt][else_size][else_idx];
                                            let value = op::ite(
                                                cond.value.clone(),
                                                then_expr.value.clone(),
                                                else_expr.value.clone(),
                                            );
                                            if nt_idx == grammar.start && spec.matches(&value) {
                                                return Ok(OwnedExpr::Ite(
                                                    Box::new(cond.expr.clone()),
                                                    Box::new(then_expr.expr.clone()),
                                                    Box::new(else_expr.expr.clone()),
                                                ));
                                            }
                                            if seen[nt_idx].contains_key(&value)
                                                || staged.contains_key(&value)
                                            {
                                                continue;
                                            }
                                            staged.insert(
                                                value,
                                                (
                                                    cond.expr.clone(),
                                                    then_expr.expr.clone(),
                                                    else_expr.expr.clone(),
                                                ),
                                            );
                                        }
                                    }
                                }
                                for (value, (cond_expr, then_expr, else_expr)) in staged.drain() {
                                    if let Some(found) = insert_multi_nt_candidate_lazy(
                                        nt_idx,
                                        value,
                                        size,
                                        &grammar,
                                        spec,
                                        &mut seen,
                                        &mut by_size,
                                        || {
                                            OwnedExpr::Ite(
                                                Box::new(cond_expr),
                                                Box::new(then_expr),
                                                Box::new(else_expr),
                                            )
                                        },
                                    )? {
                                        return Ok(found);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        size += 1;
    }
}

fn insert_multi_nt_candidate_lazy(
    nt_idx: usize,
    value: Value,
    size: usize,
    grammar: &MultiNtGrammar<'_>,
    spec: &NullarySpec,
    seen: &mut [FxHashMap<Value, usize>],
    by_size: &mut [Vec<Vec<Candidate>>],
    build_expr: impl FnOnce() -> OwnedExpr,
) -> parse::Result<Option<OwnedExpr>> {
    if nt_idx == grammar.start && spec.matches(&value) {
        return Ok(Some(build_expr()));
    }
    match seen[nt_idx].entry(value.clone()) {
        Entry::Occupied(_) => Ok(None),
        Entry::Vacant(entry) => {
            entry.insert(size);
            by_size[nt_idx][size].push(Candidate {
                expr: build_expr(),
                value,
            });
            Ok(None)
        }
    }
}

fn build_multi_nt_grammar(
    problem: &SynthProblem<'static>,
) -> parse::Result<MultiNtGrammar<'static>> {
    fn parse_identifier_atom(id: &Identifier) -> Option<OwnedExpr> {
        let name = id.get_name();
        if name.eq_ignore_ascii_case("true") {
            Some(OwnedExpr::Const(Value::from_u64(1, 1)))
        } else if name.eq_ignore_ascii_case("false") {
            Some(OwnedExpr::Const(Value::from_u64(0, 1)))
        } else if let Some(fid) = crate::parse::deffun::ENV.lookup(name, 0) {
            Some(OwnedExpr::Fop0Dyn(fid))
        } else {
            None
        }
    }

    fn parse_literal_atom(lit: &SyGuSLiteral) -> Option<OwnedExpr> {
        match lit {
            SyGuSLiteral::Bool(v) => {
                Some(OwnedExpr::Const(Value::from_u64(if *v { 1 } else { 0 }, 1)))
            }
            SyGuSLiteral::Numeral(v) => Some(OwnedExpr::Const(Value::from_u64(*v as u64, 64))),
            SyGuSLiteral::HexConst(v) => {
                let s = if v.starts_with("#x") {
                    v.clone()
                } else {
                    format!("#x{}", v)
                };
                let width = v.trim_start_matches("#x").len() * 4;
                crate::parse::literals::value_constant(
                    &s,
                    width.max(1),
                    pest::Span::new("", 0, 0).unwrap(),
                )
                .ok()
                .map(OwnedExpr::Const)
            }
            SyGuSLiteral::BinConst(v) => {
                let s = if v.starts_with("#b") {
                    v.clone()
                } else {
                    format!("#b{}", v)
                };
                let width = v.trim_start_matches("#b").len();
                crate::parse::literals::value_constant(
                    &s,
                    width.max(1),
                    pest::Span::new("", 0, 0).unwrap(),
                )
                .ok()
                .map(OwnedExpr::Const)
            }
            SyGuSLiteral::Decimal(_) | SyGuSLiteral::StringConst(_) => None,
        }
    }

    let nt_lookup = problem
        .cfg
        .iter()
        .enumerate()
        .map(|(idx, nt)| (nt.0, idx))
        .collect::<FxHashMap<_, _>>();

    let mut nts = Vec::with_capacity(problem.cfg.len());
    for nt in problem.cfg.iter() {
        let mut rules = Vec::new();
        for gterm in &nt.1 {
            let term = match gterm {
                sygus_parser::ast::SyGuSGTerm::SyGuSTerm(term) => term,
                sygus_parser::ast::SyGuSGTerm::Constant(_)
                | sygus_parser::ast::SyGuSGTerm::Variable(_) => {
                    continue;
                }
            };

            match term {
                SyGuSTerm::Identifier(id) => {
                    if let Some(child_nt) = nt_lookup.get(id.get_name()).copied() {
                        rules.push(MultiNtRule::Alias(child_nt));
                    } else if let Some(atom) = parse_identifier_atom(id) {
                        rules.push(MultiNtRule::Atom(atom));
                    } else {
                        return Err(new_custom_error_span(
                            format!("Unsupported nullary grammar symbol {}", id),
                            pest::Span::new("", 0, 0).unwrap(),
                        ));
                    }
                }
                SyGuSTerm::Literal(lit) => {
                    if let Some(atom) = parse_literal_atom(lit) {
                        rules.push(MultiNtRule::Atom(atom));
                    } else {
                        return Err(new_custom_error_span(
                            format!("Unsupported grammar literal {}", lit),
                            pest::Span::new("", 0, 0).unwrap(),
                        ));
                    }
                }
                SyGuSTerm::Application(id, args) => {
                    let opname = id.get_name();
                    let child_nts = args
                        .iter()
                        .map(|arg| match arg {
                            SyGuSTerm::Identifier(id) => nt_lookup.get(id.get_name()).copied(),
                            _ => None,
                        })
                        .collect::<Option<Vec<_>>>()
                        .ok_or_else(|| {
                            new_custom_error_span(
                                format!(
                                    "Unsupported nullary grammar term with non-nonterminal args: {}",
                                    term
                                ),
                                pest::Span::new("", 0, 0).unwrap(),
                            )
                        })?;
                    match (opname, child_nts.as_slice()) {
                        ("ite", [a, b, c]) => rules.push(MultiNtRule::Ite(*a, *b, *c)),
                        _ => {
                            if let Some(fid) =
                                crate::parse::deffun::ENV.lookup(opname, child_nts.len())
                            {
                                match child_nts.as_slice() {
                                    _ => rules.push(MultiNtRule::Apply(fid, child_nts.clone())),
                                }
                            } else {
                                return Err(new_custom_error_span(
                                    format!("Unsupported nullary grammar operator {}", opname),
                                    pest::Span::new("", 0, 0).unwrap(),
                                ));
                            }
                        }
                    }
                }
                _ => {
                    return Err(new_custom_error_span(
                        format!("Unsupported nullary grammar term {}", term),
                        pest::Span::new("", 0, 0).unwrap(),
                    ));
                }
            }
        }
        nts.push((nt.0, rules));
    }

    Ok(MultiNtGrammar { nts, start: 0 })
}

enum InsertOutcome {
    Found(OwnedExpr),
    Inserted,
    Duplicate,
}

fn insert_single_nt_candidate_lazy(
    value: Value,
    size: usize,
    spec: &NullarySpec,
    seen: &mut FxHashMap<Value, usize>,
    by_size: &mut [Vec<Candidate>],
    build_expr: impl FnOnce() -> OwnedExpr,
) -> parse::Result<InsertOutcome> {
    if spec.matches(&value) {
        return Ok(InsertOutcome::Found(build_expr()));
    }
    match seen.entry(value.clone()) {
        Entry::Occupied(_) => Ok(InsertOutcome::Duplicate),
        Entry::Vacant(entry) => {
            entry.insert(size);
            by_size[size].push(Candidate {
                expr: build_expr(),
                value,
            });
            Ok(InsertOutcome::Inserted)
        }
    }
}

fn build_atom(rule: &Rule<1>) -> Option<OwnedExpr> {
    match rule {
        Rule::Const(value) => Some(OwnedExpr::Const(value.clone())),
        Rule::Fop0(id) => Some(OwnedExpr::Fop0Dyn(*id)),
        Rule::Var(_) => None,
        _ => None,
    }
}

fn build_unary(rule: &Rule<1>, child: &OwnedExpr, bits: usize) -> Option<OwnedExpr> {
    let child = Box::new(child.clone());
    match rule {
        Rule::Not => Some(OwnedExpr::Not(child)),
        Rule::Neg => Some(OwnedExpr::Neg(child)),
        Rule::LShrC(v) => Some(OwnedExpr::LShr(
            child,
            Box::new(OwnedExpr::Const(Value::from_u64(*v, bits))),
        )),
        Rule::ShlC(v) => Some(OwnedExpr::Shl(
            child,
            Box::new(OwnedExpr::Const(Value::from_u64(*v, bits))),
        )),
        Rule::Fop1(id) => Some(OwnedExpr::Fop1Dyn(*id, child)),
        _ => None,
    }
}

fn build_binary(rule: &Rule<1>, lhs: &OwnedExpr, rhs: &OwnedExpr) -> Option<OwnedExpr> {
    let lhs = Box::new(lhs.clone());
    let rhs = Box::new(rhs.clone());
    match rule {
        Rule::Add => Some(OwnedExpr::Add(lhs, rhs)),
        Rule::Xor => Some(OwnedExpr::Xor(lhs, rhs)),
        Rule::And => Some(OwnedExpr::And(lhs, rhs)),
        Rule::Or => Some(OwnedExpr::Or(lhs, rhs)),
        Rule::Sub => Some(OwnedExpr::Sub(lhs, rhs)),
        Rule::Mul => Some(OwnedExpr::Mul(lhs, rhs)),
        Rule::UDiv => Some(OwnedExpr::UDiv(lhs, rhs)),
        Rule::LShr => Some(OwnedExpr::LShr(lhs, rhs)),
        Rule::Shl => Some(OwnedExpr::Shl(lhs, rhs)),
        Rule::SDiv => Some(OwnedExpr::SDiv(lhs, rhs)),
        Rule::URem => Some(OwnedExpr::URem(lhs, rhs)),
        Rule::SRem => Some(OwnedExpr::SRem(lhs, rhs)),
        Rule::AShr => Some(OwnedExpr::AShr(lhs, rhs)),
        Rule::Fop2(id) => Some(OwnedExpr::Fop2Dyn(*id, lhs, rhs)),
        _ => None,
    }
}

fn eval_unary_rule(rule: &Rule<1>, child: &Value, bits: usize) -> Option<Value> {
    match rule {
        Rule::Not => Some(op::not(child.clone())),
        Rule::Neg => Some(op::neg(child.clone())),
        Rule::LShrC(v) => Some(op::lshr(child.clone(), Value::from_u64(*v, bits))),
        Rule::ShlC(v) => Some(op::shl(child.clone(), Value::from_u64(*v, bits))),
        Rule::Fop1(id) => crate::parse::deffun::ENV
            .apply(*id, 1)
            .eval(&[child.clone()])
            .ok(),
        _ => None,
    }
}

fn eval_binary_rule(rule: &Rule<1>, lhs: &Value, rhs: &Value) -> Option<Value> {
    match rule {
        Rule::Add => Some(op::add(lhs.clone(), rhs.clone())),
        Rule::Xor => Some(op::xor(lhs.clone(), rhs.clone())),
        Rule::And => Some(op::and(lhs.clone(), rhs.clone())),
        Rule::Or => Some(op::or(lhs.clone(), rhs.clone())),
        Rule::Sub => Some(op::sub(lhs.clone(), rhs.clone())),
        Rule::Mul => Some(op::mul(lhs.clone(), rhs.clone())),
        Rule::UDiv => op::udiv(lhs.clone(), rhs.clone()).ok(),
        Rule::LShr => Some(op::lshr(lhs.clone(), rhs.clone())),
        Rule::Shl => Some(op::shl(lhs.clone(), rhs.clone())),
        Rule::SDiv => op::sdiv(lhs.clone(), rhs.clone()).ok(),
        Rule::URem => op::urem(lhs.clone(), rhs.clone()).ok(),
        Rule::SRem => op::srem(lhs.clone(), rhs.clone()).ok(),
        Rule::AShr => Some(op::ashr(lhs.clone(), rhs.clone())),
        Rule::Fop2(id) => crate::parse::deffun::ENV
            .apply(*id, 2)
            .eval(&[lhs.clone(), rhs.clone()])
            .ok(),
        _ => None,
    }
}

fn parse_target_define_fun(file: &SyGuSFile, target_name: &str) -> parse::Result<Option<Value>> {
    for cmd in &file.cmds {
        if let SyGuSCmd::DefineFun(name, args, _, body) = cmd {
            if name == target_name && args.is_empty() {
                let expr = OwnedExpr::from_term(body, &[])?;
                let value = expr.eval(&[]).map_err(|_| {
                    new_custom_error_span(
                        format!("failed to evaluate nullary define-fun {}", target_name),
                        pest::Span::new("", 0, 0).unwrap(),
                    )
                })?;
                return Ok(Some(value));
            }
        }
    }
    Ok(None)
}

fn parse_bit_constraints(
    file: &SyGuSFile,
    target_name: &str,
    target_bits: usize,
) -> parse::Result<Option<BTreeMap<usize, bool>>> {
    let mut known_bits = BTreeMap::<usize, bool>::new();
    let mut found_any = false;

    for cmd in &file.cmds {
        if let SyGuSCmd::Constraint(c) = cmd {
            let Some((bit, value)) = parse_bit_constraint(c, target_name) else {
                continue;
            };
            if bit >= target_bits {
                continue;
            }
            found_any = true;
            if let Some(old) = known_bits.get(&bit).copied() {
                if old != value {
                    return Err(new_custom_error_span(
                        format!("Conflicting constraints on bit {} of {}", bit, target_name),
                        pest::Span::new("", 0, 0).unwrap(),
                    ));
                }
            } else {
                known_bits.insert(bit, value);
            }
        }
    }

    Ok(found_any.then_some(known_bits))
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
    fn index_numeral(idx: &sygus_parser::ast::Index) -> Option<usize> {
        match idx {
            sygus_parser::ast::Index::Numeral(v) => Some(*v),
            sygus_parser::ast::Index::Symbol(_) => None,
        }
    }

    fn extract_indices(id: &Identifier) -> Option<(usize, usize)> {
        match id {
            Identifier::Indexed(sym, idxs) if sym == "extract" && idxs.len() >= 2 => {
                match (index_numeral(&idxs[0]), index_numeral(&idxs[1])) {
                    (Some(hi), Some(lo)) => Some((hi, lo)),
                    _ => None,
                }
            }
            Identifier::Indexed(sym, idxs) if sym == "_" && idxs.len() >= 3 => {
                match (&idxs[0], index_numeral(&idxs[1]), index_numeral(&idxs[2])) {
                    (sygus_parser::ast::Index::Symbol(op), Some(hi), Some(lo))
                        if op == "extract" =>
                    {
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

    match term {
        SyGuSTerm::Annotated(inner, _) => extract_bit_of_target(inner, target_name),
        SyGuSTerm::Application(id, args) if args.len() == 1 => {
            let arg_is_target =
                matches!(&args[0], SyGuSTerm::Identifier(var) if var.get_name() == target_name);
            if !arg_is_target {
                return None;
            }
            if let Some((hi, lo)) = extract_indices(id) {
                if hi == lo {
                    return Some(hi);
                }
            }
            None
        }
        _ => None,
    }
}
