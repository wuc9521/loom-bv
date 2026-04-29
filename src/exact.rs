use std::collections::{BTreeMap, HashMap};

use sygus_parser::ast::{Identifier, Literal as SyGuSLiteral, SyGuSCmd, SyGuSFile, SyGuSTerm};

use crate::{
    enumerate::{
        config::{Config, Rule},
        expr::OwnedExpr,
        value::Value,
    },
    parse::{self, new_custom_error_span, SynthProblem},
};

const MAX_NULLARY_SIZE: usize = 24;

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
                let raw = value.to_biguint();
                known_bits.iter().all(|(bit, expected)| {
                    let actual = ((&raw >> *bit) & num_bigint::BigUint::from(1u8))
                        == num_bigint::BigUint::from(1u8);
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
    let mut by_size: Vec<Vec<OwnedExpr>> = vec![Vec::new(); MAX_NULLARY_SIZE + 1];
    let mut seen = HashMap::<Value, usize>::new();

    for rule in config.iter() {
        if !rule.is_atom() {
            continue;
        }
        let Some(expr) = build_atom(rule) else {
            continue;
        };
        if let Some(found) = insert_candidate(expr, 1, spec, &mut seen, &mut by_size)? {
            return Ok(found);
        }
    }

    for size in 2..=MAX_NULLARY_SIZE {
        for rule in config.iter() {
            match rule {
                Rule::Var(_) | Rule::Const(_) | Rule::Fop0(_) => {}
                Rule::Not
                | Rule::Neg
                | Rule::LShrC(_)
                | Rule::ShlC(_)
                | Rule::Fop1(_) => {
                    let children = by_size[size - 1].clone();
                    for child in &children {
                        let Some(expr) = build_unary(rule, child, problem.bits) else {
                            continue;
                        };
                        if let Some(found) =
                            insert_candidate(expr, size, spec, &mut seen, &mut by_size)?
                        {
                            return Ok(found);
                        }
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
                        let lhs_terms = by_size[lhs_size].clone();
                        let rhs_terms = by_size[rhs_size].clone();
                        for lhs in &lhs_terms {
                            for rhs in &rhs_terms {
                                let Some(expr) = build_binary(rule, lhs, rhs) else {
                                    continue;
                                };
                                if let Some(found) =
                                    insert_candidate(expr, size, spec, &mut seen, &mut by_size)?
                                {
                                    return Ok(found);
                                }
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
                            let cond_terms = by_size[cond_size].clone();
                            let then_terms = by_size[then_size].clone();
                            let else_terms = by_size[else_size].clone();
                            for cond in &cond_terms {
                                for then_expr in &then_terms {
                                    for else_expr in &else_terms {
                                        let expr = OwnedExpr::Ite(
                                            Box::new(cond.clone()),
                                            Box::new(then_expr.clone()),
                                            Box::new(else_expr.clone()),
                                        );
                                        if let Some(found) = insert_candidate(
                                            expr,
                                            size,
                                            spec,
                                            &mut seen,
                                            &mut by_size,
                                        )? {
                                            return Ok(found);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                Rule::ChatGPT(_, _) => {}
            }
        }
    }

    Err(new_custom_error_span(
        format!(
            "Nullary exact search failed within size bound {} for {}",
            MAX_NULLARY_SIZE, problem.name
        ),
        pest::Span::new("", 0, 0).unwrap(),
    ))
}

#[derive(Clone)]
enum MultiNtRule {
    Atom(OwnedExpr),
    Alias(usize),
    Unary(usize, usize),
    Binary(usize, usize, usize),
    Ite(usize, usize, usize),
}

#[derive(Clone)]
struct MultiNtGrammar<'a> {
    nts: Vec<(&'a str, Vec<MultiNtRule>)>,
    start: usize,
}

fn search_nullary_multi_nt(
    problem: &SynthProblem<'static>,
    spec: &NullarySpec,
) -> parse::Result<OwnedExpr> {
    let grammar = build_multi_nt_grammar(problem)?;
    let nt_count = grammar.nts.len();
    let mut by_size = vec![vec![Vec::<OwnedExpr>::new(); MAX_NULLARY_SIZE + 1]; nt_count];
    let mut seen = vec![HashMap::<Value, usize>::new(); nt_count];

    for (nt_idx, (_, rules)) in grammar.nts.iter().enumerate() {
        for rule in rules {
            let MultiNtRule::Atom(expr) = rule else {
                continue;
            };
            if let Some(found) = insert_multi_nt_candidate(
                nt_idx,
                expr.clone(),
                1,
                &grammar,
                spec,
                &mut seen,
                &mut by_size,
            )? {
                return Ok(found);
            }
        }
    }

    for size in 2..=MAX_NULLARY_SIZE {
        for (nt_idx, (_, rules)) in grammar.nts.iter().enumerate() {
            for rule in rules {
                match *rule {
                    MultiNtRule::Atom(_) => {}
                    MultiNtRule::Alias(child_nt) => {
                        let children = by_size[child_nt][size].clone();
                        for child in children {
                            if let Some(found) = insert_multi_nt_candidate(
                                nt_idx,
                                child,
                                size,
                                &grammar,
                                spec,
                                &mut seen,
                                &mut by_size,
                            )? {
                                return Ok(found);
                            }
                        }
                    }
                    MultiNtRule::Unary(fid, child_nt) => {
                        let children = by_size[child_nt][size - 1].clone();
                        for child in children {
                            let expr = OwnedExpr::Fop1Dyn(fid, Box::new(child));
                            if let Some(found) = insert_multi_nt_candidate(
                                nt_idx,
                                expr,
                                size,
                                &grammar,
                                spec,
                                &mut seen,
                                &mut by_size,
                            )? {
                                return Ok(found);
                            }
                        }
                    }
                    MultiNtRule::Binary(fid, lhs_nt, rhs_nt) => {
                        if size < 3 {
                            continue;
                        }
                        for lhs_size in 1..=(size - 2) {
                            let rhs_size = size - 1 - lhs_size;
                            let lhs_terms = by_size[lhs_nt][lhs_size].clone();
                            let rhs_terms = by_size[rhs_nt][rhs_size].clone();
                            for lhs in &lhs_terms {
                                for rhs in &rhs_terms {
                                    let expr = OwnedExpr::Fop2Dyn(
                                        fid,
                                        Box::new(lhs.clone()),
                                        Box::new(rhs.clone()),
                                    );
                                    if let Some(found) = insert_multi_nt_candidate(
                                        nt_idx,
                                        expr,
                                        size,
                                        &grammar,
                                        spec,
                                        &mut seen,
                                        &mut by_size,
                                    )? {
                                        return Ok(found);
                                    }
                                }
                            }
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
                                let cond_terms = by_size[cond_nt][cond_size].clone();
                                let then_terms = by_size[then_nt][then_size].clone();
                                let else_terms = by_size[else_nt][else_size].clone();
                                for cond in &cond_terms {
                                    for then_expr in &then_terms {
                                        for else_expr in &else_terms {
                                            let expr = OwnedExpr::Ite(
                                                Box::new(cond.clone()),
                                                Box::new(then_expr.clone()),
                                                Box::new(else_expr.clone()),
                                            );
                                            if let Some(found) = insert_multi_nt_candidate(
                                                nt_idx,
                                                expr,
                                                size,
                                                &grammar,
                                                spec,
                                                &mut seen,
                                                &mut by_size,
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
            }
        }
    }

    Err(new_custom_error_span(
        format!(
            "Nullary exact search failed within size bound {} for {}",
            MAX_NULLARY_SIZE, problem.name
        ),
        pest::Span::new("", 0, 0).unwrap(),
    ))
}

fn insert_multi_nt_candidate(
    nt_idx: usize,
    expr: OwnedExpr,
    size: usize,
    grammar: &MultiNtGrammar<'_>,
    spec: &NullarySpec,
    seen: &mut [HashMap<Value, usize>],
    by_size: &mut [Vec<Vec<OwnedExpr>>],
) -> parse::Result<Option<OwnedExpr>> {
    let value = expr.eval(&[]).map_err(|_| {
        new_custom_error_span(
            format!("Nullary exact search failed to evaluate candidate {}", expr),
            pest::Span::new("", 0, 0).unwrap(),
        )
    })?;
    if nt_idx == grammar.start && spec.matches(&value) {
        return Ok(Some(expr));
    }
    if seen[nt_idx].contains_key(&value) {
        return Ok(None);
    }
    seen[nt_idx].insert(value, size);
    by_size[nt_idx][size].push(expr);
    Ok(None)
}

fn build_multi_nt_grammar(problem: &SynthProblem<'static>) -> parse::Result<MultiNtGrammar<'static>> {
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
            SyGuSLiteral::Bool(v) => Some(OwnedExpr::Const(Value::from_u64(if *v { 1 } else { 0 }, 1))),
            SyGuSLiteral::Numeral(v) => Some(OwnedExpr::Const(Value::from_u64(*v as u64, 64))),
            SyGuSLiteral::HexConst(v) => {
                let s = if v.starts_with("#x") { v.clone() } else { format!("#x{}", v) };
                let width = v.trim_start_matches("#x").len() * 4;
                crate::parse::literals::value_constant(&s, width.max(1), pest::Span::new("", 0, 0).unwrap())
                    .ok()
                    .map(OwnedExpr::Const)
            }
            SyGuSLiteral::BinConst(v) => {
                let s = if v.starts_with("#b") { v.clone() } else { format!("#b{}", v) };
                let width = v.trim_start_matches("#b").len();
                crate::parse::literals::value_constant(&s, width.max(1), pest::Span::new("", 0, 0).unwrap())
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
        .collect::<HashMap<_, _>>();

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
                            if let Some(fid) = crate::parse::deffun::ENV.lookup(opname, child_nts.len()) {
                                match child_nts.as_slice() {
                                    [a] => rules.push(MultiNtRule::Unary(fid, *a)),
                                    [a, b] => rules.push(MultiNtRule::Binary(fid, *a, *b)),
                                    _ => {
                                        return Err(new_custom_error_span(
                                            format!(
                                                "Unsupported nullary grammar operator arity {} for {}",
                                                child_nts.len(),
                                                opname
                                            ),
                                            pest::Span::new("", 0, 0).unwrap(),
                                        ));
                                    }
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

fn insert_candidate(
    expr: OwnedExpr,
    size: usize,
    spec: &NullarySpec,
    seen: &mut HashMap<Value, usize>,
    by_size: &mut [Vec<OwnedExpr>],
) -> parse::Result<Option<OwnedExpr>> {
    let value = expr.eval(&[]).map_err(|_| {
        new_custom_error_span(
            format!("Nullary exact search failed to evaluate candidate {}", expr),
            pest::Span::new("", 0, 0).unwrap(),
        )
    })?;
    if spec.matches(&value) {
        return Ok(Some(expr));
    }
    if seen.contains_key(&value) {
        return Ok(None);
    }
    seen.insert(value, size);
    by_size[size].push(expr);
    Ok(None)
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
    match term {
        SyGuSTerm::Application(id, args) if args.len() == 1 => {
            let arg_is_target =
                matches!(&args[0], SyGuSTerm::Identifier(var) if var.get_name() == target_name);
            if !arg_is_target {
                return None;
            }
            if let Identifier::Indexed(sym, idxs) = id {
                if sym == "extract" && idxs.len() >= 2 {
                    if let (
                        sygus_parser::ast::Index::Numeral(hi),
                        sygus_parser::ast::Index::Numeral(lo),
                    ) = (&idxs[0], &idxs[1])
                    {
                        if hi == lo {
                            return Some(*hi);
                        }
                    }
                }
                if sym == "_" && idxs.len() >= 3 {
                    if let (
                        sygus_parser::ast::Index::Symbol(op),
                        sygus_parser::ast::Index::Numeral(hi),
                        sygus_parser::ast::Index::Numeral(lo),
                    ) = (&idxs[0], &idxs[1], &idxs[2])
                    {
                        if op == "extract" && hi == lo {
                            return Some(*hi);
                        }
                    }
                }
            }
            None
        }
        _ => None,
    }
}
