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
