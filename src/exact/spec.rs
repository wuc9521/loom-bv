use std::collections::BTreeMap;

use sygus_parser::ast::{Identifier, Literal as SyGuSLiteral, SyGuSCmd, SyGuSFile, SyGuSTerm};

use crate::{
    enumerate::{expr::OwnedExpr, value::Value},
    parse::{self, new_custom_error_span, SynthProblem},
};

use super::search::search_problem;
use super::util::{empty_span, extract_indices_from_identifier};

// ---------------------------------------------------------------------------
//  NullarySpec — the synthesis target for the exact-nullary engine
// ---------------------------------------------------------------------------

pub enum NullarySpec {
    Exact(Value),
    BitConstraints {
        bits: usize,
        known_bits: BTreeMap<usize, bool>,
        /// Boolean / BV constraints over the synth function, compiled with
        /// [`OwnedExpr::from_term`] (same path as PBE / ref-impl) and checked
        /// via [`OwnedExpr::eval`]. A constraint holds when evaluation yields
        /// zero (see boolean encoding in `enumerate/expr.rs` `from_term`).
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

    /// Split label bit-indices into the "must be 1" and "must be 0" sets.
    /// `None` if the spec isn't bit-constraint-shaped (the only shape the
    /// LFP search currently uses).
    pub(crate) fn label_indices(&self) -> Option<(Vec<usize>, Vec<usize>)> {
        let known_bits = match self {
            NullarySpec::BitConstraints { known_bits, .. } => known_bits,
            NullarySpec::Exact(_) => return None,
        };
        let mut pos = Vec::new();
        let mut neg = Vec::new();
        for (idx, expected) in known_bits {
            if *expected {
                pos.push(*idx);
            } else {
                neg.push(*idx);
            }
        }
        Some((pos, neg))
    }

    pub(crate) fn matches(&self, value: &Value) -> bool {
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

    /// Drive the bottom-up exact-nullary search. In `fixpoint = Some(name)`
    /// mode each start-NT candidate is iterated to its LFP via Kleene; in
    /// direct mode candidates are checked against the spec immediately.
    pub fn search(
        &self,
        problem: &SynthProblem<'static>,
        min: bool,
        fixpoint: Option<&str>,
    ) -> parse::Result<OwnedExpr> {
        // Note: the `eval_defined` memo is only enabled in LFP mode (by
        // `LfpSpec::search`). Tried turning it on for direct mode too;
        // hit rate on Reg/0024 was 0.1% (define-fun calls in the
        // bottom-up search rarely repeat with identical args), so it was
        // pure overhead.
        search_problem(problem, self, min, fixpoint)
    }
}

// ---------------------------------------------------------------------------
//  SyGuS-file parsing helpers
// ---------------------------------------------------------------------------


pub fn parse_target_define_fun(
    file: &SyGuSFile,
    target_name: &str,
) -> parse::Result<Option<Value>> {
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

pub fn parse_bit_constraints(
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
            if let Some(bits) = collect_bit_constraints(c, target_name) {
                for (bit, value) in bits {
                    if bit >= target_bits {
                        continue;
                    }
                    found_any = true;
                    if let Some(old) = known_bits.get(&bit).copied() {
                        if old != value {
                            return Err(new_custom_error_span(
                                format!(
                                    "Conflicting constraints on bit {} of {}",
                                    bit, target_name
                                ),
                                empty_span(),
                            ));
                        }
                    } else {
                        known_bits.insert(bit, value);
                    }
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

/// Try to extract a conjunction of bit constraints from a term.
/// Handles `and`, `not`, and atomic `(= (extract i i) target) literal` patterns.
/// Returns None if the term cannot be fully decomposed into bit constraints.
fn collect_bit_constraints(
    term: &SyGuSTerm,
    target_name: &str,
) -> Option<Vec<(usize, bool)>> {
    if let SyGuSTerm::Annotated(inner, _) = term {
        return collect_bit_constraints(inner, target_name);
    }
    let SyGuSTerm::Application(op, args) = term else {
        return None;
    };
    match op.get_name() {
        "not" if args.len() == 1 => {
            let inner = collect_bit_constraints(&args[0], target_name)?;
            Some(inner.into_iter().map(|(bit, val)| (bit, !val)).collect())
        }
        "and" => {
            let mut result = Vec::new();
            for arg in args {
                result.extend(collect_bit_constraints(arg, target_name)?);
            }
            Some(result)
        }
        "=" if args.len() == 2 => {
            let pair = extract_bit_of_target(&args[0], target_name)
                .zip(bit_literal(&args[1]))
                .or_else(|| {
                    extract_bit_of_target(&args[1], target_name).zip(bit_literal(&args[0]))
                })?;
            Some(vec![pair])
        }
        _ => None,
    }
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

