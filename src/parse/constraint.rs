//! SyGuS constraint parsing — produces `RefImplConstraint` and the
//! bit-extract / structural-constraint shapes consumed by `Constraint`.

use std::collections::BTreeMap;

use derive_more::DebugCustom;
#[cfg(feature = "chatgpt")]
use rand::{rngs::StdRng, seq::SliceRandom};
use sygus_parser::ast::{
    Identifier, Index, Literal as SyGuSLiteral, SortedVar, SyGuSCmd, SyGuSFile, SyGuSTerm,
};

use crate::enumerate::{expr::OwnedExpr, value::BitVec};

#[cfg(feature = "chatgpt")]
use crate::exact::Constraint;

use super::{new_custom_error_span, ProblemView, Result};

// ---------------------------------------------------------------------------
//  Generic SyGuS-term helpers
// ---------------------------------------------------------------------------

pub fn empty_span() -> () {
    ()
}

pub fn literal_to_value(lit: &SyGuSLiteral) -> Result<BitVec> {
    match lit {
        SyGuSLiteral::Numeral(v) => Ok(BitVec::from_u64(*v as u64, 64)),
        SyGuSLiteral::Bool(v) => Ok(BitVec::from_u64(if *v { 1 } else { 0 }, 1)),
        SyGuSLiteral::HexConst(digits) => {
            let bits = digits.len() * 4;
            parse_bv_digits(digits, 16, bits.max(1))
        }
        SyGuSLiteral::BinConst(digits) => {
            let bits = digits.len();
            parse_bv_digits(digits, 2, bits.max(1))
        }
        SyGuSLiteral::Decimal(_) | SyGuSLiteral::StringConst(_) => Err(new_custom_error_span(
            "Constraint parser: expecting a SyGuS constant literal".into(),
            empty_span(),
        )),
    }
}

pub fn parse_bv_digits(digits: &str, radix: u32, bits: usize) -> Result<BitVec> {
    if bits <= 64 {
        u64::from_str_radix(digits, radix)
            .map(|v| BitVec::from_u64(v, bits))
            .map_err(|_| {
                new_custom_error_span(
                    format!("Invalid bitvector constant: {}", digits),
                    empty_span(),
                )
            })
    } else {
        num_bigint::BigUint::parse_bytes(digits.as_bytes(), radix)
            .map(|v| BitVec::from_biguint(v, bits))
            .ok_or_else(|| {
                new_custom_error_span(
                    format!("Invalid bitvector constant: {}", digits),
                    empty_span(),
                )
            })
    }
}

fn term_app(term: &SyGuSTerm) -> Option<(&str, &[SyGuSTerm])> {
    let SyGuSTerm::Application(id, args) = term else {
        return None;
    };
    Some((id.get_name(), args.as_slice()))
}

pub(crate) fn term_eq(term: &SyGuSTerm) -> Option<(&SyGuSTerm, &SyGuSTerm)> {
    let ("=", args) = term_app(term)? else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    Some((&args[0], &args[1]))
}

pub(crate) fn term_call_to<'a>(
    term: &'a SyGuSTerm,
    name: &str,
    arity: usize,
) -> Option<&'a [SyGuSTerm]> {
    let (head, args) = term_app(term)?;
    if head == name && args.len() == arity {
        Some(args)
    } else {
        None
    }
}

fn term_var_name(term: &SyGuSTerm) -> Option<&str> {
    let SyGuSTerm::Identifier(Identifier::Symbol(name)) = term else {
        return None;
    };
    Some(name)
}

// ---------------------------------------------------------------------------
//  `(_ extract hi lo)` parsing — used by both the bit-spec parser here and by
//  `exact::util::extract_single_bit_idx` (for LFP-side bit-label extraction).
// ---------------------------------------------------------------------------

fn numeral_index(idx: &Index) -> Option<usize> {
    match idx {
        Index::Numeral(v) => Some(*v),
        Index::Symbol(_) => None,
    }
}

pub fn extract_indices_from_identifier(id: &Identifier) -> Option<(usize, usize)> {
    let Identifier::Indexed(sym, idxs) = id else {
        return None;
    };
    if sym != "extract" || idxs.len() < 2 {
        return None;
    }
    match (numeral_index(&idxs[0]), numeral_index(&idxs[1])) {
        (Some(hi), Some(lo)) => Some((hi, lo)),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
//  Bit-extract / structural constraint parsing (consumed by `exact::Constraint`)
// ---------------------------------------------------------------------------

pub struct BitConstraintExample {
    pub args: Vec<BitVec>,
    pub known_bits: BTreeMap<usize, bool>,
}

/// Parse a nullary `(define-fun target () _ body)` whose body evaluates to a
/// concrete `BitVec` — the trivial-spec case for the exact engine.
pub fn parse_target_define_fun(
    file: &SyGuSFile,
    target_name: &str,
    arity: usize,
) -> Result<Option<BitVec>> {
    if arity != 0 {
        return Ok(None);
    }
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

/// Group `(constraint ...)` / `(assume ...)` commands into per-input bit
/// constraints. For nullary targets, also collects structural boolean
/// constraints over the synth value.
pub fn parse_bit_constraints_grouped(
    file: &SyGuSFile,
    target_name: &str,
    target_bits: usize,
    args: &[&str],
) -> Result<Option<(Vec<BitConstraintExample>, Vec<OwnedExpr>)>> {
    let arity = args.len();
    let mut example_map: Vec<(Vec<BitVec>, BTreeMap<usize, bool>)> = Vec::new();
    let mut structural = Vec::new();
    let synth_env: Vec<(&str, u64)> = if arity == 0 {
        vec![(target_name, target_bits as u64)]
    } else {
        vec![]
    };
    let mut found_any = false;

    for cmd in &file.cmds {
        let constraint_term = match cmd {
            SyGuSCmd::Constraint(c) => c,
            SyGuSCmd::Assume(c) => c,
            _ => continue,
        };

        if arity == 0 {
            if let Some(bits) = collect_bit_constraints(constraint_term, target_name) {
                for (bit, value) in bits {
                    if bit >= target_bits {
                        continue;
                    }
                    found_any = true;
                    let entry = example_map.iter_mut().find(|(a, _)| a.is_empty());
                    if let Some((_, known_bits)) = entry {
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
                    } else {
                        let mut known_bits = BTreeMap::new();
                        known_bits.insert(bit, value);
                        example_map.push((vec![], known_bits));
                    }
                }
            } else if constraint_mentions_target(constraint_term, target_name) {
                validate_structural_shape(constraint_term, target_name)?;
                let rewritten = rewrite_constraint_literals_for_owned_eval(constraint_term);
                structural.push(OwnedExpr::from_term(&rewritten, &synth_env)?);
                found_any = true;
            }
        } else if let Some((arg_values, bit, val)) =
            parse_extract_call_constraint(constraint_term, target_name, arity, target_bits)
        {
            found_any = true;
            let entry = example_map.iter_mut().find(|(a, _)| *a == arg_values);
            if let Some((_, known_bits)) = entry {
                if let Some(old) = known_bits.get(&bit).copied() {
                    if old != val {
                        return Err(new_custom_error_span(
                            format!(
                                "Conflicting constraints on bit {} of {}",
                                bit, target_name
                            ),
                            empty_span(),
                        ));
                    }
                } else {
                    known_bits.insert(bit, val);
                }
            } else {
                let mut known_bits = BTreeMap::new();
                known_bits.insert(bit, val);
                example_map.push((arg_values, known_bits));
            }
        }
    }

    if !found_any {
        return Ok(None);
    }
    let examples = example_map
        .into_iter()
        .map(|(args, known_bits)| BitConstraintExample { args, known_bits })
        .collect();
    Ok(Some((examples, structural)))
}

fn parse_extract_call_constraint(
    term: &SyGuSTerm,
    target_name: &str,
    arity: usize,
    target_bits: usize,
) -> Option<(Vec<BitVec>, usize, bool)> {
    if let SyGuSTerm::Annotated(inner, _) = term {
        return parse_extract_call_constraint(inner, target_name, arity, target_bits);
    }
    let SyGuSTerm::Application(op, args) = term else {
        return None;
    };
    if op.get_name() != "=" || args.len() != 2 {
        return None;
    }
    try_parse_extract_eq(&args[0], &args[1], target_name, arity, target_bits)
        .or_else(|| try_parse_extract_eq(&args[1], &args[0], target_name, arity, target_bits))
}

fn try_parse_extract_eq(
    extract_side: &SyGuSTerm,
    lit_side: &SyGuSTerm,
    target_name: &str,
    arity: usize,
    target_bits: usize,
) -> Option<(Vec<BitVec>, usize, bool)> {
    let SyGuSTerm::Application(extract_op, extract_args) = extract_side else {
        return None;
    };
    if extract_args.len() != 1 {
        return None;
    }
    let (hi, lo) = extract_indices_from_identifier(extract_op)?;
    if hi != lo || hi >= target_bits {
        return None;
    }
    let call = &extract_args[0];
    let SyGuSTerm::Application(call_op, call_args) = call else {
        return None;
    };
    if call_op.get_name() != target_name || call_args.len() != arity {
        return None;
    }
    let mut arg_values = Vec::with_capacity(arity);
    for arg in call_args {
        let SyGuSTerm::Literal(lit) = arg else {
            return None;
        };
        arg_values.push(literal_to_value(lit).ok()?);
    }
    let bit_val = bit_literal(lit_side)?;
    Some((arg_values, hi, bit_val))
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

fn validate_structural_shape(term: &SyGuSTerm, target: &str) -> Result<()> {
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

// ---------------------------------------------------------------------------
//  RefImplConstraint — symbolic reference implementation. CEGIS uses it both
//  to seed examples and to verify candidate equivalence via SMT.
// ---------------------------------------------------------------------------

#[derive(DebugCustom, Clone)]
#[debug(fmt = "{:?}", ref_impl)]
pub struct RefImplConstraint {
    pub args: usize,
    pub ref_impl: OwnedExpr,
}

impl RefImplConstraint {
    pub fn parse_from_file(
        file: &SyGuSFile,
        target_name: &str,
        target_arity: usize,
    ) -> Result<Option<Self>> {
        let view = ProblemView::from_file(file);
        Self::parse_from_view(&view, target_name, target_arity)
    }

    pub fn parse_from_view(
        view: &ProblemView<'_>,
        target_name: &str,
        target_arity: usize,
    ) -> Result<Option<Self>> {
        fn target_var_indices(args: &[SyGuSTerm], target_args: &[SortedVar]) -> Option<Vec<usize>> {
            let mut indices = Vec::with_capacity(args.len());
            for arg in args {
                let name = term_var_name(arg)?;
                let idx = target_args.iter().position(|v| v.name == name)?;
                indices.push(idx);
            }
            Some(indices)
        }

        fn helper_env_from_call(
            helper_formals: &[SortedVar],
            helper_call_args: &[SyGuSTerm],
            target_args: &[SortedVar],
        ) -> Option<Vec<(&'static str, u64)>> {
            if helper_formals.len() != helper_call_args.len() {
                return None;
            }
            let mapping = target_var_indices(helper_call_args, target_args)?;
            let mut env = target_args
                .iter()
                .map(|arg| {
                    let name =
                        Box::leak(format!("__unused_target_arg_{}", arg.name).into_boxed_str());
                    (name as &'static str, 64_u64)
                })
                .collect::<Vec<_>>();
            for (formal, target_idx) in helper_formals.iter().zip(mapping) {
                let name = Box::leak(formal.name.clone().into_boxed_str()) as &'static str;
                env[target_idx] = (name, 64);
            }
            Some(env)
        }

        for def in &view.define_funs {
            if def.name != target_name || def.args.len() != target_arity {
                continue;
            }
            let vargs: Vec<(&'static str, u64)> = def
                .args
                .iter()
                .map(|v| {
                    let name = Box::leak(v.name.clone().into_boxed_str()) as &'static str;
                    let bits = view.sort_aliases.parse_sort_width(&v.sort).unwrap_or(1) as u64;
                    (name, bits)
                })
                .collect();
            let e = OwnedExpr::from_term(def.body, &*vargs)?;
            return Ok(Some(Self {
                ref_impl: e,
                args: vargs.len(),
            }));
        }

        let Some(target_decl) = view
            .synth_funs
            .iter()
            .copied()
            .find(|synth| synth.name == target_name)
            .map(|synth| synth.args)
        else {
            return Ok(None);
        };

        for term in &view.constraints {
            let Some((lhs_eq, rhs_eq)) = term_eq(term) else {
                continue;
            };

            let mut candidate = None;
            for (lhs, rhs) in [(lhs_eq, rhs_eq), (rhs_eq, lhs_eq)] {
                let Some((rhs_name, rhs_args)) = term_app(rhs) else {
                    continue;
                };
                if rhs_name != target_name || rhs_args.len() != target_arity {
                    continue;
                }
                let expected = (0..target_decl.len()).collect::<Vec<_>>();
                if target_var_indices(rhs_args, target_decl).as_deref() != Some(expected.as_slice())
                {
                    continue;
                }
                let Some((helper_name, helper_call_args)) = term_app(lhs) else {
                    continue;
                };
                candidate = Some((helper_name, helper_call_args));
                break;
            }

            let Some((helper_name, helper_call_args)) = candidate else {
                continue;
            };

            for helper_def in &view.define_funs {
                if helper_def.name != helper_name {
                    continue;
                }
                let Some(env) =
                    helper_env_from_call(helper_def.args, helper_call_args, target_decl)
                else {
                    continue;
                };
                let e = OwnedExpr::from_term(helper_def.body, &env)?;
                return Ok(Some(Self {
                    ref_impl: e,
                    args: target_arity,
                }));
            }
        }

        Ok(None)
    }
    #[cfg(feature = "chatgpt")]
    pub fn generate_pbe(
        &self,
        count: usize,
        arity: usize,
        bits: usize,
        rng: &mut StdRng,
    ) -> Constraint {
        let mut res = Constraint::empty(arity, bits);
        for _ in 0..count {
            let mask = [
                u64::MAX,
                u64::MAX,
                u64::MAX,
                u64::MAX,
                0xFF,
                0xFFFFFFFFFFFF,
                0xFFFFFF0000FFFFFF,
            ]
            .choose(rng)
            .unwrap();
            res.random_example(rng, *mask, &self.ref_impl, arity)
        }
        res
    }
}

#[cfg(test)]
mod tests {
    use sygus_parser::ast::SyGuSFile;

    use crate::exact::Constraint;

    #[test]
    fn test_constraint() {
        let e = SyGuSFile::from_str(
            " (constraint (= (f #x1 #x2) #x3))
            (constraint (= (f #x1 #x2) #x3))
        ",
        )
        .unwrap();
        let spec = Constraint::parse_pbe_from_file("f", 2, 64, &e).unwrap();
        assert_eq!(spec.examples.len(), 2);
    }
}
