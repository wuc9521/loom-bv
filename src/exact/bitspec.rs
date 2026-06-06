use std::collections::BTreeMap;

use sygus_parser::ast::{Identifier, Literal as SyGuSLiteral, SyGuSCmd, SyGuSFile, SyGuSTerm};

use crate::{
    enumerate::{expr::OwnedExpr, value::Value},
    exact::{
        relevance::{bits, Relevance},
        search::search_problem,
        types::ExactGrammar,
        util::empty_span,
    },
    parse::{self, new_custom_error_span, SynthProblem},
};

use crate::exact::util::extract_indices_from_identifier;

pub struct BitSpec {
    pub bits: usize,
    pub examples: Vec<Example>,
    pub structural: Vec<OwnedExpr>,
    pub closure: Option<ClosureInfo>,
}

pub struct Example {
    pub args: Vec<Value>,
    pub known_bits: BTreeMap<usize, bool>,
}

pub struct ClosureInfo;

impl BitSpec {
    pub fn from_file(
        file: &SyGuSFile,
        problem: &SynthProblem<'static>,
    ) -> parse::Result<Option<Self>> {
        if let Some(value) = parse_target_define_fun(file, problem.name, problem.args.len())? {
            let mut known_bits = BTreeMap::new();
            for bit in 0..value.bits() {
                known_bits.insert(bit, value.bit(bit));
            }
            return Ok(Some(Self {
                bits: problem.bits,
                examples: vec![Example {
                    args: vec![],
                    known_bits,
                }],
                structural: vec![],
                closure: None,
            }));
        }
        if let Some((examples, structural)) =
            parse_bit_constraints_grouped(file, problem.name, problem.bits, &problem.args)?
        {
            return Ok(Some(Self {
                bits: problem.bits,
                examples,
                structural,
                closure: None,
            }));
        }
        Ok(None)
    }

    pub fn from_labels(
        bits: usize,
        known_bits: BTreeMap<usize, bool>,
    ) -> Self {
        Self {
            bits,
            examples: vec![Example {
                args: vec![],
                known_bits,
            }],
            structural: vec![],
            closure: Some(ClosureInfo),
        }
    }

    pub fn label_indices(&self) -> Option<(Vec<usize>, Vec<usize>)> {
        if self.examples.len() != 1 {
            return None;
        }
        let known_bits = &self.examples[0].known_bits;
        if known_bits.is_empty() {
            return None;
        }
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

    pub fn matches(&self, values: &[Value]) -> bool {
        debug_assert_eq!(values.len(), self.examples.len());
        for (example, value) in self.examples.iter().zip(values.iter()) {
            if value.bits() != self.bits {
                return false;
            }
            if !example
                .known_bits
                .iter()
                .all(|(bit, expected)| value.bit(*bit) == *expected)
            {
                return false;
            }
        }
        self.structural.iter().all(|expr| {
            expr.eval(values)
                .map(|v| v.as_bool().holds())
                .unwrap_or(false)
        })
    }

    pub fn demanded_bits(&self) -> BTreeMap<usize, bool> {
        let mut union = BTreeMap::new();
        for example in &self.examples {
            for (bit, val) in &example.known_bits {
                union.entry(*bit).or_insert(*val);
            }
        }
        union
    }

    pub fn num_examples(&self) -> usize {
        self.examples.len()
    }

    pub fn search(
        &self,
        problem: &SynthProblem<'static>,
        min: bool,
        fixpoint: Option<&str>,
    ) -> parse::Result<OwnedExpr> {
        search_problem(problem, self, min, fixpoint)
    }

    pub fn compute_relevant_bits(
        &self,
        grammar: &ExactGrammar<'_>,
    ) -> Option<Vec<Vec<usize>>> {
        if !self.structural.is_empty() {
            return None;
        }
        let demanded = self.demanded_bits();
        if demanded.is_empty() {
            return None;
        }
        let mut lazy = Relevance::new(grammar, self.bits, &demanded)?;
        if self.closure.is_some() {
            lazy.closure_param = Some(0);
            lazy.closure_relevant = Some(bits::BitSet::new(self.bits));
        }
        while !lazy.advance(1024) {}
        lazy.finish()
    }
}

fn parse_target_define_fun(
    file: &SyGuSFile,
    target_name: &str,
    arity: usize,
) -> parse::Result<Option<Value>> {
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

fn parse_bit_constraints_grouped(
    file: &SyGuSFile,
    target_name: &str,
    target_bits: usize,
    args: &[&str],
) -> parse::Result<Option<(Vec<Example>, Vec<OwnedExpr>)>> {
    let arity = args.len();
    let mut example_map: Vec<(Vec<Value>, BTreeMap<usize, bool>)> = Vec::new();
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
                    let entry = example_map
                        .iter_mut()
                        .find(|(a, _)| a.is_empty());
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
                let rewritten =
                    rewrite_constraint_literals_for_owned_eval(constraint_term);
                structural.push(OwnedExpr::from_term(&rewritten, &synth_env)?);
                found_any = true;
            }
        } else {
            if let Some((arg_values, bit, val)) =
                parse_extract_call_constraint(constraint_term, target_name, arity, target_bits)
            {
                found_any = true;
                let entry = example_map
                    .iter_mut()
                    .find(|(a, _)| *a == arg_values);
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
    }

    if !found_any {
        return Ok(None);
    }
    let examples = example_map
        .into_iter()
        .map(|(args, known_bits)| Example { args, known_bits })
        .collect();
    Ok(Some((examples, structural)))
}

/// Parse `(= ((_ extract i i) (f lit_1 ... lit_n)) #b0/#b1)` for non-nullary,
/// or `(= ((_ extract i i) (f lit_1 ... lit_n)) #b0/#b1)` with negation.
/// Returns (arg_values, bit_index, bit_value).
fn parse_extract_call_constraint(
    term: &SyGuSTerm,
    target_name: &str,
    arity: usize,
    target_bits: usize,
) -> Option<(Vec<Value>, usize, bool)> {
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
) -> Option<(Vec<Value>, usize, bool)> {
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
        arg_values.push(literal_to_value(lit)?);
    }
    let bit_val = bit_literal(lit_side)?;
    Some((arg_values, hi, bit_val))
}

fn literal_to_value(lit: &SyGuSLiteral) -> Option<Value> {
    match lit {
        SyGuSLiteral::Numeral(v) => Some(Value::from_u64(*v as u64, 64)),
        SyGuSLiteral::Bool(v) => Some(Value::from_u64(if *v { 1 } else { 0 }, 1)),
        SyGuSLiteral::HexConst(v) => {
            let trimmed = v.trim_start_matches("#x");
            let bits = trimmed.len() * 4;
            let big = num_bigint::BigUint::parse_bytes(trimmed.as_bytes(), 16)?;
            Some(Value::from_biguint(big, bits.max(1)))
        }
        SyGuSLiteral::BinConst(v) => {
            let trimmed = v.trim_start_matches("#b");
            let bits = trimmed.len();
            let big = num_bigint::BigUint::parse_bytes(trimmed.as_bytes(), 2)?;
            Some(Value::from_biguint(big, bits.max(1)))
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------------
//  Shared parsing helpers (kept from spec.rs for nullary path)
// ---------------------------------------------------------------------------

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
