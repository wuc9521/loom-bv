use std::collections::BTreeMap;

use derive_more::DebugCustom;
use itertools::Itertools;
use rand::{rngs::StdRng, Rng};
use sdset::SetBuf;
use smallvec::SmallVec;
use sygus_parser::ast::{SyGuSFile, SyGuSTerm};

use crate::{
    enumerate::{
        expr::{Expr, OwnedExpr},
        value::BitVec,
        Bv,
    },
    exact::{
        relevance::{bits, Relevance},
        search::search_problem,
        types::Grammar,
    },
    parse::{
        self,
        constraint::{
            literal_to_value, parse_bit_constraints_grouped, parse_target_define_fun,
            term_call_to, term_eq, BitConstraintExample,
        },
        ProblemView, SynthProblem,
    },
};

/// One synthesis example: concrete arguments, the constrained output value,
/// and a mask telling which output bits are constrained.
///
/// PBE benchmarks have `mask = all-ones` (every output bit is fully
/// specified). Bit-extract benchmarks set only the asserted bits in `mask`
/// and leave the remaining `output` bits at zero — they are don't-cares.
#[derive(Clone)]
pub struct Example {
    pub args: Vec<BitVec>,
    pub output: BitVec,
    pub mask: BitVec,
}

impl Example {
    pub fn known_bits(&self) -> BTreeMap<usize, bool> {
        let mut out = BTreeMap::new();
        for bit in 0..self.mask.bits() {
            if self.mask.bit(bit) {
                out.insert(bit, self.output.bit(bit));
            }
        }
        out
    }
}

#[derive(Clone)]
pub struct ClosureInfo;

#[derive(DebugCustom, Clone)]
#[debug(fmt = "{} examples, bits={}", "examples.len()", bits)]
pub struct Constraint {
    pub bits: usize,
    pub args: usize,
    pub examples: Vec<Example>,
    pub structural: Vec<OwnedExpr>,
    pub closure: Option<ClosureInfo>,
}

fn all_ones(bits: usize) -> BitVec {
    if bits == 0 {
        BitVec::zero(0)
    } else {
        BitVec::zero(bits).bitnot()
    }
}

impl Constraint {
    pub fn empty(args: usize, bits: usize) -> Self {
        Self {
            bits,
            args,
            examples: Vec::new(),
            structural: Vec::new(),
            closure: None,
        }
    }

    pub fn from_pbe_parts(
        args: usize,
        bits: usize,
        input: Vec<Vec<BitVec>>,
        output: Vec<BitVec>,
        mask: Option<BitVec>,
    ) -> Self {
        let n = output.len();
        debug_assert_eq!(input.len(), args);
        debug_assert!(input.iter().all(|col| col.len() == n));
        let mask_value = mask.unwrap_or_else(|| all_ones(bits));
        let mut examples = Vec::with_capacity(n);
        for i in 0..n {
            let row: Vec<BitVec> = (0..args).map(|a| input[a][i].clone()).collect();
            examples.push(Example {
                args: row,
                output: output[i].clone(),
                mask: mask_value.clone(),
            });
        }
        Self {
            bits,
            args,
            examples,
            structural: Vec::new(),
            closure: None,
        }
    }

    pub fn from_file(
        file: &SyGuSFile,
        problem: &SynthProblem<'static>,
    ) -> parse::Result<Option<Self>> {
        if let Some(value) = parse_target_define_fun(file, problem.name, problem.args.len())? {
            let bits = problem.bits;
            return Ok(Some(Self {
                bits,
                args: problem.args.len(),
                examples: vec![Example {
                    args: vec![],
                    output: value,
                    mask: all_ones(bits),
                }],
                structural: vec![],
                closure: None,
            }));
        }
        if let Some((parsed, structural)) =
            parse_bit_constraints_grouped(file, problem.name, problem.bits, &problem.args)?
        {
            let bits = problem.bits;
            let examples = parsed
                .into_iter()
                .map(|BitConstraintExample { args, known_bits }| {
                    bit_constraint_example_to_example(args, known_bits, bits)
                })
                .collect();
            return Ok(Some(Self {
                bits,
                args: problem.args.len(),
                examples,
                structural,
                closure: None,
            }));
        }
        Ok(None)
    }

    pub fn parse_pbe_from_file(
        func: &str,
        arity: usize,
        bits: usize,
        file: &SyGuSFile,
    ) -> parse::Result<Self> {
        let view = ProblemView::from_file(file);
        Self::parse_pbe_from_view(func, arity, bits, &view)
    }

    pub fn parse_pbe_from_view(
        func: &str,
        arity: usize,
        bits: usize,
        view: &ProblemView<'_>,
    ) -> parse::Result<Self> {
        let mut spec = Self::empty(arity, bits);
        let full_mask = all_ones(bits);
        for value in &view.constraints {
            let Some((lhs, rhs)) = term_eq(value) else {
                continue;
            };
            let Some(args) = term_call_to(lhs, func, arity) else {
                continue;
            };
            let mut row = Vec::with_capacity(arity);
            for arg in args {
                let SyGuSTerm::Literal(lit) = arg else {
                    row.clear();
                    break;
                };
                row.push(literal_to_value(lit)?);
            }
            if row.len() != arity {
                continue;
            }
            let SyGuSTerm::Literal(lit) = rhs else {
                continue;
            };
            let output = literal_to_value(lit)?;
            spec.examples.push(Example {
                args: row,
                output,
                mask: full_mask.clone(),
            });
        }
        Ok(spec)
    }

    pub fn from_labels(bits: usize, known_bits: BTreeMap<usize, bool>) -> Self {
        let example = bit_constraint_example_to_example(vec![], known_bits, bits);
        Self {
            bits,
            args: 0,
            examples: vec![example],
            structural: vec![],
            closure: Some(ClosureInfo),
        }
    }

    pub fn label_indices(&self) -> Option<(Vec<usize>, Vec<usize>)> {
        if self.examples.len() != 1 {
            return None;
        }
        let known_bits = self.examples[0].known_bits();
        if known_bits.is_empty() {
            return None;
        }
        let mut pos = Vec::new();
        let mut neg = Vec::new();
        for (idx, expected) in known_bits {
            if expected {
                pos.push(idx);
            } else {
                neg.push(idx);
            }
        }
        Some((pos, neg))
    }

    pub fn matches(&self, values: &[BitVec]) -> bool {
        debug_assert_eq!(values.len(), self.examples.len());
        for (example, value) in self.examples.iter().zip(values.iter()) {
            if value.bits() != self.bits {
                return false;
            }
            if !value.matches_masked(&example.output, &example.mask) {
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
            for (bit, val) in example.known_bits() {
                union.entry(bit).or_insert(val);
            }
        }
        union
    }

    pub fn num_examples(&self) -> usize {
        self.examples.len()
    }

    pub fn len(&self) -> usize {
        self.examples.len()
    }

    pub fn args_count(&self) -> usize {
        self.args
    }

    pub fn is_fully_specified(&self) -> bool {
        let full = all_ones(self.bits);
        self.examples.iter().all(|e| e.mask == full)
    }

    pub fn args(&self, i: usize) -> SmallVec<[BitVec; 4]> {
        self.examples[i].args.iter().cloned().collect()
    }

    pub fn bv_from_slice<const N: usize>(&self, iter: &[usize; N]) -> (Vec<Bv<N>>, Bv<N>) {
        let inputs: Vec<Bv<N>> = (0..self.args)
            .map(|arg_idx| {
                Bv(iter
                    .map(|i| self.examples[i].args[arg_idx].as_u64_lossy())
                    .into())
            })
            .collect();
        let output = Bv(iter.map(|i| self.examples[i].output.as_u64_lossy()).into());
        (inputs, output)
    }

    pub fn test(&self, expr: &Expr) -> SetBuf<usize> {
        SetBuf::new_unchecked(
            (0..self.len())
                .flat_map(|i| {
                    let ex = &self.examples[i];
                    let ok = expr
                        .eval(self.args(i).as_slice())
                        .map(|x| {
                            x.bitxor(ex.output.clone())
                                .bitand(ex.mask.clone())
                                .is_zero()
                        })
                        .unwrap_or(false);
                    ok.then_some(i)
                })
                .collect(),
        )
    }

    #[cfg(feature = "chatgpt")]
    pub fn test_owned(&self, expr: &OwnedExpr) -> SetBuf<usize> {
        SetBuf::new_unchecked(
            (0..self.len())
                .flat_map(|i| {
                    let ex = &self.examples[i];
                    let ok = expr
                        .eval(self.args(i).as_slice())
                        .map(|x| {
                            x.bitxor(ex.output.clone())
                                .bitand(ex.mask.clone())
                                .is_zero()
                        })
                        .unwrap_or(false);
                    ok.then_some(i)
                })
                .collect(),
        )
    }

    pub fn test_and(&self, expr: &Expr) -> bool {
        (0..self.len()).all(|i| {
            let ex = &self.examples[i];
            expr.eval(self.args(i).as_slice())
                .map(|x| ex.output.clone().bitand(x.bitnot()).is_zero())
                .unwrap_or(false)
        })
    }

    pub fn test_or(&self, expr: &Expr) -> bool {
        (0..self.len()).all(|i| {
            let ex = &self.examples[i];
            expr.eval(self.args(i).as_slice())
                .map(|x| ex.output.clone().bitnot().bitand(x).is_zero())
                .unwrap_or(false)
        })
    }

    /// Replace every example's output (and mask) with `value`. Used by the
    /// condition-search worker, which searches for boolean predicates whose
    /// output is the constant `0`.
    pub fn set_output(mut self, value: BitVec) -> Self {
        let mask = all_ones(value.bits());
        self.bits = value.bits();
        for ex in &mut self.examples {
            ex.output = value.clone();
            ex.mask = mask.clone();
        }
        self
    }

    pub fn add_example(&mut self, args: &[BitVec], output: BitVec) {
        let mask = all_ones(output.bits());
        self.examples.push(Example {
            args: args.to_vec(),
            output,
            mask,
        });
    }

    pub fn random_example(
        &mut self,
        rng: &mut StdRng,
        randmask: u64,
        expr: &OwnedExpr,
        len: usize,
    ) {
        loop {
            let args = (0..len)
                .map(|_| BitVec::from_u64(rng.gen::<u64>() & randmask, 64))
                .collect_vec();
            if let Ok(a) = expr.eval(&*args) {
                self.add_example(&args, a);
                break;
            }
        }
    }

    #[cfg(feature = "chatgpt")]
    pub fn fmt(&self, arity: usize) -> String {
        let iter = self.examples.iter().map(|ex| {
            (
                (0..arity).map(|i| ex.args[i].clone()).collect_vec(),
                ex.output.clone(),
            )
        });
        let mut siter = iter.map(|(v, o)| {
            format!(
                "({}) -> {}",
                v.iter().map(|j| format!("{}", j)).join(", "),
                o
            )
        });
        format!("Here are some examples:\n{}", siter.join("\n"))
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
        grammar: &Grammar<'_>,
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

fn bit_constraint_example_to_example(
    args: Vec<BitVec>,
    known_bits: BTreeMap<usize, bool>,
    bits: usize,
) -> Example {
    let mut output_raw = num_bigint::BigUint::ZERO;
    let mut mask_raw = num_bigint::BigUint::ZERO;
    for (&bit, &val) in &known_bits {
        mask_raw |= num_bigint::BigUint::from(1u64) << bit;
        if val {
            output_raw |= num_bigint::BigUint::from(1u64) << bit;
        }
    }
    Example {
        args,
        output: BitVec::from_biguint(output_raw, bits),
        mask: BitVec::from_biguint(mask_raw, bits),
    }
}
