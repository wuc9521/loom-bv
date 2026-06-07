use std::collections::BTreeMap;

use sygus_parser::ast::SyGuSFile;

use crate::{
    enumerate::{expr::OwnedExpr, value::Value},
    exact::{
        relevance::{bits, Relevance},
        search::search_problem,
        types::ExactGrammar,
    },
    parse::{
        self,
        constraint::{
            parse_bit_constraints_grouped, parse_target_define_fun, BitConstraintExample,
        },
        SynthProblem,
    },
};

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
        if let Some((parsed, structural)) =
            parse_bit_constraints_grouped(file, problem.name, problem.bits, &problem.args)?
        {
            let examples = parsed
                .into_iter()
                .map(|BitConstraintExample { args, known_bits }| Example { args, known_bits })
                .collect();
            return Ok(Some(Self {
                bits: problem.bits,
                examples,
                structural,
                closure: None,
            }));
        }
        Ok(None)
    }

    pub fn from_labels(bits: usize, known_bits: BTreeMap<usize, bool>) -> Self {
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
