use itertools::Itertools;
use rand::{rngs::StdRng, Rng};
use sdset::SetBuf;

use derive_more::DebugCustom;
use smallvec::SmallVec;
use sygus_parser::ast::{SyGuSFile, SyGuSTerm};

use crate::enumerate::{
    expr::{Expr, OwnedExpr},
    value::Value,
    Bv,
};

use super::super::{Error, ProblemView};
use super::{literal_to_value, term_call_to, term_eq};

#[derive(DebugCustom, Clone)]
#[debug(fmt = "{:#x?} -> {:#x?}", input, output)]
pub struct PbeConstraint {
    input: Vec<Vec<Value>>,
    output: Vec<Value>,
}

impl PbeConstraint {
    pub fn new(args: usize) -> Self {
        Self {
            input: (0..args).map(|_| Vec::new()).collect(),
            output: Vec::new(),
        }
    }
    pub fn len(&self) -> usize {
        self.output.len()
    }
    pub fn args_count(&self) -> usize {
        self.input.len()
    }
    pub fn parse_from_file(func: &str, arity: usize, file: &SyGuSFile) -> Result<Self, Error> {
        let view = ProblemView::from_file(file);
        Self::parse_from_view(func, arity, &view)
    }

    pub fn parse_from_view(
        func: &str,
        arity: usize,
        view: &ProblemView<'_>,
    ) -> Result<Self, Error> {
        let mut input: Vec<Vec<Value>> = (0..arity).map(|_| Vec::new()).collect();
        let mut output = Vec::new();
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
            for (value, vec) in row.into_iter().zip(input.iter_mut()) {
                vec.push(value);
            }
            output.push(literal_to_value(lit)?);
        }
        Ok(PbeConstraint { input, output })
    }

    pub fn bv_from_slice<const N: usize>(&self, iter: &[usize; N]) -> (Vec<Bv<N>>, Bv<N>) {
        (
            self.input
                .iter()
                .map(|x| Bv(iter.map(|i| x[i].as_u64_lossy()).into()))
                .collect(),
            Bv(iter.map(|i| self.output[i].as_u64_lossy()).into()),
        )
    }
    pub fn args(&self, i: usize) -> SmallVec<[Value; 4]> {
        self.input.iter().map(|x| x[i].clone()).collect()
    }
    pub fn test(&self, expr: &Expr) -> sdset::SetBuf<usize> {
        SetBuf::new_unchecked(
            (0..self.len())
                .into_iter()
                .flat_map(|i| {
                    if expr
                        .eval(self.args(i).as_slice())
                        .map(|x| x == self.output[i].clone())
                        .unwrap_or(false)
                    {
                        Some(i)
                    } else {
                        None
                    }
                })
                .collect(),
        )
    }
    #[cfg(feature = "chatgpt")]
    pub fn test_owned(&self, expr: &OwnedExpr) -> sdset::SetBuf<usize> {
        SetBuf::new_unchecked(
            (0..self.len())
                .into_iter()
                .flat_map(|i| {
                    if expr
                        .eval(self.args(i).as_slice())
                        .map(|x| x == self.output[i].clone())
                        .unwrap_or(false)
                    {
                        Some(i)
                    } else {
                        None
                    }
                })
                .collect(),
        )
    }
    pub fn test_and(&self, expr: &Expr) -> bool {
        (0..self.len()).into_iter().all(|i| {
            expr.eval(self.args(i).as_slice())
                .map(|x| self.output[i].clone().bitand(x.bitnot()).is_zero())
                .unwrap_or(false)
        })
    }
    pub fn test_or(&self, expr: &Expr) -> bool {
        (0..self.len()).into_iter().all(|i| {
            expr.eval(self.args(i).as_slice())
                .map(|x| self.output[i].clone().bitnot().bitand(x).is_zero())
                .unwrap_or(false)
        })
    }

    pub fn set_output(mut self, value: Value) -> Self {
        self.output.iter_mut().for_each(|x| *x = value.clone());
        self
    }
    pub fn add_example(&mut self, input: &[Value], output: Value) {
        self.input
            .iter_mut()
            .zip(input.iter())
            .for_each(|(x, p)| x.push(p.clone()));
        self.output.push(output)
    }
    pub fn random_example(&mut self, rng: &mut StdRng, mask: u64, expr: &OwnedExpr, len: usize) {
        loop {
            let args = (0..len)
                .map(|_| Value::from_u64(rng.gen::<u64>() & mask, 64))
                .collect_vec();
            if let Ok(a) = expr.eval(&*args) {
                self.add_example(&args, a);
                break;
            }
        }
    }
    #[cfg(feature = "chatgpt")]
    pub fn fmt(&self, arity: usize) -> String {
        let iter = (0..self.output.len()).map(|x| {
            (
                (0..arity).map(|i| self.input[i][x].clone()).collect_vec(),
                self.output[x].clone(),
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
}

#[cfg(test)]
mod tests {
    use sygus_parser::ast::SyGuSFile;

    use super::PbeConstraint;

    #[test]
    fn test_constraint() {
        let e = SyGuSFile::from_str(
            " (constraint (= (f #x1 #x2) #x3))
            (constraint (= (f #x1 #x2) #x3))
        ",
        )
        .unwrap();
        let contraint = PbeConstraint::parse_from_file("f", 2, &e).unwrap();
        println!("{:?}", contraint);
    }
}
