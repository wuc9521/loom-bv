use itertools::Itertools;
use pest::Span;
use rand::{rngs::StdRng, Rng};
use sdset::SetBuf;

use derive_more::DebugCustom;
use smallvec::SmallVec;
use sygus_parser::ast::{Identifier, Literal as SyGuSLiteral, SyGuSCmd, SyGuSFile, SyGuSTerm};

use crate::enumerate::{
    expr::{Expr, OwnedExpr},
    value::Value,
    Bv,
};

use super::super::{literals, new_custom_error_span, Error};

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
        fn empty_span() -> Span<'static> {
            Span::new("", 0, 0).expect("empty span should be valid")
        }
        fn id_name(id: &Identifier) -> &str {
            id.get_name()
        }
        fn lit_to_value(lit: &SyGuSLiteral) -> Result<Value, Error> {
            match lit {
                SyGuSLiteral::Numeral(v) => Ok(Value::from_u64(*v as u64, 64)),
                SyGuSLiteral::Bool(v) => Ok(Value::from_u64(if *v { 1 } else { 0 }, 1)),
                SyGuSLiteral::HexConst(v) => {
                    let s = if v.starts_with("#x") {
                        v.clone()
                    } else {
                        format!("#x{}", v)
                    };
                    let bits = v.trim_start_matches("#x").len() * 4;
                    literals::value_constant(&s, bits.max(1), empty_span())
                }
                SyGuSLiteral::BinConst(v) => {
                    let s = if v.starts_with("#b") {
                        v.clone()
                    } else {
                        format!("#b{}", v)
                    };
                    let bits = v.trim_start_matches("#b").len();
                    literals::value_constant(&s, bits.max(1), empty_span())
                }
                SyGuSLiteral::Decimal(_) | SyGuSLiteral::StringConst(_) => {
                    Err(new_custom_error_span(
                        "PBEConstraint: Expecting Constant.".into(),
                        empty_span(),
                    ))
                }
            }
        }

        let mut input: Vec<Vec<Value>> = (0..arity).map(|_| Vec::new()).collect();
        let mut output = Vec::new();
        for cmd in &file.cmds {
            if let SyGuSCmd::Constraint(value) = cmd {
                if let SyGuSTerm::Application(eq, eq_args) = value {
                    if id_name(eq) != "=" || eq_args.len() != 2 {
                        return Err(new_custom_error_span(
                            "PBEConstraint: Expecting Input-Output Examples (= (<func> <arg1> ...) <output>).".into(),
                            empty_span(),
                        ));
                    }
                    let l = &eq_args[0];
                    let r = &eq_args[1];
                    if let SyGuSTerm::Application(fid, args) = l {
                        if id_name(fid) == func && args.len() == arity {
                            for (arg, vec) in args.iter().zip(input.iter_mut()) {
                                if let SyGuSTerm::Literal(lit) = arg {
                                    vec.push(lit_to_value(lit)?);
                                } else {
                                    return Err(new_custom_error_span(
                                        "PBEConstraint: Expecting Constant for input.".into(),
                                        empty_span(),
                                    ));
                                }
                            }
                            if let SyGuSTerm::Literal(lit) = r {
                                output.push(lit_to_value(lit)?);
                            } else {
                                return Err(new_custom_error_span(
                                    "PBEConstraint: Expecting Constant for output.".into(),
                                    empty_span(),
                                ));
                            }
                        }
                    } else {
                        return Err(new_custom_error_span(
                            "PBEConstraint: Expecting Input Examples.".into(),
                            empty_span(),
                        ));
                    }
                } else {
                    return Err(new_custom_error_span(
                        "PBEConstraint: Expecting Input-Output Examples (= (<func> <arg1> ...) <output>).".into(),
                        empty_span(),
                    ));
                }
            }
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
