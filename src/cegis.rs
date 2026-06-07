use itertools::Itertools;
use rsmt2::{
    print::{IdentParser, ModelParser},
    SmtConf, SmtRes,
};
// use z3::{ast::Ast, Symbol};

use crate::{
    enumerate::{expr::OwnedExpr, utils::run_with_timeout, value::Value},
    exact::Constraint,
    info,
    parse::{constraint::RefImplConstraint, literals},
};

pub struct CegisState {
    pub examples: Constraint,
    constraint: RefImplConstraint,
    bits: usize,
    conf: SmtConf,
}

impl CegisState {
    pub fn new(args: usize, bits: usize, refimpl: RefImplConstraint, conf: SmtConf) -> Self {
        Self {
            examples: Constraint::empty(args, bits),
            constraint: refimpl,
            bits,
            conf,
        }
    }

    pub fn verify(&mut self, expr: &OwnedExpr) -> Result<bool, String> {
        let mut solver = self
            .conf
            .clone()
            .spawn(Parser)
            .map_err(|e| format!("failed to spawn verifier solver: {e}"))?;
        solver
            .set_logic(rsmt2::Logic::QF_BV)
            .map_err(|e| format!("failed to set verifier logic: {e}"))?;
        for i in 0..self.constraint.args {
            solver
                .declare_const(VAR_NAMES[i], &format!("(_ BitVec {})", self.bits))
                .map_err(|e| format!("failed to declare verifier var {}: {e}", VAR_NAMES[i]))?;
        }
        let arg_names: Vec<&str> = VAR_NAMES[..self.constraint.args].to_vec();
        let refimpl_smt = self.constraint.ref_impl.to_sygus(&arg_names);
        let expr_smt = expr.to_sygus(&arg_names);
        let s = if self.bits == 1 {
            format!("(not (= {} (= {} #b0)))", refimpl_smt, expr_smt)
        } else {
            format!("(not (= {} {}))", refimpl_smt, expr_smt)
        };
        solver
            .assert(s)
            .map_err(|e| format!("failed to assert verifier constraint: {e}"))?;

        loop {
            let a = run_with_timeout(10, {
                let s = unsafe { you_can::borrow_unchecked(&mut solver) };
                move || s.check_sat()
            });
            match a {
                Some(Ok(true)) => {
                let model = solver
                    .get_model()
                    .map_err(|e| format!("failed to read verifier model: {e}"))?;
                let mut args = (0..self.constraint.args)
                    .map(|_| Value::zero(self.bits))
                    .collect_vec();
                for (name, _, _, value) in model.into_iter() {
                    let value = literals::value_constant(
                        &value,
                        self.bits,
                        pest::Span::new("", 0, 0).unwrap(),
                    )
                    .unwrap_or_else(|_| Value::zero(self.bits));
                    let index = VAR_NAMES
                        .iter()
                        .enumerate()
                        .find(|(_i, x)| x == &&&name)
                        .unwrap()
                        .0;
                    args[index] = value;
                }
                if let Ok(out) = self.constraint.ref_impl.eval(&*args) {
                    self.examples.add_example(&*args, out.clone());
                    info!("{:?} can not be verified. {:?} -> {}", expr, args, out);
                    return Ok(false);
                } else {
                    let statement = if let [a] = &*args {
                        format!("(distinct v0 {})", a.to_smt_hex())
                    } else {
                        format!(
                            "(not (and {}))",
                            args.iter()
                                .enumerate()
                                .map(|(i, x)| format!("(= {} {})", VAR_NAMES[i], x.to_smt_hex()))
                                .join(" ")
                        )
                    };
                    solver
                        .assert(statement)
                        .map_err(|e| format!("failed to refine verifier constraint: {e}"))?;
                }
                }
                Some(Ok(false)) => return Ok(true),
                Some(Err(e)) => return Err(format!("verifier solver check_sat failed: {e}")),
                None => return Err("verifier solver timed out".into()),
            }
        }
    }
}

const VAR_NAMES: [&'static str; 11] = [
    "v0", "v1", "v2", "v3", "v4", "v5", "v6", "v7", "v8", "v9", "v10",
];

#[derive(Clone, Copy)]
struct Parser;

impl<'a> IdentParser<String, String, &'a str> for Parser {
    fn parse_ident(self, input: &'a str) -> SmtRes<String> {
        Ok(input.into())
    }
    fn parse_type(self, input: &'a str) -> SmtRes<String> {
        Ok(input.into())
    }
}

impl<'a> ModelParser<String, String, String, &'a str> for Parser {
    fn parse_value(
        self,
        input: &'a str,
        _ident: &String,
        _params: &[(String, String)],
        _typ: &String,
    ) -> SmtRes<String> {
        Ok(input.into())
    }
}
