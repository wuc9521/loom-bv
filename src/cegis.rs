use itertools::Itertools;
use rsmt2::{
    print::{IdentParser, ModelParser},
    SmtConf, SmtRes,
};
// use z3::{ast::Ast, Symbol};

use crate::{
    enumerate::{expr::OwnedExpr, utils::run_with_timeout, value::Value},
    info,
    parse::{constraint::RefImplConstraint, literals, PbeConstraint},
};

pub struct CegisState {
    pub examples: PbeConstraint,
    constraint: RefImplConstraint,
    bits: usize,
    conf: SmtConf,
}

impl CegisState {
    pub fn new(args: usize, bits: usize, refimpl: RefImplConstraint, conf: SmtConf) -> Self {
        Self {
            examples: PbeConstraint::new(args),
            constraint: refimpl,
            bits,
            conf,
        }
    }

    pub fn verify(&mut self, expr: &OwnedExpr) -> bool {
        let mut solver = self.conf.clone().spawn(Parser).unwrap();
        solver.set_logic(rsmt2::Logic::QF_BV).unwrap();
        for i in 0..self.constraint.args {
            solver
                .declare_const(VAR_NAMES[i], &format!("(_ BitVec {})", self.bits))
                .unwrap();
        }
        let s = format!("(not (= {} {}))", self.constraint.ref_impl, expr);
        // println!("{}", s);
        solver.assert(s).unwrap();

        loop {
            let a = run_with_timeout(10, {
                let s = unsafe { you_can::borrow_unchecked(&mut solver) };
                move || s.check_sat()
            });
            if let Some(Ok(true)) = a {
                let model = solver.get_model().unwrap();
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
                    return false;
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
                    solver.assert(statement).unwrap();
                }
            } else {
                return true;
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
