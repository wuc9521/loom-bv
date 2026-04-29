use crate::enumerate::value::Value;
use crate::parse::{self, cfg::NonTerminal, deffun, literals, new_custom_error_span, SynthProblem};
use pest::Span;
use sygus_parser::ast::{Identifier, Literal as SyGuSLiteral, SyGuSGTerm, SyGuSTerm};

use super::expr::OwnedExpr;
use derive_more::{Deref, From};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Rule<const N: usize> {
    Var(usize),
    Const(Value),
    Fop0(usize),
    Fop1(usize),
    Fop2(usize),
    ChatGPT(OwnedExpr, usize),
    LShrC(u64),
    ShlC(u64),
    Not,
    Neg,
    Add,
    Xor,
    And,
    Or,
    Sub,
    Mul,
    UDiv,
    LShr,
    Shl,
    SDiv,
    URem,
    SRem,
    AShr,
    Ite,
}

impl<const N: usize> Rule<N> {
    pub fn is_atom(&self) -> bool {
        match self {
            Rule::Var(_) | Rule::Const(_) | Rule::Fop0(_) => true,
            _ => false,
        }
    }
    pub fn is_shift(&self) -> bool {
        match self {
            Rule::Shl | Rule::AShr | Rule::LShr => true,
            _ => false,
        }
    }
}

#[macro_export]
macro_rules! generate_rules_matching {
    ($rules:expr) => {
        match $rules {
            Rule::Not => {
                generate_op!(op1, |e1| Expr::Not(e1), $crate::bv_op_of!(Not));
            }
            Rule::Neg => {
                generate_op!(op1, |e1| Expr::Neg(e1), $crate::bv_op_of!(Neg));
            }
            Rule::LShrC(v) => {
                generate_op!(
                    op1_constant,
                    |e1, e2| Expr::LShr(e1, e2),
                    $crate::bv_op_of!(LShr),
                    *v
                );
            }
            Rule::ChatGPT(e, v) => {
                generate_op!(chatgpt, e, v);
            }
            Rule::ShlC(v) => {
                generate_op!(
                    op1_constant,
                    |e1, e2| Expr::Shl(e1, e2),
                    $crate::bv_op_of!(Shl),
                    *v
                );
            }
            Rule::Add => {
                generate_op!(op2_sym, |e1, e2| Expr::Add(e1, e2), $crate::bv_op_of!(Add));
            }
            Rule::Xor => {
                generate_op!(op2_sym, |e1, e2| Expr::Xor(e1, e2), $crate::bv_op_of!(Xor));
            }
            Rule::And => {
                generate_op!(op2_sym, |e1, e2| Expr::And(e1, e2), $crate::bv_op_of!(And));
            }
            Rule::Or => {
                generate_op!(op2_sym, |e1, e2| Expr::Or(e1, e2), $crate::bv_op_of!(Or));
            }
            Rule::Mul => {
                generate_op!(op2_sym, |e1, e2| Expr::Mul(e1, e2), $crate::bv_op_of!(Mul));
            }
            Rule::Sub => {
                generate_op!(op2, |e1, e2| Expr::Sub(e1, e2), $crate::bv_op_of!(Sub));
            }
            Rule::UDiv => {
                generate_op!(
                    op2_nonzero,
                    |e1, e2| Expr::UDiv(e1, e2),
                    $crate::bv_op_of!(UDiv)
                );
            }
            Rule::LShr => {
                generate_op!(op2, |e1, e2| Expr::LShr(e1, e2), $crate::bv_op_of!(LShr));
            }
            Rule::Shl => {
                generate_op!(op2, |e1, e2| Expr::Shl(e1, e2), $crate::bv_op_of!(Shl));
            }
            Rule::SDiv => {
                generate_op!(
                    op2_nonzero,
                    |e1, e2| Expr::SDiv(e1, e2),
                    $crate::bv_op_of!(SDiv)
                );
            }
            Rule::URem => {
                generate_op!(
                    op2_nonzero,
                    |e1, e2| Expr::URem(e1, e2),
                    $crate::bv_op_of!(URem)
                );
            }
            Rule::SRem => {
                generate_op!(
                    op2_nonzero,
                    |e1, e2| Expr::SRem(e1, e2),
                    $crate::bv_op_of!(SRem)
                );
            }
            Rule::AShr => {
                generate_op!(op2, |e1, e2| Expr::AShr(e1, e2), $crate::bv_op_of!(AShr));
            }
            Rule::Var(id) => {
                generate_op!(var, id);
            }
            Rule::Fop0(id) => {
                generate_op!(op0, id);
            }
            Rule::Fop1(id) => match id {
                _ => {
                    generate_op!(op1, |e1| Expr::Fop1Dyn(*id, e1), |v1| {
                        crate::parse::deffun::ENV.apply(*id, 1).eval_bv(&[v1])
                    });
                }
            },
            Rule::Fop2(id) => match id {
                _ => {
                    generate_op!(
                        op2_nonzero,
                        |e1, e2| Expr::Fop2Dyn(*id, e1, e2),
                        |v1, v2| crate::parse::deffun::ENV.apply(*id, 2).eval_bv(&[v1, v2])
                    );
                }
            },
            Rule::Const(value) => {
                generate_op!(const, value);
            }
            Rule::Ite => {
                generate_op!(ite);
            }
        }
    };
}

#[derive(From, Debug, Deref, Clone)]
pub struct Config<const N: usize>(pub Vec<Rule<N>>);

impl<const N: usize> Config<N> {
    pub fn from_problem(
        problem: &SynthProblem<'_>,
        _partial_solution: bool,
    ) -> parse::Result<Self> {
        fn empty_span() -> Span<'static> {
            Span::new("", 0, 0).expect("empty span should be valid")
        }
        fn id_name(id: &Identifier) -> &str {
            id.get_name()
        }
        fn term_symbol(term: &SyGuSTerm) -> Option<&str> {
            if let SyGuSTerm::Identifier(id) = term {
                Some(id_name(id))
            } else {
                None
            }
        }
        fn term_value(term: &SyGuSTerm, bits: usize) -> Option<parse::Result<Value>> {
            match term {
                SyGuSTerm::Identifier(id) => {
                    let name = id_name(id);
                    if name.eq_ignore_ascii_case("true") {
                        Some(Ok(Value::from_u64(1, 1)))
                    } else if name.eq_ignore_ascii_case("false") {
                        Some(Ok(Value::from_u64(0, 1)))
                    } else if name.starts_with("#x") {
                        let w = name.trim_start_matches("#x").len() * 4;
                        Some(literals::value_constant(name, w.max(1), empty_span()))
                    } else if name.starts_with("#b") {
                        let w = name.trim_start_matches("#b").len();
                        Some(literals::value_constant(name, w.max(1), empty_span()))
                    } else if name.starts_with("#d") {
                        Some(literals::value_constant(name, bits.max(1), empty_span()))
                    } else {
                        None
                    }
                }
                SyGuSTerm::Literal(lit) => Some(match lit {
                    SyGuSLiteral::Numeral(v) => Ok(Value::from_u64(*v as u64, bits)),
                    SyGuSLiteral::Bool(v) => Ok(Value::from_u64(if *v { 1 } else { 0 }, 1)),
                    SyGuSLiteral::HexConst(v) => {
                        let s = if v.starts_with("#x") {
                            v.clone()
                        } else {
                            format!("#x{}", v)
                        };
                        let w = v.trim_start_matches("#x").len() * 4;
                        literals::value_constant(&s, w.max(1), empty_span())
                    }
                    SyGuSLiteral::BinConst(v) => {
                        let s = if v.starts_with("#b") {
                            v.clone()
                        } else {
                            format!("#b{}", v)
                        };
                        let w = v.trim_start_matches("#b").len();
                        literals::value_constant(&s, w.max(1), empty_span())
                    }
                    SyGuSLiteral::Decimal(v) => Err(new_custom_error_span(
                        format!("Enumeration: unsupported decimal constant {v}"),
                        empty_span(),
                    )),
                    SyGuSLiteral::StringConst(v) => Err(new_custom_error_span(
                        format!("Enumeration: unsupported string constant {v:?}"),
                        empty_span(),
                    )),
                }),
                _ => None,
            }
        }
        fn term_call(term: &SyGuSTerm) -> Option<(&str, &[SyGuSTerm])> {
            if let SyGuSTerm::Application(fid, args) = term {
                Some((id_name(fid), args))
            } else {
                None
            }
        }
        fn ensure_start(arg: Option<&str>, start: &str) -> parse::Result<()> {
            if arg == Some(start) {
                Ok(())
            } else {
                Err(new_custom_error_span(
                    "Enumeration: Only Start Non-Terminal is accepted.".into(),
                    empty_span(),
                ))
            }
        }
        fn ensure_start2(a: Option<&str>, b: Option<&str>, start: &str) -> parse::Result<()> {
            ensure_start(a, start)?;
            ensure_start(b, start)
        }

        if let Some(NonTerminal(name, rules)) = problem.cfg.first() {
            let mut res = Vec::<Rule<N>>::new();
            for e in problem.chatgpt_exprs.iter() {
                res.push(Rule::ChatGPT(e.clone(), 1))
            }
            for r in rules {
                let term = match r {
                    SyGuSGTerm::SyGuSTerm(t) => t,
                    SyGuSGTerm::Constant(_) | SyGuSGTerm::Variable(_) => continue,
                };
                if let Some(v) = term_symbol(term) {
                    if let Some(id) = problem.arg(v) {
                        res.push(Rule::Var(id));
                    } else if let Some(fid) = deffun::ENV.lookup(v, 0) {
                        res.push(Rule::Fop0(fid));
                    } else {
                        return Err(new_custom_error_span(
                            "Enumeration: Unknowned variable.".into(),
                            empty_span(),
                        ));
                    }
                } else if let Some(v) = term_value(term, problem.bits) {
                    let v = v?;
                    res.push(Rule::Const(v));
                } else if let Some((op, args)) = term_call(term) {
                    match (op, args.len()) {
                        (_, 0) => {
                            if let Some(fid) = deffun::ENV.lookup(op, 0) {
                                res.push(Rule::Fop0(fid));
                            } else {
                                return Err(new_custom_error_span(
                                    "Unknown Symbol.".into(),
                                    empty_span(),
                                ));
                            }
                        }
                        ("bvnot", 1) => {
                            ensure_start(term_symbol(&args[0]), name)?;
                            res.push(Rule::Not);
                        }
                        ("bvneg", 1) => {
                            ensure_start(term_symbol(&args[0]), name)?;
                            res.push(Rule::Neg);
                        }
                        ("bvlshr", 2) if term_symbol(&args[0]) == Some(name) => {
                            if let Some(v) = term_value(&args[1], problem.bits) {
                                res.push(Rule::LShrC(v?.as_u64_lossy()));
                            } else {
                                ensure_start2(term_symbol(&args[0]), term_symbol(&args[1]), name)?;
                                res.push(Rule::LShr);
                            }
                        }
                        ("ehad", 1) => {
                            ensure_start(term_symbol(&args[0]), name)?;
                            res.push(Rule::LShrC(1));
                        }
                        ("arba", 1) => {
                            ensure_start(term_symbol(&args[0]), name)?;
                            res.push(Rule::LShrC(4));
                        }
                        ("shesh", 1) => {
                            ensure_start(term_symbol(&args[0]), name)?;
                            res.push(Rule::LShrC(16));
                        }
                        ("bvshl", 2) if term_symbol(&args[0]) == Some(name) => {
                            if let Some(v) = term_value(&args[1], problem.bits) {
                                res.push(Rule::ShlC(v?.as_u64_lossy()));
                            } else {
                                ensure_start2(term_symbol(&args[0]), term_symbol(&args[1]), name)?;
                                res.push(Rule::Shl);
                            }
                        }
                        ("smol", 2) => {
                            ensure_start(term_symbol(&args[0]), name)?;
                            let _ = term_value(&args[1], problem.bits).ok_or_else(|| {
                                new_custom_error_span(
                                    format!(
                                        "Enumeration: expected constant rhs for smol, got {}",
                                        args[1]
                                    ),
                                    empty_span(),
                                )
                            })??;
                            res.push(Rule::ShlC(1));
                        }
                        ("bvadd", 2) => {
                            ensure_start2(term_symbol(&args[0]), term_symbol(&args[1]), name)?;
                            res.push(Rule::Add);
                        }
                        ("bvxor", 2) => {
                            ensure_start2(term_symbol(&args[0]), term_symbol(&args[1]), name)?;
                            res.push(Rule::Xor);
                        }
                        ("bvand", 2) => {
                            ensure_start2(term_symbol(&args[0]), term_symbol(&args[1]), name)?;
                            res.push(Rule::And);
                        }
                        ("bvor", 2) => {
                            ensure_start2(term_symbol(&args[0]), term_symbol(&args[1]), name)?;
                            res.push(Rule::Or);
                        }
                        ("bvsub", 2) => {
                            ensure_start2(term_symbol(&args[0]), term_symbol(&args[1]), name)?;
                            res.push(Rule::Sub);
                        }
                        ("bvmul", 2) => {
                            ensure_start2(term_symbol(&args[0]), term_symbol(&args[1]), name)?;
                            res.push(Rule::Mul);
                        }
                        ("bvudiv", 2) => {
                            ensure_start2(term_symbol(&args[0]), term_symbol(&args[1]), name)?;
                            res.push(Rule::UDiv);
                        }
                        ("bvsdiv", 2) => {
                            ensure_start2(term_symbol(&args[0]), term_symbol(&args[1]), name)?;
                            res.push(Rule::SDiv);
                        }
                        ("bvurem", 2) => {
                            ensure_start2(term_symbol(&args[0]), term_symbol(&args[1]), name)?;
                            res.push(Rule::URem);
                        }
                        ("bvsrem", 2) => {
                            ensure_start2(term_symbol(&args[0]), term_symbol(&args[1]), name)?;
                            res.push(Rule::SRem);
                        }
                        ("bvashr", 2) => {
                            ensure_start2(term_symbol(&args[0]), term_symbol(&args[1]), name)?;
                            res.push(Rule::AShr);
                        }
                        ("bvlshr", 2) => {
                            ensure_start2(term_symbol(&args[0]), term_symbol(&args[1]), name)?;
                            res.push(Rule::LShr);
                        }
                        ("ite", _) => {
                            res.push(Rule::Ite);
                        }
                        (_, 1) => {
                            ensure_start(term_symbol(&args[0]), name)?;
                            if let Some(a) = deffun::ENV.lookup(op, 1) {
                                res.push(Rule::Fop1(a));
                            } else {
                                return Err(new_custom_error_span(
                                    "Unknown Symbol.".into(),
                                    empty_span(),
                                ));
                            }
                        }
                        (_, 2) => {
                            ensure_start2(term_symbol(&args[0]), term_symbol(&args[1]), name)?;
                            if let Some(a) = deffun::ENV.lookup(op, 2) {
                                res.push(Rule::Fop2(a));
                            } else {
                                return Err(new_custom_error_span(
                                    "Unknown Symbol.".into(),
                                    empty_span(),
                                ));
                            }
                        }
                        _ => {}
                    }
                }
            }
            Ok(res.into())
        } else {
            Err(new_custom_error_span(
                "Enumeration: Need a Start Non-Terminal.".into(),
                problem.span.clone(),
            ))
        }
    }
}
