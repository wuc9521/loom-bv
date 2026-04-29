use bumpalo::Bump;
use derive_more::{DebugCustom, Display};
use pest::Span;
use sygus_parser::ast::{Identifier, Literal as SyGuSLiteral, SyGuSTerm};
use thiserror::Error;
// use z3::{ast::{BV, Ast}, Symbol};

use crate::{
    all_ops, bv_op_of, enum_expr, enum_ownedexpr,
    enumerate::op,
    enumerate::value::Value,
    parse::{self, deffun, literals, new_custom_error_span},
    smt_name_of,
};

use super::Bv;

enum_expr!();

#[derive(Error, Debug)]
#[error("divided by zero")]
pub struct DivideByZero;

fn value_extract(value: Value, hi: u64, lo: u64) -> Value {
    let width = (hi - lo + 1) as usize;
    let shifted = value.to_biguint() >> (lo as usize);
    let mask = (num_bigint::BigUint::from(1u8) << width) - num_bigint::BigUint::from(1u8);
    Value::from_biguint(shifted & mask, width)
}

fn value_concat(lhs: Value, rhs: Value) -> Value {
    let rhs_bits = rhs.bits();
    let total_bits = lhs.bits() + rhs_bits;
    let raw = (lhs.to_biguint() << rhs_bits) | rhs.to_biguint();
    Value::from_biguint(raw, total_bits)
}

fn bv_extract<const N: usize>(value: Bv<N>, hi: u64, lo: u64) -> Bv<N> {
    let width = hi - lo + 1;
    let mask = if width >= 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    };
    Bv(value.map(|lane| (lane >> lo) & mask))
}

fn bv_concat<const N: usize>(lhs: Bv<N>, rhs: Bv<N>, rhs_bits: usize) -> Bv<N> {
    let shift = rhs_bits.min(63) as u32;
    Bv(lhs
        .into_iter_fixed()
        .zip(rhs.into_iter_fixed())
        .map(|(l, r)| (l << shift) | r)
        .collect())
}

fn expr_width(expr: &Expr<'_>) -> usize {
    match expr {
        Expr::Concat(a, b) => expr_width(a) + expr_width(b),
        Expr::Extract(_, hi, lo) => (hi - lo + 1) as usize,
        Expr::Fop0Dyn(id) => deffun::ENV.ret_bits(*id, 0),
        Expr::Const(v) => v.bits(),
        Expr::Var(_) => 64,
        Expr::Not(a)
        | Expr::Neg(a)
        | Expr::Fop1Dyn(_, a) => expr_width(a),
        Expr::Add(a, _)
        | Expr::Xor(a, _)
        | Expr::And(a, _)
        | Expr::Or(a, _)
        | Expr::Mul(a, _)
        | Expr::Sub(a, _)
        | Expr::Fop2Dyn(_, a, _)
        | Expr::LShr(a, _)
        | Expr::AShr(a, _)
        | Expr::Shl(a, _)
        | Expr::UDiv(a, _)
        | Expr::URem(a, _)
        | Expr::SDiv(a, _)
        | Expr::SRem(a, _) => expr_width(a),
        Expr::Ite(_, a, _) => expr_width(a),
    }
}

fn owned_expr_width(expr: &OwnedExpr) -> usize {
    match expr {
        OwnedExpr::Concat(a, b) => owned_expr_width(a) + owned_expr_width(b),
        OwnedExpr::Extract(_, hi, lo) => (hi - lo + 1) as usize,
        OwnedExpr::Fop0Dyn(id) => deffun::ENV.ret_bits(*id, 0),
        OwnedExpr::FopDyn(id, args) => deffun::ENV.ret_bits(*id, args.len()),
        OwnedExpr::Const(v) => v.bits(),
        OwnedExpr::Var(_) => 64,
        OwnedExpr::Not(a)
        | OwnedExpr::Neg(a)
        | OwnedExpr::Fop1Dyn(_, a) => owned_expr_width(a),
        OwnedExpr::Add(a, _)
        | OwnedExpr::Xor(a, _)
        | OwnedExpr::And(a, _)
        | OwnedExpr::Or(a, _)
        | OwnedExpr::Mul(a, _)
        | OwnedExpr::Sub(a, _)
        | OwnedExpr::Fop2Dyn(_, a, _)
        | OwnedExpr::LShr(a, _)
        | OwnedExpr::AShr(a, _)
        | OwnedExpr::Shl(a, _)
        | OwnedExpr::UDiv(a, _)
        | OwnedExpr::URem(a, _)
        | OwnedExpr::SDiv(a, _)
        | OwnedExpr::SRem(a, _) => owned_expr_width(a),
        OwnedExpr::Ite(_, a, _) => owned_expr_width(a),
    }
}

pub fn format_owned_dyn_app(fid: usize, args: &[OwnedExpr]) -> String {
    let rendered_args = args
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(" ");
    format!("({} {})", deffun::ENV.name(fid, args.len()), rendered_args)
}

impl<'a> Expr<'a> {
    pub fn eval(&self, args: &[Value]) -> Result<Value, DivideByZero> {
        macro_rules! foreach_op {
            (1, false, $op: ident) => {
                if let Expr::$op(e1) = self {
                    return Ok(crate::op_of![$op](e1.eval(args)?));
                }
            };
            (2, false, $op: ident) => {
                if let Expr::$op(e1, e2) = self {
                    return Ok(crate::op_of![$op](e1.eval(args)?, e2.eval(args)?));
                }
            };
            (2, true, $op: ident) => {
                if let Expr::$op(e1, e2) = self {
                    return crate::op_of![$op](e1.eval(args)?, e2.eval(args)?);
                }
            };
        }
        if let Expr::Var(a) = self {
            return Ok(args[*a].clone());
        }
        if let Expr::Concat(a, b) = self {
            return Ok(value_concat(a.eval(args)?, b.eval(args)?));
        }
        if let Expr::Extract(a, hi, lo) = self {
            return Ok(value_extract(a.eval(args)?, *hi, *lo));
        }
        if let Expr::Fop0Dyn(id) = self {
            return deffun::ENV.apply(*id, 0).eval(&[]);
        }
        if let Expr::Const(a) = self {
            return Ok(a.clone());
        }
        if let Expr::Ite(a, b, c) = self {
            return Ok(op::ite(a.eval(args)?, b.eval(args)?, c.eval(args)?));
        }
        if let Expr::Fop1Dyn(id, e1) = self {
            return Ok(deffun::ENV.apply(*id, 1).eval(&[e1.eval(args)?])?);
        }
        if let Expr::Fop2Dyn(id, e1, e2) = self {
            return deffun::ENV
                .apply(*id, 2)
                .eval(&[e1.eval(args)?, e2.eval(args)?]);
        }
        all_ops!(arity nonzero);
        panic!("should not reach here. {:?}", self);
    }
    pub fn eval_bv<const N: usize>(&self, args: &[Bv<N>]) -> Bv<N> {
        macro_rules! foreach_op {
            (1, $op: ident) => {
                if let Expr::$op(e1) = self {
                    return crate::bv_op_of![$op](e1.eval_bv(args));
                }
            };
            (2, $op: ident) => {
                if let Expr::$op(e1, e2) = self {
                    return crate::bv_op_of![$op](e1.eval_bv(args), e2.eval_bv(args));
                }
            };
        }
        if let Expr::Var(a) = self {
            return args[*a];
        }
        if let Expr::Concat(a, b) = self {
            return bv_concat(a.eval_bv(args), b.eval_bv(args), expr_width(b));
        }
        if let Expr::Extract(a, hi, lo) = self {
            return bv_extract(a.eval_bv(args), *hi, *lo);
        }
        if let Expr::Fop0Dyn(id) = self {
            return deffun::ENV.apply(*id, 0).eval_bv(&[]);
        }
        if let Expr::Const(a) = self {
            return Bv([a.as_u64_lossy(); N].into());
        }
        if let Expr::Ite(a, b, c) = self {
            return op::bv::ite(a.eval_bv(args), b.eval_bv(args), c.eval_bv(args));
        }
        if let Expr::Fop1Dyn(id, e1) = self {
            return deffun::ENV.apply(*id, 1).eval_bv(&[e1.eval_bv(args)]);
        }
        if let Expr::Fop2Dyn(id, e1, e2) = self {
            return deffun::ENV
                .apply(*id, 2)
                .eval_bv(&[e1.eval_bv(args), e2.eval_bv(args)]);
        }
        all_ops!(arity);
        panic!("should not reach here. {:?}", self);
    }
    pub fn is_shift(&self) -> bool {
        match self {
            Expr::LShr(_, _) => true,
            Expr::AShr(_, _) => true,
            Expr::Shl(_, _) => true,
            _ => false,
        }
    }
    pub fn from_owned(bump: &'a Bump, expr: &OwnedExpr) -> &'a Expr<'a> {
        macro_rules! foreach_op {
            (1, $op:ident) => {
                if let OwnedExpr::$op(a) = expr {
                    return bump.alloc(Expr::$op(Self::from_owned(bump, a)));
                }
            };
            (2, $op:ident) => {
                if let OwnedExpr::$op(a, b) = expr {
                    return bump.alloc(Expr::$op(
                        Self::from_owned(bump, a),
                        Self::from_owned(bump, b),
                    ));
                }
            };
        }
        if let OwnedExpr::Var(i) = expr {
            return bump.alloc(Expr::Var(*i));
        }
        if let OwnedExpr::Concat(a, b) = expr {
            return bump.alloc(Expr::Concat(
                Self::from_owned(bump, a),
                Self::from_owned(bump, b),
            ));
        }
        if let OwnedExpr::Extract(a, hi, lo) = expr {
            return bump.alloc(Expr::Extract(Self::from_owned(bump, a), *hi, *lo));
        }
        if let OwnedExpr::Fop0Dyn(id) = expr {
            return bump.alloc(Expr::Fop0Dyn(*id));
        }
        if let OwnedExpr::Const(c) = expr {
            return bump.alloc(Expr::Const(c.clone()));
        }
        if let OwnedExpr::Ite(a, b, c) = expr {
            return bump.alloc(Expr::Ite(
                Self::from_owned(bump, a),
                Self::from_owned(bump, b),
                Self::from_owned(bump, c),
            ));
        }
        if let OwnedExpr::Fop1Dyn(id, a) = expr {
            return bump.alloc(Expr::Fop1Dyn(*id, Self::from_owned(bump, a)));
        }
        if let OwnedExpr::Fop2Dyn(id, a, b) = expr {
            return bump.alloc(Expr::Fop2Dyn(
                *id,
                Self::from_owned(bump, a),
                Self::from_owned(bump, b),
            ));
        }
        all_ops!(arity);
        panic!();
    }
    pub fn for_each_subexpr<const N: usize>(
        &'a self,
        f: &mut impl FnMut(&'a Expr, Bv<N>) -> Result<(), ()>,
        args: &[Bv<N>],
    ) -> Result<Option<Bv<N>>, ()> {
        macro_rules! foreach_op {
            (1, false, $op: ident) => {
                if let Expr::$op(e1) = self {
                    let v1 = e1.for_each_subexpr(f, args)?;
                    let v1 = if let Some(v) = v1 { v } else { return Ok(None) };
                    f(e1, v1)?;
                    return Ok(Some(bv_op_of![$op](v1)));
                }
            };
            (2, false, $op:ident) => {{
                if let Expr::$op(e1, e2) = self {
                    let v1 = e1.for_each_subexpr(f, args)?;
                    let v1 = if let Some(v) = v1 { v } else { return Ok(None) };
                    f(e1, v1)?;
                    let v2 = e2.for_each_subexpr(f, args)?;
                    let v2 = if let Some(v) = v2 { v } else { return Ok(None) };
                    f(e2, v2)?;
                    let v = bv_op_of![$op](v1, v2);
                    return Ok(Some(v));
                }
            }};
            (2, true, $op:ident) => {{
                if let Expr::$op(e1, e2) = self {
                    let v1 = e1.for_each_subexpr(f, args)?;
                    let v1 = if let Some(v) = v1 { v } else { return Ok(None) };
                    f(e1, v1)?;
                    let v2 = e2.for_each_subexpr(f, args)?;
                    let v2 = if let Some(v) = v2 { v } else { return Ok(None) };
                    f(e2, v2)?;
                    if v2.any_eq(&Bv::ZEROS) {
                        return Ok(None);
                    }
                    let v = bv_op_of![$op](v1, v2);
                    return Ok(Some(v));
                }
            }};
        }
        if let Expr::Var(i) = self {
            return Ok(Some(args[*i].clone()));
        }
        if let Expr::Concat(a, b) = self {
            let v1 = a.for_each_subexpr(f, args)?;
            let v1 = if let Some(v) = v1 { v } else { return Ok(None) };
            f(a, v1)?;
            let v2 = b.for_each_subexpr(f, args)?;
            let v2 = if let Some(v) = v2 { v } else { return Ok(None) };
            f(b, v2)?;
            return Ok(Some(bv_concat(v1, v2, expr_width(b))));
        }
        if let Expr::Extract(a, hi, lo) = self {
            let v = a.for_each_subexpr(f, args)?;
            let v = if let Some(v) = v { v } else { return Ok(None) };
            f(a, v)?;
            return Ok(Some(bv_extract(v, *hi, *lo)));
        }
        if let Expr::Fop0Dyn(id) = self {
            return Ok(Some(deffun::ENV.apply(*id, 0).eval_bv(&[])));
        }
        if let Expr::Const(c) = self {
            return Ok(Some(Bv([c.as_u64_lossy(); N].into())));
        }
        if let Expr::Fop1Dyn(id, e1) = self {
            let v1 = e1.for_each_subexpr(f, args)?;
            let v1 = if let Some(v) = v1 { v } else { return Ok(None) };
            f(e1, v1)?;
            return Ok(Some(deffun::ENV.apply(*id, 1).eval_bv(&[v1])));
        }
        if let Expr::Fop2Dyn(id, e1, e2) = self {
            let v1 = e1.for_each_subexpr(f, args)?;
            let v1 = if let Some(v) = v1 { v } else { return Ok(None) };
            f(e1, v1)?;
            let v2 = e2.for_each_subexpr(f, args)?;
            let v2 = if let Some(v) = v2 { v } else { return Ok(None) };
            f(e2, v2)?;
            return Ok(Some(deffun::ENV.apply(*id, 2).eval_bv(&[v1, v2])));
        }
        all_ops!(arity nonzero);
        return Ok(None);
    }
}

enum_ownedexpr!();

impl OwnedExpr {
    pub fn equal(&self, expr: &Expr) -> bool {
        self == &expr.into()
    }
    pub fn from_term(term: &SyGuSTerm, env: &[(&str, u64)]) -> parse::Result<Self> {
        fn empty_span() -> Span<'static> {
            Span::new("", 0, 0).expect("empty span should be valid")
        }

        fn symbol_name(id: &Identifier) -> &str {
            id.get_name()
        }

        fn index_numeral(idx: &sygus_parser::ast::Index) -> Option<u64> {
            match idx {
                sygus_parser::ast::Index::Numeral(v) => Some(*v as u64),
                sygus_parser::ast::Index::Symbol(_) => None,
            }
        }

        fn literal_to_value(lit: &SyGuSLiteral) -> parse::Result<Value> {
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
                SyGuSLiteral::Decimal(_) | SyGuSLiteral::StringConst(_) => Err(
                    new_custom_error_span("Unrecongnized Constant.".into(), empty_span()),
                ),
            }
        }

        fn identifier_to_value(id: &Identifier) -> Option<parse::Result<Value>> {
            let name = symbol_name(id);
            if name.eq_ignore_ascii_case("true") {
                Some(Ok(Value::from_u64(1, 1)))
            } else if name.eq_ignore_ascii_case("false") {
                Some(Ok(Value::from_u64(0, 1)))
            } else if name.starts_with("#x") {
                let bits = name.trim_start_matches("#x").len() * 4;
                Some(literals::value_constant(name, bits.max(1), empty_span()))
            } else if name.starts_with("#b") {
                let bits = name.trim_start_matches("#b").len();
                Some(literals::value_constant(name, bits.max(1), empty_span()))
            } else if name.starts_with("#d") {
                Some(literals::value_constant(name, 64, empty_span()))
            } else {
                None
            }
        }

        match term {
            SyGuSTerm::Identifier(id) => {
                let v = symbol_name(id);
                if let Some((i, _)) = env.iter().enumerate().find(|(_, x)| x.0 == v) {
                    Ok(Self::Var(i))
                } else if let Some(value) = identifier_to_value(id) {
                    Ok(Self::Const(value?))
                } else if let Some(fid) = deffun::ENV.lookup(v, 0) {
                    Ok(Self::Fop0Dyn(fid))
                } else {
                    Err(new_custom_error_span(
                        "Unrecongnized Variable".into(),
                        empty_span(),
                    ))
                }
            }
            SyGuSTerm::Literal(lit) => Ok(Self::Const(literal_to_value(lit)?)),
            SyGuSTerm::Annotated(inner, _) => Self::from_term(inner, env),
            SyGuSTerm::Application(id, args) => {
                let opname = symbol_name(id);
                if opname == "extract" && args.len() == 1 {
                    if let Identifier::Indexed(_, idxs) = id {
                        if idxs.len() >= 2 {
                            if let (Some(hi), Some(lo)) =
                                (index_numeral(&idxs[0]), index_numeral(&idxs[1]))
                            {
                                if hi >= lo {
                                    return Ok(Self::Extract(
                                        Self::from_term(&args[0], env)?.into(),
                                        hi,
                                        lo,
                                    ));
                                }
                            }
                        }
                    }
                }
                if opname == "concat" && args.len() >= 2 {
                    let last = args.last().unwrap();
                    let mut acc = Self::from_term(last, env)?;
                    for arg in args[..args.len() - 1].iter().rev() {
                        acc = Self::Concat(Self::from_term(arg, env)?.into(), acc.into());
                    }
                    return Ok(acc);
                }
                macro_rules! operator1 {
                    ($opn:expr, $n:ident) => {
                        if opname == $opn && args.len() == 1 {
                            return Ok(Self::$n(Self::from_term(&args[0], env)?.into()));
                        }
                    };
                }
                macro_rules! operator2 {
                    ($opn:expr, $n:ident) => {
                        if opname == $opn && args.len() == 2 {
                            return Ok(Self::$n(
                                Self::from_term(&args[0], env)?.into(),
                                Self::from_term(&args[1], env)?.into(),
                            ));
                        }
                    };
                }
                macro_rules! foreach_op {
                    (1, $op:ident) => {
                        operator1!(smt_name_of![$op], $op);
                    };
                    (2, $op:ident) => {
                        operator2!(smt_name_of![$op], $op);
                    };
                }
                all_ops!(arity);
                // SyGuS boolean connectives may appear in define-fun bodies; booleans
                // are represented as 1-bit bitvectors in this codebase.
                operator1!("not", Not);
                if opname == "and" && args.len() >= 2 {
                    let mut it = args.iter();
                    let mut acc = Self::from_term(it.next().unwrap(), env)?;
                    for a in it {
                        // Internal boolean encoding uses 0 for true and 1 for false.
                        acc = Self::Or(acc.into(), Self::from_term(a, env)?.into());
                    }
                    return Ok(acc);
                }
                if opname == "or" && args.len() >= 2 {
                    let mut it = args.iter();
                    let mut acc = Self::from_term(it.next().unwrap(), env)?;
                    for a in it {
                        // Internal boolean encoding uses 0 for true and 1 for false.
                        acc = Self::And(acc.into(), Self::from_term(a, env)?.into());
                    }
                    return Ok(acc);
                }
                if opname == "xor" && args.len() >= 2 {
                    let mut it = args.iter();
                    let mut acc = Self::from_term(it.next().unwrap(), env)?;
                    for a in it {
                        acc = Self::Xor(acc.into(), Self::from_term(a, env)?.into());
                    }
                    return Ok(acc);
                }
                operator2!("=", Xor);
                if opname == "ite" && args.len() == 3 {
                    return Ok(Self::Ite(
                        Self::from_term(&args[0], env)?.into(),
                        Self::from_term(&args[1], env)?.into(),
                        Self::from_term(&args[2], env)?.into(),
                    ));
                }
                if args.len() == 1 {
                    if let Some(fid) = deffun::ENV.lookup(opname, 1) {
                        return Ok(Self::Fop1Dyn(
                            fid,
                            Self::from_term(&args[0], env)?.into(),
                        ));
                    }
                }
                if args.len() == 2 {
                    if let Some(fid) = deffun::ENV.lookup(opname, 2) {
                        return Ok(Self::Fop2Dyn(
                            fid,
                            Self::from_term(&args[0], env)?.into(),
                            Self::from_term(&args[1], env)?.into(),
                        ));
                    }
                }
                if let Some(fid) = deffun::ENV.lookup(opname, args.len()) {
                    return Ok(Self::FopDyn(
                        fid,
                        args.iter()
                            .map(|arg| Self::from_term(arg, env))
                            .collect::<parse::Result<Vec<_>>>()?,
                    ));
                }
                Err(new_custom_error_span(
                    format!("Unrecongnized Expression: {}", term),
                    empty_span(),
                ))
            }
            SyGuSTerm::Exists(_, _) | SyGuSTerm::Forall(_, _) | SyGuSTerm::Let(_, _) => Err(
                new_custom_error_span(format!("Unrecongnized Expression: {}", term), empty_span()),
            ),
        }
    }

    pub fn for_each_subexpr(&self, f: &mut impl FnMut(&OwnedExpr) -> ()) -> () {
        f(self);
        macro_rules! foreach_op {
            (1, $op:ident) => {
                if let OwnedExpr::$op(e1) = self {
                    e1.for_each_subexpr(f);
                    return;
                }
            };
            (2, $op:ident) => {{
                if let OwnedExpr::$op(e1, e2) = self {
                    e1.for_each_subexpr(f);
                    e2.for_each_subexpr(f);
                    return;
                }
            }};
        }
        if let OwnedExpr::Var(_) = self {
            return ();
        }
        if let OwnedExpr::Concat(a, b) = self {
            a.for_each_subexpr(f);
            b.for_each_subexpr(f);
            return ();
        }
        if let OwnedExpr::Extract(a, _, _) = self {
            a.for_each_subexpr(f);
            return ();
        }
        if let OwnedExpr::Fop0Dyn(_) = self {
            return ();
        }
        if let OwnedExpr::Const(_) = self {
            return ();
        }
        if let OwnedExpr::Ite(_, _, _) = self {
            return ();
        }
        if let OwnedExpr::FopDyn(_, args) = self {
            for arg in args {
                arg.for_each_subexpr(f);
            }
            return ();
        }
        if let OwnedExpr::Fop1Dyn(_, a) = self {
            a.for_each_subexpr(f);
            return ();
        }
        if let OwnedExpr::Fop2Dyn(_, a, b) = self {
            a.for_each_subexpr(f);
            b.for_each_subexpr(f);
            return ();
        }
        all_ops!(arity);
        panic!();
    }
    pub fn size(&self) -> usize {
        macro_rules! foreach_op {
            (1, $op:ident) => {
                if let OwnedExpr::$op(a) = self {
                    return 1 + a.size();
                }
            };
            (2, $op:ident) => {
                if let OwnedExpr::$op(a, b) = self {
                    return 1 + a.size() + b.size();
                }
            };
        }
        if let OwnedExpr::Var(_) = self {
            return 1;
        }
        if let OwnedExpr::Concat(a, b) = self {
            return 1 + a.size() + b.size();
        }
        if let OwnedExpr::Extract(a, _, _) = self {
            return 1 + a.size();
        }
        if let OwnedExpr::Fop0Dyn(_) = self {
            return 1;
        }
        if let OwnedExpr::Const(_) = self {
            return 1;
        }
        if let OwnedExpr::Ite(a, b, c) = self {
            return 1 + a.size() + b.size() + c.size();
        }
        if let OwnedExpr::FopDyn(_, args) = self {
            return 1 + args.iter().map(OwnedExpr::size).sum::<usize>();
        }
        if let OwnedExpr::Fop1Dyn(_, a) = self {
            return 1 + a.size();
        }
        if let OwnedExpr::Fop2Dyn(_, a, b) = self {
            return 1 + a.size() + b.size();
        }
        all_ops!(arity);
        panic!();
    }

    pub fn to_sygus(&self, arg_names: &[&str]) -> String {
        macro_rules! foreach_op {
            (1, $op:ident) => {
                if let OwnedExpr::$op(a) = self {
                    return format!("({} {})", smt_name_of!($op), a.to_sygus(arg_names));
                }
            };
            (2, $op:ident) => {
                if let OwnedExpr::$op(a, b) = self {
                    return format!(
                        "({} {} {})",
                        smt_name_of!($op),
                        a.to_sygus(arg_names),
                        b.to_sygus(arg_names)
                    );
                }
            };
        }
        if let OwnedExpr::Var(i) = self {
            return arg_names
                .get(*i)
                .map(|name| (*name).to_string())
                .unwrap_or_else(|| format!("v{i}"));
        }
        if let OwnedExpr::Concat(a, b) = self {
            return format!("(concat {} {})", a.to_sygus(arg_names), b.to_sygus(arg_names));
        }
        if let OwnedExpr::Extract(a, hi, lo) = self {
            return format!("((_ extract {} {}) {})", hi, lo, a.to_sygus(arg_names));
        }
        if let OwnedExpr::Fop0Dyn(id) = self {
            return deffun::ENV.name(*id, 0).to_string();
        }
        if let OwnedExpr::Const(c) = self {
            return c.to_string();
        }
        if let OwnedExpr::Ite(a, b, c) = self {
            return format!(
                "(ite (= {} #x0000000000000000) {} {})",
                a.to_sygus(arg_names),
                b.to_sygus(arg_names),
                c.to_sygus(arg_names)
            );
        }
        if let OwnedExpr::FopDyn(id, args) = self {
            let rendered_args = args
                .iter()
                .map(|arg| arg.to_sygus(arg_names))
                .collect::<Vec<_>>()
                .join(" ");
            return format!("({} {})", deffun::ENV.name(*id, args.len()), rendered_args);
        }
        if let OwnedExpr::Fop1Dyn(id, a) = self {
            return format!("({} {})", deffun::ENV.name(*id, 1), a.to_sygus(arg_names));
        }
        if let OwnedExpr::Fop2Dyn(id, a, b) = self {
            return format!(
                "({} {} {})",
                deffun::ENV.name(*id, 2),
                a.to_sygus(arg_names),
                b.to_sygus(arg_names)
            );
        }
        all_ops!(arity);
        unreachable!()
    }
}

impl<'a> From<&Expr<'a>> for OwnedExpr {
    fn from(value: &Expr<'a>) -> Self {
        if let Expr::Var(i) = value {
            return OwnedExpr::Var(*i);
        }
        if let Expr::Concat(a, b) = value {
            return OwnedExpr::Concat(Box::new((*a).into()), Box::new((*b).into()));
        }
        if let Expr::Extract(a, hi, lo) = value {
            return OwnedExpr::Extract(Box::new((*a).into()), *hi, *lo);
        }
        if let Expr::Fop0Dyn(id) = value {
            return OwnedExpr::Fop0Dyn(*id);
        }
        if let Expr::Const(c) = value {
            return OwnedExpr::Const(c.clone());
        }
        if let Expr::Ite(e1, e2, e3) = value {
            return OwnedExpr::Ite(
                Box::new((*e1).into()),
                Box::new((*e2).into()),
                Box::new((*e3).into()),
            );
        }
        if let Expr::Fop1Dyn(id, e1) = value {
            return OwnedExpr::Fop1Dyn(*id, Box::new((*e1).into()));
        }
        if let Expr::Fop2Dyn(id, e1, e2) = value {
            return OwnedExpr::Fop2Dyn(*id, Box::new((*e1).into()), Box::new((*e2).into()));
        }
        macro_rules! foreach_op {
            (1, $op:ident) => {
                if let Expr::$op(e1) = value {
                    return OwnedExpr::$op(Box::new((*e1).into()));
                }
            };
            (2, $op:ident) => {
                if let Expr::$op(e1, e2) = value {
                    return OwnedExpr::$op(Box::new((*e1).into()), Box::new((*e2).into()));
                }
            };
        }
        all_ops!(arity);
        panic!("shoud not reach here");
    }
}

#[macro_export]
macro_rules! oexpr {
    ($v:literal) => { OwnedExpr::Var($v as usize) };
    ([$v:expr]) => { OwnedExpr::Const(crate::enumerate::value::Value::from_u64($v as u64, 64)) };
    ($v:ident) => { $v.clone() };
    (! $a1:tt) => { OwnedExpr::Not(Box::new(oexpr![$a1])) };
    (~ $a1:tt) => { OwnedExpr::Neg(Box::new(oexpr![$a1])) };
    (+ $a1:tt $a2:tt) => { OwnedExpr::Add(Box::new(oexpr![$a1]), Box::new(oexpr![$a2])) };
    (^ $a1:tt $a2:tt) => { OwnedExpr::Xor(Box::new(oexpr![$a1]), Box::new(oexpr![$a2])) };
    (& $a1:tt $a2:tt) => { OwnedExpr::And(Box::new(oexpr![$a1]), Box::new(oexpr![$a2])) };
    (| $a1:tt $a2:tt) => { OwnedExpr::Or(Box::new(oexpr![$a1]), Box::new(oexpr![$a2])) };
    (- $a1:tt $a2:tt) => { OwnedExpr::Sub(Box::new(oexpr![$a1]), Box::new(oexpr![$a2])) };
    (* $a1:tt $a2:tt) => { OwnedExpr::Mul(Box::new(oexpr![$a1]), Box::new(oexpr![$a2])) };
    (/ $a1:tt $a2:tt) => { OwnedExpr::UDiv(Box::new(oexpr![$a1]), Box::new(oexpr![$a2])) };
    (>> $a1:tt $a2:tt) => { OwnedExpr::LShr(Box::new(oexpr![$a1]), Box::new(oexpr![$a2])) };
    (<< $a1:tt $a2:tt) => { OwnedExpr::Shl(Box::new(oexpr![$a1]), Box::new(oexpr![$a2])) };
    (ite $a1:tt $a2:tt $a3:tt) => { OwnedExpr::Ite(Box::new(oexpr![$a1]), Box::new(oexpr![$a2]), Box::new(oexpr![$a3])) };
    ( ($( $inner:tt )*) ) => { oexpr!($($inner)*) };
}

#[cfg(test)]
mod tests {
    #[test]
    fn test1() {
        use super::OwnedExpr;
        println!("{:?}", oexpr! {+ [1] [2]});
    }
}

impl OwnedExpr {
    pub fn eval(&self, args: &[Value]) -> Result<Value, DivideByZero> {
        macro_rules! foreach_op {
            (1, false, $op: ident) => {
                if let OwnedExpr::$op(e1) = self {
                    return Ok(crate::op_of![$op](e1.eval(args)?));
                }
            };
            (2, false, $op: ident) => {
                if let OwnedExpr::$op(e1, e2) = self {
                    return Ok(crate::op_of![$op](e1.eval(args)?, e2.eval(args)?));
                }
            };
            (2, true, $op: ident) => {
                if let OwnedExpr::$op(e1, e2) = self {
                    return crate::op_of![$op](e1.eval(args)?, e2.eval(args)?);
                }
            };
        }
        if let OwnedExpr::Var(a) = self {
            return Ok(args[*a].clone());
        }
        if let OwnedExpr::Concat(a, b) = self {
            return Ok(value_concat(a.eval(args)?, b.eval(args)?));
        }
        if let OwnedExpr::Extract(a, hi, lo) = self {
            return Ok(value_extract(a.eval(args)?, *hi, *lo));
        }
        if let OwnedExpr::Fop0Dyn(id) = self {
            return deffun::ENV.apply(*id, 0).eval(&[]);
        }
        if let OwnedExpr::Const(a) = self {
            return Ok(a.clone());
        }
        if let OwnedExpr::FopDyn(id, exprs) = self {
            let values = exprs
                .iter()
                .map(|expr| expr.eval(args))
                .collect::<Result<Vec<_>, _>>()?;
            return deffun::ENV.apply(*id, exprs.len()).eval(&values);
        }
        if let OwnedExpr::Ite(e1, e2, e3) = self {
            return Ok(op::ite(e1.eval(args)?, e2.eval(args)?, e3.eval(args)?));
        }
        if let OwnedExpr::Fop1Dyn(id, e1) = self {
            return Ok(deffun::ENV.apply(*id, 1).eval(&[e1.eval(args)?])?);
        }
        if let OwnedExpr::Fop2Dyn(id, e1, e2) = self {
            return deffun::ENV
                .apply(*id, 2)
                .eval(&[e1.eval(args)?, e2.eval(args)?]);
        }
        all_ops!(arity nonzero);
        panic!("should not reach here.");
    }
    pub fn eval_bv<const N: usize>(&self, args: &[Bv<N>]) -> Bv<N> {
        macro_rules! foreach_op {
            (1, $op: ident) => {
                if let OwnedExpr::$op(e1) = self {
                    return crate::bv_op_of![$op](e1.eval_bv(args));
                }
            };
            (2, $op: ident) => {
                if let OwnedExpr::$op(e1, e2) = self {
                    return crate::bv_op_of![$op](e1.eval_bv(args), e2.eval_bv(args));
                }
            };
        }
        if let OwnedExpr::Var(a) = self {
            return args[*a];
        }
        if let OwnedExpr::Concat(a, b) = self {
            return bv_concat(a.eval_bv(args), b.eval_bv(args), owned_expr_width(b));
        }
        if let OwnedExpr::Extract(a, hi, lo) = self {
            return bv_extract(a.eval_bv(args), *hi, *lo);
        }
        if let OwnedExpr::Fop0Dyn(id) = self {
            return deffun::ENV.apply(*id, 0).eval_bv(&[]);
        }
        if let OwnedExpr::Const(a) = self {
            return Bv([a.as_u64_lossy(); N].into());
        }
        if let OwnedExpr::FopDyn(id, exprs) = self {
            let values = exprs.iter().map(|expr| expr.eval_bv(args)).collect::<Vec<_>>();
            return deffun::ENV.apply(*id, exprs.len()).eval_bv(&values);
        }
        if let OwnedExpr::Ite(e1, e2, e3) = self {
            return op::bv::ite(e1.eval_bv(args), e2.eval_bv(args), e3.eval_bv(args));
        }
        if let OwnedExpr::Fop1Dyn(id, e1) = self {
            return deffun::ENV.apply(*id, 1).eval_bv(&[e1.eval_bv(args)]);
        }
        if let OwnedExpr::Fop2Dyn(id, e1, e2) = self {
            return deffun::ENV
                .apply(*id, 2)
                .eval_bv(&[e1.eval_bv(args), e2.eval_bv(args)]);
        }
        all_ops!(arity);
        panic!("Should not reach here.")
    }
}
