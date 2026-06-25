use bumpalo::Bump;
use derive_more::{DebugCustom, Display};
use sygus_parser::ast::{Identifier, SyGuSTerm};
use thiserror::Error;
// use z3::{ast::{BV, Ast}, Symbol};

use crate::{
    all_ops, bv_op_of, enum_expr, enum_ownedexpr,
    enumerate::op,
    enumerate::typing,
    enumerate::value::BitVec,
    parse::{self, deffun, empty_span, new_custom_error_span},
    smt_name_of,
};

use super::Bv;

enum_expr!();

#[derive(Error, Debug)]
#[error("divided by zero")]
pub struct DivideByZero;

impl<'a> Expr<'a> {
    pub fn width(&self) -> usize {
        match self {
            Expr::Concat(a, b) => a.width() + b.width(),
            Expr::Extract(_, hi, lo) => (hi - lo + 1) as usize,
            Expr::Func(id, _) => deffun::ENV.ret_bits(*id),
            Expr::Const(v) => v.bits(),
            Expr::Var(_, width) => *width,
            Expr::Not(a) | Expr::Neg(a) => a.width(),
            Expr::Add(a, _)
            | Expr::Xor(a, _)
            | Expr::And(a, _)
            | Expr::Or(a, _)
            | Expr::Mul(a, _)
            | Expr::Sub(a, _)
            | Expr::LShr(a, _)
            | Expr::AShr(a, _)
            | Expr::Shl(a, _)
            | Expr::UDiv(a, _)
            | Expr::URem(a, _)
            | Expr::SDiv(a, _)
            | Expr::SRem(a, _) => a.width(),
            Expr::Ite(_, a, _) => a.width(),
            Expr::BVule(_, _) | Expr::BVult(_, _) | Expr::BVsle(_, _) | Expr::BVslt(_, _) => 1,
        }
    }
}

pub fn format_owned_let(name: &str, value: &OwnedExpr, body: &OwnedExpr) -> String {
    format!("(let (({} {})) {})", name, value, body)
}

pub fn format_func_app(fid: usize, args: &[&Expr<'_>]) -> String {
    let name = deffun::ENV.name(fid);
    if args.is_empty() {
        return name.to_string();
    }
    let rendered = args.iter().map(|a| format!("{}", a)).collect::<Vec<_>>().join(" ");
    format!("({} {})", name, rendered)
}

pub fn format_owned_func_app(fid: usize, args: &[OwnedExpr]) -> String {
    let name = deffun::ENV.name(fid);
    if args.is_empty() {
        return name.to_string();
    }
    let rendered_args = args
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(" ");
    format!("({} {})", name, rendered_args)
}

/// Display helper for `OwnedExpr::SynthApp`. The synth-fun name is looked
/// up from the program's synth-fun registry by index; if the registry is
/// not present (e.g. a freshly-built expression outside a search context)
/// falls back to `synth<idx>`.
pub fn format_owned_synth_app(idx: usize, args: &[OwnedExpr]) -> String {
    let name = deffun::synth_name(idx).unwrap_or_else(|| format!("synth{idx}"));
    if args.is_empty() {
        return name;
    }
    let rendered = args
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(" ");
    format!("({} {})", name, rendered)
}

impl<'a> Expr<'a> {
    pub fn eval(&self, args: &[BitVec]) -> Result<BitVec, DivideByZero> {
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
        if let Expr::Var(a, _) = self {
            return Ok(args[*a].clone());
        }
        if let Expr::Concat(a, b) = self {
            let lhs = a.eval(args)?;
            let rhs = b.eval(args)?;
            return Ok(lhs.concat(&rhs));
        }
        if let Expr::Extract(a, hi, lo) = self {
            let value = a.eval(args)?;
            return Ok(value.extract(*hi, *lo));
        }
        if let Expr::Func(id, args_expr) = self {
            let values = args_expr.iter().map(|a| a.eval(args)).collect::<Result<Vec<_>, _>>()?;
            return deffun::ENV.eval_defined(*id, &values, &[]);
        }        if let Expr::Const(a) = self {
            return Ok(a.clone());
        }
        if let Expr::Ite(a, b, c) = self {
            return Ok(op::ite(a.eval(args)?, b.eval(args)?, c.eval(args)?));
        }
        if let Expr::BVule(a, b) = self { return Ok(op::ule(a.eval(args)?, b.eval(args)?)); }
        if let Expr::BVult(a, b) = self { return Ok(op::ult(a.eval(args)?, b.eval(args)?)); }
        if let Expr::BVsle(a, b) = self { return Ok(op::sle(a.eval(args)?, b.eval(args)?)); }
        if let Expr::BVslt(a, b) = self { return Ok(op::slt(a.eval(args)?, b.eval(args)?)); }
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
        if let Expr::Var(a, _) = self {
            return args[*a];
        }
        if let Expr::Concat(a, b) = self {
            return a.eval_bv(args).concat_low(b.eval_bv(args), b.width());
        }
        if let Expr::Extract(a, hi, lo) = self {
            return a.eval_bv(args).extract(*hi, *lo);
        }
        if let Expr::Func(id, args_expr) = self {
            let values: Vec<_> = args_expr.iter().map(|a| a.eval_bv(args)).collect();
            return deffun::ENV.apply(*id).eval_bv(&values);
        }
        if let Expr::Const(a) = self {
            return Bv([a.as_u64_lossy(); N].into());
        }
        if let Expr::Ite(a, b, c) = self {
            return op::bv::ite(a.eval_bv(args), b.eval_bv(args), c.eval_bv(args));
        }
        if let Expr::BVule(a, b) = self { return op::bv::ule(a.eval_bv(args), b.eval_bv(args)); }
        if let Expr::BVult(a, b) = self { return op::bv::ult(a.eval_bv(args), b.eval_bv(args)); }
        if let Expr::BVsle(a, b) = self { return op::bv::sle(a.eval_bv(args), b.eval_bv(args)); }
        if let Expr::BVslt(a, b) = self { return op::bv::slt(a.eval_bv(args), b.eval_bv(args)); }
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
        if let OwnedExpr::Var(i, w) = expr {
            return bump.alloc(Expr::Var(*i, *w));
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
        if let OwnedExpr::Func(id, owned_args) = expr {
            let children: Vec<&'a Expr<'a>> = owned_args.iter().map(|a| Self::from_owned(bump, a)).collect();
            let slice = bump.alloc_slice_copy(&children);
            return bump.alloc(Expr::Func(*id, slice));
        }
        if let OwnedExpr::Const(c) = expr {
            return bump.alloc(Expr::Const(c.clone()));
        }
        if let OwnedExpr::Let(_, _, _) = expr {
            panic!("borrowed Expr conversion does not support let-bound OwnedExpr");
        }
        if let OwnedExpr::Ite(a, b, c) = expr {
            return bump.alloc(Expr::Ite(
                Self::from_owned(bump, a),
                Self::from_owned(bump, b),
                Self::from_owned(bump, c),
            ));
        }
        if let OwnedExpr::BVule(a, b) = expr { return bump.alloc(Expr::BVule(Self::from_owned(bump, a), Self::from_owned(bump, b))); }
        if let OwnedExpr::BVult(a, b) = expr { return bump.alloc(Expr::BVult(Self::from_owned(bump, a), Self::from_owned(bump, b))); }
        if let OwnedExpr::BVsle(a, b) = expr { return bump.alloc(Expr::BVsle(Self::from_owned(bump, a), Self::from_owned(bump, b))); }
        if let OwnedExpr::BVslt(a, b) = expr { return bump.alloc(Expr::BVslt(Self::from_owned(bump, a), Self::from_owned(bump, b))); }
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
        if let Expr::Var(i, _) = self {
            return Ok(Some(args[*i].clone()));
        }
        if let Expr::Concat(a, b) = self {
            let v1 = a.for_each_subexpr(f, args)?;
            let v1 = if let Some(v) = v1 { v } else { return Ok(None) };
            f(a, v1)?;
            let v2 = b.for_each_subexpr(f, args)?;
            let v2 = if let Some(v) = v2 { v } else { return Ok(None) };
            f(b, v2)?;
            return Ok(Some(v1.concat_low(v2, b.width())));
        }
        if let Expr::Extract(a, hi, lo) = self {
            let v = a.for_each_subexpr(f, args)?;
            let v = if let Some(v) = v { v } else { return Ok(None) };
            f(a, v)?;
            return Ok(Some(v.extract(*hi, *lo)));
        }
        if let Expr::Func(id, args_expr) = self {
            let mut values = Vec::with_capacity(args_expr.len());
            for e in args_expr.iter() {
                let v = e.for_each_subexpr(f, args)?;
                let v = if let Some(v) = v { v } else { return Ok(None) };
                f(*e, v)?;
                values.push(v);
            }
            return Ok(Some(deffun::ENV.apply(*id).eval_bv(&values)));
        }
        if let Expr::Const(c) = self {
            return Ok(Some(Bv([c.as_u64_lossy(); N].into())));
        }
        if let Expr::BVule(e1, e2) = self {
            let v1 = e1.for_each_subexpr(f, args)?;
            let v1 = if let Some(v) = v1 { v } else { return Ok(None) };
            f(e1, v1)?;
            let v2 = e2.for_each_subexpr(f, args)?;
            let v2 = if let Some(v) = v2 { v } else { return Ok(None) };
            f(e2, v2)?;
            return Ok(Some(op::bv::ule(v1, v2)));
        }
        if let Expr::BVult(e1, e2) = self {
            let v1 = e1.for_each_subexpr(f, args)?;
            let v1 = if let Some(v) = v1 { v } else { return Ok(None) };
            f(e1, v1)?;
            let v2 = e2.for_each_subexpr(f, args)?;
            let v2 = if let Some(v) = v2 { v } else { return Ok(None) };
            f(e2, v2)?;
            return Ok(Some(op::bv::ult(v1, v2)));
        }
        if let Expr::BVsle(e1, e2) = self {
            let v1 = e1.for_each_subexpr(f, args)?;
            let v1 = if let Some(v) = v1 { v } else { return Ok(None) };
            f(e1, v1)?;
            let v2 = e2.for_each_subexpr(f, args)?;
            let v2 = if let Some(v) = v2 { v } else { return Ok(None) };
            f(e2, v2)?;
            return Ok(Some(op::bv::sle(v1, v2)));
        }
        if let Expr::BVslt(e1, e2) = self {
            let v1 = e1.for_each_subexpr(f, args)?;
            let v1 = if let Some(v) = v1 { v } else { return Ok(None) };
            f(e1, v1)?;
            let v2 = e2.for_each_subexpr(f, args)?;
            let v2 = if let Some(v) = v2 { v } else { return Ok(None) };
            f(e2, v2)?;
            return Ok(Some(op::bv::slt(v1, v2)));
        }
        all_ops!(arity nonzero);
        return Ok(None);
    }
}

enum_ownedexpr!();

impl OwnedExpr {
    /// Parse a SyGuS term into an `OwnedExpr`, first validating that it is
    /// well-sorted (rejecting genuine Bool ↔ bit-vector mismatches). The sort
    /// check runs on the `SyGuSTerm` because lowering is lossy: e.g. `bvand`
    /// and the boolean `or` both become `OwnedExpr::And`, so sort cannot be
    /// recovered afterwards. `env` maps in-scope names to bit-vector widths
    /// (formal parameters are always bit-vectors here).
    pub fn from_term(term: &SyGuSTerm, env: &[(&str, u64)]) -> parse::Result<Self> {
        let sort_env: Vec<(&str, typing::Sort)> = env
            .iter()
            .map(|&(name, width)| (name, typing::Sort::BitVec(width as usize)))
            .collect();
        typing::check_sort(term, &sort_env)?;
        Self::from_term_lower(term, env)
    }

    fn from_term_lower(term: &SyGuSTerm, env: &[(&str, u64)]) -> parse::Result<Self> {
        fn symbol_name(id: &Identifier) -> &str {
            id.get_name()
        }

        fn extract_indices(id: &Identifier) -> Option<(u64, u64)> {
            let (hi, lo) = crate::parse::extract_indices_from_identifier(id)?;
            let (hi, lo) = (hi as u64, lo as u64);
            if hi >= lo { Some((hi, lo)) } else { None }
        }

        fn identifier_to_value(id: &Identifier) -> Option<parse::Result<BitVec>> {
            let name = symbol_name(id);
            // Booleans use the internal negative-logic convention (0 = true),
            // matching `op::ite` (then-branch when the condition `is_zero()`)
            // and `BoolValue::holds`. SMT `true` → 0, `false` → 1.
            if name.eq_ignore_ascii_case("true") {
                Some(Ok(BitVec::from_u64(0, 1)))
            } else if name.eq_ignore_ascii_case("false") {
                Some(Ok(BitVec::from_u64(1, 1)))
            } else if let Some(digits) = name.strip_prefix("#x") {
                let bits = digits.len() * 4;
                Some(crate::parse::constraint::parse_bv_digits(digits, 16, bits.max(1)))
            } else if let Some(digits) = name.strip_prefix("#b") {
                let bits = digits.len();
                Some(crate::parse::constraint::parse_bv_digits(digits, 2, bits.max(1)))
            } else if let Some(digits) = name.strip_prefix("#d") {
                Some(crate::parse::constraint::parse_bv_digits(digits, 10, 64))
            } else if let Some((digits, width)) =
                crate::parse::constraint::indexed_bv_literal(id)
            {
                // SMT-LIB indexed bit-vector literal `(_ bvDECIMAL WIDTH)`.
                Some(crate::parse::constraint::parse_bv_digits(digits, 10, width))
            } else {
                None
            }
        }

        match term {
            SyGuSTerm::Identifier(id) => {
                let v = symbol_name(id);
                if let Some((i, (_, w))) = env.iter().enumerate().find(|(_, x)| x.0 == v) {
                    Ok(Self::Var(i, *w as usize))
                } else if let Some(value) = identifier_to_value(id) {
                    Ok(Self::Const(value?))
                } else if let Some(fid) = deffun::ENV.lookup(v, 0) {
                    Ok(Self::Func(fid, vec![]))
                } else if let Some(synth_idx) = deffun::lookup_synth(v, 0) {
                    // Bare reference to a nullary synth-fun (fwd-decls
                    // auxiliary, or a nullary entry-point synth-fun).
                    Ok(Self::SynthApp(synth_idx, vec![]))
                } else {
                    Err(new_custom_error_span(
                        format!("Unrecognized identifier `{v}`"),
                        empty_span(),
                    ))
                }
            }
            SyGuSTerm::Literal(lit) => Ok(Self::Const(crate::parse::literal_to_value(lit)?)),
            SyGuSTerm::Annotated(inner, _) => Self::from_term_lower(inner, env),
            SyGuSTerm::Application(id, args) => {
                let opname = symbol_name(id);
                if args.len() == 1 {
                    if let Some((hi, lo)) = extract_indices(id) {
                        return Ok(Self::Extract(
                            Self::from_term_lower(&args[0], env)?.into(),
                            hi,
                            lo,
                        ));
                    }
                }
                if opname == "concat" && args.len() >= 2 {
                    let last = args.last().unwrap();
                    let mut acc = Self::from_term_lower(last, env)?;
                    for arg in args[..args.len() - 1].iter().rev() {
                        acc = Self::Concat(Self::from_term_lower(arg, env)?.into(), acc.into());
                    }
                    return Ok(acc);
                }
                macro_rules! operator1 {
                    ($opn:expr, $n:ident) => {
                        if opname == $opn && args.len() == 1 {
                            return Ok(Self::$n(Self::from_term_lower(&args[0], env)?.into()));
                        }
                    };
                }
                macro_rules! operator2 {
                    ($opn:expr, $n:ident) => {
                        if opname == $opn && args.len() == 2 {
                            return Ok(Self::$n(
                                Self::from_term_lower(&args[0], env)?.into(),
                                Self::from_term_lower(&args[1], env)?.into(),
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
                operator2!("bvule", BVule);
                operator2!("bvult", BVult);
                operator2!("bvsle", BVsle);
                operator2!("bvslt", BVslt);
                if opname == "bvugt" && args.len() == 2 {
                    return Ok(Self::BVult(Box::new(Self::from_term_lower(&args[1], env)?), Box::new(Self::from_term_lower(&args[0], env)?)));
                }
                if opname == "bvuge" && args.len() == 2 {
                    return Ok(Self::BVule(Box::new(Self::from_term_lower(&args[1], env)?), Box::new(Self::from_term_lower(&args[0], env)?)));
                }
                if opname == "bvsgt" && args.len() == 2 {
                    return Ok(Self::BVslt(Box::new(Self::from_term_lower(&args[1], env)?), Box::new(Self::from_term_lower(&args[0], env)?)));
                }
                if opname == "bvsge" && args.len() == 2 {
                    return Ok(Self::BVsle(Box::new(Self::from_term_lower(&args[1], env)?), Box::new(Self::from_term_lower(&args[0], env)?)));
                }
                // SyGuS boolean connectives may appear in define-fun bodies; booleans
                // are represented as 1-bit bitvectors in this codebase.
                operator1!("not", Not);
                if opname == "and" && args.len() >= 2 {
                    let mut it = args.iter();
                    let mut acc = Self::from_term_lower(it.next().unwrap(), env)?;
                    for a in it {
                        // Internal boolean encoding uses 0 for true and 1 for false.
                        acc = Self::Or(acc.into(), Self::from_term_lower(a, env)?.into());
                    }
                    return Ok(acc);
                }
                if opname == "or" && args.len() >= 2 {
                    let mut it = args.iter();
                    let mut acc = Self::from_term_lower(it.next().unwrap(), env)?;
                    for a in it {
                        // Internal boolean encoding uses 0 for true and 1 for false.
                        acc = Self::And(acc.into(), Self::from_term_lower(a, env)?.into());
                    }
                    return Ok(acc);
                }
                if opname == "xor" && args.len() >= 2 {
                    let mut it = args.iter();
                    let mut acc = Self::from_term_lower(it.next().unwrap(), env)?;
                    for a in it {
                        acc = Self::Xor(acc.into(), Self::from_term_lower(a, env)?.into());
                    }
                    return Ok(acc);
                }
                operator2!("=", Xor);
                if opname == "ite" && args.len() == 3 {
                    return Ok(Self::Ite(
                        Self::from_term_lower(&args[0], env)?.into(),
                        Self::from_term_lower(&args[1], env)?.into(),
                        Self::from_term_lower(&args[2], env)?.into(),
                    ));
                }
                if let Some(fid) = deffun::ENV.lookup(opname, args.len()) {
                    return Ok(Self::Func(
                        fid,
                        args.iter()
                            .map(|arg| Self::from_term_lower(arg, env))
                            .collect::<parse::Result<Vec<_>>>()?,
                    ));
                }
                if let Some(synth_idx) = deffun::lookup_synth(opname, args.len()) {
                    return Ok(Self::SynthApp(
                        synth_idx,
                        args.iter()
                            .map(|arg| Self::from_term_lower(arg, env))
                            .collect::<parse::Result<Vec<_>>>()?,
                    ));
                }
                Err(new_custom_error_span(
                    format!("Unrecongnized Expression: {}", term),
                    empty_span(),
                ))
            }
            SyGuSTerm::Let(bindings, body) => {
                let mut extended_env = env.to_vec();
                let mut lowered = Vec::with_capacity(bindings.len());
                for binding in bindings {
                    let value = Self::from_term_lower(&binding.term, &extended_env)?;
                    let width = value.width() as u64;
                    let leaked = Box::leak(binding.name.clone().into_boxed_str()) as &'static str;
                    extended_env.push((leaked, width));
                    lowered.push((binding.name.clone(), value));
                }
                let mut expr = Self::from_term_lower(body, &extended_env)?;
                for (name, value) in lowered.into_iter().rev() {
                    expr = Self::Let(name, Box::new(value), Box::new(expr));
                }
                Ok(expr)
            }
            SyGuSTerm::Exists(_, _) | SyGuSTerm::Forall(_, _) => Err(new_custom_error_span(
                format!("Unrecongnized Expression: {}", term),
                empty_span(),
            )),
        }
    }

    #[cfg(feature = "chatgpt")]
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
        if let OwnedExpr::Var(_, _) = self {
            return 1;
        }
        if let OwnedExpr::Concat(a, b) = self {
            return 1 + a.size() + b.size();
        }
        if let OwnedExpr::Extract(a, _, _) = self {
            return 1 + a.size();
        }
        if let OwnedExpr::Func(_, args) = self {
            return 1 + args.iter().map(OwnedExpr::size).sum::<usize>();
        }
        if let OwnedExpr::Const(_) = self {
            return 1;
        }
        if let OwnedExpr::Let(_, value, body) = self {
            return 1 + value.size() + body.size();
        }
        if let OwnedExpr::Ite(a, b, c) = self {
            return 1 + a.size() + b.size() + c.size();
        }
        if let OwnedExpr::BVule(a, b) = self { return 1 + a.size() + b.size(); }
        if let OwnedExpr::BVult(a, b) = self { return 1 + a.size() + b.size(); }
        if let OwnedExpr::BVsle(a, b) = self { return 1 + a.size() + b.size(); }
        if let OwnedExpr::BVslt(a, b) = self { return 1 + a.size() + b.size(); }
        all_ops!(arity);
        panic!();
    }

    pub fn to_sygus(&self, arg_names: &[&str]) -> String {
        let scoped = arg_names.iter().map(|name| (*name).to_string()).collect::<Vec<_>>();
        self.to_sygus_with_env(&scoped)
    }

    fn to_sygus_with_env(&self, names: &[String]) -> String {
        macro_rules! foreach_op {
            (1, $op:ident) => {
                if let OwnedExpr::$op(a) = self {
                    return format!("({} {})", smt_name_of!($op), a.to_sygus_with_env(names));
                }
            };
            (2, $op:ident) => {
                if let OwnedExpr::$op(a, b) = self {
                    return format!(
                        "({} {} {})",
                        smt_name_of!($op),
                        a.to_sygus_with_env(names),
                        b.to_sygus_with_env(names)
                    );
                }
            };
        }
        if let OwnedExpr::Var(i, _) = self {
            return names
                .get(*i)
                .map(|name| (*name).to_string())
                .unwrap_or_else(|| format!("v{i}"));
        }
        if let OwnedExpr::Concat(a, b) = self {
            return format!(
                "(concat {} {})",
                a.to_sygus_with_env(names),
                b.to_sygus_with_env(names)
            );
        }
        if let OwnedExpr::Extract(a, hi, lo) = self {
            return format!("((_ extract {} {}) {})", hi, lo, a.to_sygus_with_env(names));
        }
        if let OwnedExpr::Func(id, args) = self {
            if args.is_empty() {
                return deffun::ENV.name(*id).to_string();
            }
            let rendered_args = args
                .iter()
                .map(|arg| arg.to_sygus_with_env(names))
                .collect::<Vec<_>>()
                .join(" ");
            return format!("({} {})", deffun::ENV.name(*id), rendered_args);
        }
        if let OwnedExpr::Const(c) = self {
            return c.to_string();
        }
        if let OwnedExpr::Let(name, value, body) = self {
            let mut scoped = names.to_vec();
            scoped.push(name.clone());
            return format!(
                "(let (({} {})) {})",
                name,
                value.to_sygus_with_env(names),
                body.to_sygus_with_env(&scoped)
            );
        }
        if let OwnedExpr::Ite(a, b, c) = self {
            let cond_str = a.to_sygus_with_env(names);
            let cond_is_bool = matches!(
                a.as_ref(),
                OwnedExpr::BVule(_, _)
                    | OwnedExpr::BVult(_, _)
                    | OwnedExpr::BVsle(_, _)
                    | OwnedExpr::BVslt(_, _)
            );
            let cond_fmt = if cond_is_bool {
                cond_str
            } else {
                let w = a.width();
                if w <= 3 {
                    let zeros = "0".repeat(w.max(1));
                    format!("(= {} #b{})", cond_str, zeros)
                } else {
                    let zeros = "0".repeat(w.div_ceil(4).max(1));
                    format!("(= {} #x{})", cond_str, zeros)
                }
            };
            return format!(
                "(ite {} {} {})",
                cond_fmt,
                b.to_sygus_with_env(names),
                c.to_sygus_with_env(names)
            );
        }
        if let OwnedExpr::BVule(a, b) = self { return format!("(bvule {} {})", a.to_sygus_with_env(names), b.to_sygus_with_env(names)); }
        if let OwnedExpr::BVult(a, b) = self { return format!("(bvult {} {})", a.to_sygus_with_env(names), b.to_sygus_with_env(names)); }
        if let OwnedExpr::BVsle(a, b) = self { return format!("(bvsle {} {})", a.to_sygus_with_env(names), b.to_sygus_with_env(names)); }
        if let OwnedExpr::BVslt(a, b) = self { return format!("(bvslt {} {})", a.to_sygus_with_env(names), b.to_sygus_with_env(names)); }
        all_ops!(arity);
        unreachable!()
    }
}

impl<'a> From<&Expr<'a>> for OwnedExpr {
    fn from(value: &Expr<'a>) -> Self {
        if let Expr::Var(i, w) = value {
            return OwnedExpr::Var(*i, *w);
        }
        if let Expr::Concat(a, b) = value {
            return OwnedExpr::Concat(Box::new((*a).into()), Box::new((*b).into()));
        }
        if let Expr::Extract(a, hi, lo) = value {
            return OwnedExpr::Extract(Box::new((*a).into()), *hi, *lo);
        }
        if let Expr::Func(id, args_expr) = value {
            return OwnedExpr::Func(*id, args_expr.iter().map(|a| (*a).into()).collect());
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
        if let Expr::BVule(a, b) = value { return OwnedExpr::BVule(Box::new((*a).into()), Box::new((*b).into())); }
        if let Expr::BVult(a, b) = value { return OwnedExpr::BVult(Box::new((*a).into()), Box::new((*b).into())); }
        if let Expr::BVsle(a, b) = value { return OwnedExpr::BVsle(Box::new((*a).into()), Box::new((*b).into())); }
        if let Expr::BVslt(a, b) = value { return OwnedExpr::BVslt(Box::new((*a).into()), Box::new((*b).into())); }
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
    ($v:literal) => { OwnedExpr::Var($v as usize, 64) };
    ([$v:expr]) => { OwnedExpr::Const(crate::enumerate::value::BitVec::from_u64($v as u64, 64)) };
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

    /// SMT-LIB indexed bit-vector literals `(_ bvDECIMAL WIDTH)` lift to a
    /// `Const` of the right width/value (the gap that blocked lowering the
    /// founded-encoding define-funs into plans).
    #[test]
    fn indexed_bv_literal_lifts_to_const() {
        use super::OwnedExpr;
        use crate::enumerate::value::BitVec;
        use sygus_parser::ast::{SyGuSCmd, SyGuSFile};

        for (src, val, width) in [("(_ bv5 8)", 5u64, 8usize), ("(_ bv0 977)", 0, 977)] {
            let wrapped = format!("(define-fun f () (_ BitVec {width}) {src})");
            let file = SyGuSFile::from_str(&wrapped).unwrap();
            let body = file
                .cmds
                .iter()
                .find_map(|c| match c {
                    SyGuSCmd::DefineFun(_, _, _, b) => Some(b),
                    _ => None,
                })
                .unwrap();
            match OwnedExpr::from_term(body, &[]).unwrap() {
                OwnedExpr::Const(v) => assert_eq!(v, BitVec::from_u64(val, width)),
                _ => panic!("`{src}` did not lift to a Const"),
            }
        }
    }

    /// A `bvult` over bit-slices now lowers to a `BitCircuit` plan (the founded
    /// rank comparison), instead of falling back to `Generic` — and evaluates to
    /// the same truth value as the arithmetic comparison.
    #[test]
    fn bvult_on_slices_lowers_to_bitcircuit() {
        use super::OwnedExpr;
        use crate::enumerate::value::BitVec;
        use crate::parse::deffun::DefineFunPlan;

        // f(x: 4 bits) = bvult(x[1:0], x[3:2])
        let slice = |hi, lo| {
            OwnedExpr::Extract(Box::new(OwnedExpr::Var(0, 4)), hi, lo)
        };
        let body = OwnedExpr::BVult(Box::new(slice(1, 0)), Box::new(slice(3, 2)));
        let plan = DefineFunPlan::compile(&body, &[4]);
        let DefineFunPlan::BitCircuit(bc) = &plan else {
            panic!("bvult-on-slices should lower to BitCircuit, got Generic");
        };
        // Spot-check semantics against the real comparator for all 16 inputs.
        for x in 0u64..16 {
            let lo = x & 0b11;
            let hi = (x >> 2) & 0b11;
            let got = bc.eval(&[BitVec::from_u64(x, 4)]).unwrap();
            assert_eq!(got, BitVec::from_u64((lo < hi) as u64, 1), "x={x}");
        }
    }
}

impl OwnedExpr {
    pub fn width(&self) -> usize {
        match self {
            OwnedExpr::Concat(a, b) => a.width() + b.width(),
            OwnedExpr::Extract(_, hi, lo) => (hi - lo + 1) as usize,
            OwnedExpr::Func(id, _) => deffun::ENV.ret_bits(*id),
            OwnedExpr::Const(v) => v.bits(),
            OwnedExpr::Var(_, width) => *width,
            OwnedExpr::Let(_, _, body) => body.width(),
            OwnedExpr::Not(a) | OwnedExpr::Neg(a) => a.width(),
            OwnedExpr::Add(a, _)
            | OwnedExpr::Xor(a, _)
            | OwnedExpr::And(a, _)
            | OwnedExpr::Or(a, _)
            | OwnedExpr::Mul(a, _)
            | OwnedExpr::Sub(a, _)
            | OwnedExpr::LShr(a, _)
            | OwnedExpr::AShr(a, _)
            | OwnedExpr::Shl(a, _)
            | OwnedExpr::UDiv(a, _)
            | OwnedExpr::URem(a, _)
            | OwnedExpr::SDiv(a, _)
            | OwnedExpr::SRem(a, _) => a.width(),
            OwnedExpr::Ite(_, a, _) => a.width(),
            OwnedExpr::BVule(_, _) | OwnedExpr::BVult(_, _) | OwnedExpr::BVsle(_, _) | OwnedExpr::BVslt(_, _) => 1,
            OwnedExpr::SynthApp(idx, _) => deffun::synth_ret_bits(*idx),
        }
    }

    /// Render this expression as a string, truncated to roughly `limit`
    /// characters with a `... <N chars total>` suffix when it overflows.
    /// Used by deffun logging to keep huge compiled bodies grep-able.
    pub fn summarize(&self, limit: usize) -> String {
        let rendered = self.to_string();
        let total = rendered.chars().count();
        if total <= limit {
            return rendered;
        }
        let prefix = rendered.chars().take(limit).collect::<String>();
        format!("{prefix}... <{} chars total>", total)
    }

    fn eval_bv_let_chain<const N: usize>(&self, args: &[Bv<N>]) -> Bv<N> {
        let mut scoped = args.to_vec();
        let mut current = self;
        loop {
            match current {
                OwnedExpr::Let(_, value, body) => {
                    let bound = value.eval_bv(&scoped);
                    scoped.push(bound);
                    current = body;
                }
                other => return other.eval_bv(&scoped),
            }
        }
    }

    pub fn eval(&self, args: &[BitVec]) -> Result<BitVec, DivideByZero> {
        self.eval_with_bindings(args, &[])
    }

    /// Like `eval`, but threads `bindings` into nested `Func` calls so a
    /// define-fun body that references a synth-fun (via `closure_args`)
    /// resolves the right value for it. `args` populates `Var(N)` slots
    /// (formal parameters of the candidate). `bindings` is a name→value
    /// lookup for synth-fun substitution. Pass `&[]` for direct mode.
    pub fn eval_with_bindings(
        &self,
        args: &[BitVec],
        bindings: &[(&str, &BitVec)],
    ) -> Result<BitVec, DivideByZero> {
        macro_rules! foreach_op {
            (1, false, $op: ident) => {
                if let OwnedExpr::$op(e1) = self {
                    return Ok(crate::op_of![$op](e1.eval_with_bindings(args, bindings)?));
                }
            };
            (2, false, $op: ident) => {
                if let OwnedExpr::$op(e1, e2) = self {
                    return Ok(crate::op_of![$op](
                        e1.eval_with_bindings(args, bindings)?,
                        e2.eval_with_bindings(args, bindings)?,
                    ));
                }
            };
            (2, true, $op: ident) => {
                if let OwnedExpr::$op(e1, e2) = self {
                    return crate::op_of![$op](
                        e1.eval_with_bindings(args, bindings)?,
                        e2.eval_with_bindings(args, bindings)?,
                    );
                }
            };
        }
        if let OwnedExpr::Var(a, _) = self {
            return Ok(args[*a].clone());
        }
        if let OwnedExpr::Concat(a, b) = self {
            let lhs = a.eval_with_bindings(args, bindings)?;
            let rhs = b.eval_with_bindings(args, bindings)?;
            return Ok(lhs.concat(&rhs));
        }
        if let OwnedExpr::Extract(a, hi, lo) = self {
            let value = a.eval_with_bindings(args, bindings)?;
            return Ok(value.extract(*hi, *lo));
        }
        if let OwnedExpr::Func(id, exprs) = self {
            let values = exprs
                .iter()
                .map(|expr| expr.eval_with_bindings(args, bindings))
                .collect::<Result<Vec<_>, _>>()?;
            return deffun::ENV.eval_defined(*id, &values, bindings);
        }
        if let OwnedExpr::Const(a) = self {
            return Ok(a.clone());
        }
        if let OwnedExpr::Let(_, _, _) = self {
            return self.eval_let_chain_with_bindings(args, bindings);
        }
        if let OwnedExpr::Ite(e1, e2, e3) = self {
            return Ok(op::ite(
                e1.eval_with_bindings(args, bindings)?,
                e2.eval_with_bindings(args, bindings)?,
                e3.eval_with_bindings(args, bindings)?,
            ));
        }
        if let OwnedExpr::BVule(a, b) = self {
            return Ok(op::ule(a.eval_with_bindings(args, bindings)?, b.eval_with_bindings(args, bindings)?));
        }
        if let OwnedExpr::BVult(a, b) = self {
            return Ok(op::ult(a.eval_with_bindings(args, bindings)?, b.eval_with_bindings(args, bindings)?));
        }
        if let OwnedExpr::BVsle(a, b) = self {
            return Ok(op::sle(a.eval_with_bindings(args, bindings)?, b.eval_with_bindings(args, bindings)?));
        }
        if let OwnedExpr::BVslt(a, b) = self {
            return Ok(op::slt(a.eval_with_bindings(args, bindings)?, b.eval_with_bindings(args, bindings)?));
        }
        if let OwnedExpr::SynthApp(synth_idx, call_args) = self {
            let evaled_args = call_args
                .iter()
                .map(|a| a.eval_with_bindings(args, bindings))
                .collect::<Result<Vec<_>, _>>()?;
            // Cache `(synth_idx, args) → body_value` across the lifetime of
            // the current candidate. Multiple structural constraints invoke
            // `SynthApp` with identical evaled args; without this cache we
            // re-walk the (possibly large) candidate body once per
            // constraint. `set_candidate` clears the cache.
            if let Some(v) = deffun::synth_app_lookup(*synth_idx, &evaled_args) {
                return Ok(v);
            }
            let body = deffun::get_candidate(*synth_idx).unwrap_or_else(|| {
                panic!(
                    "OwnedExpr::SynthApp eval: no current candidate set for synth_idx={synth_idx}"
                )
            });
            let v = body.eval_with_bindings(&evaled_args, bindings)?;
            deffun::synth_app_insert(*synth_idx, &evaled_args, v.clone());
            return Ok(v);
        }
        all_ops!(arity nonzero);
        panic!("should not reach here.");
    }

    fn eval_let_chain_with_bindings(
        &self,
        args: &[BitVec],
        bindings: &[(&str, &BitVec)],
    ) -> Result<BitVec, DivideByZero> {
        let mut scoped = args.to_vec();
        let mut current = self;
        loop {
            match current {
                OwnedExpr::Let(_, value, body) => {
                    let bound = value.eval_with_bindings(&scoped, bindings)?;
                    scoped.push(bound);
                    current = body;
                }
                other => return other.eval_with_bindings(&scoped, bindings),
            }
        }
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
        if let OwnedExpr::Var(a, _) = self {
            return args[*a];
        }
        if let OwnedExpr::Concat(a, b) = self {
            return a.eval_bv(args).concat_low(b.eval_bv(args), b.width());
        }
        if let OwnedExpr::Extract(a, hi, lo) = self {
            return a.eval_bv(args).extract(*hi, *lo);
        }
        if let OwnedExpr::Func(id, exprs) = self {
            let values = exprs.iter().map(|expr| expr.eval_bv(args)).collect::<Vec<_>>();
            return deffun::ENV.apply(*id).eval_bv(&values);
        }
        if let OwnedExpr::Const(a) = self {
            return Bv([a.as_u64_lossy(); N].into());
        }
        if let OwnedExpr::Let(_, _, _) = self {
            return self.eval_bv_let_chain(args);
        }
        if let OwnedExpr::Ite(e1, e2, e3) = self {
            return op::bv::ite(e1.eval_bv(args), e2.eval_bv(args), e3.eval_bv(args));
        }
        if let OwnedExpr::BVule(a, b) = self { return op::bv::ule(a.eval_bv(args), b.eval_bv(args)); }
        if let OwnedExpr::BVult(a, b) = self { return op::bv::ult(a.eval_bv(args), b.eval_bv(args)); }
        if let OwnedExpr::BVsle(a, b) = self { return op::bv::sle(a.eval_bv(args), b.eval_bv(args)); }
        if let OwnedExpr::BVslt(a, b) = self { return op::bv::slt(a.eval_bv(args), b.eval_bv(args)); }
        all_ops!(arity);
        panic!("Should not reach here.")
    }
}
