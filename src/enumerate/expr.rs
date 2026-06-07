use bumpalo::Bump;
use derive_more::{DebugCustom, Display};
use sygus_parser::ast::{Identifier, SyGuSTerm};
use thiserror::Error;
// use z3::{ast::{BV, Ast}, Symbol};

use crate::{
    all_ops, enum_expr, enum_ownedexpr,
    enumerate::op,
    enumerate::value::BitVec,
    parse::{self, deffun, empty_span, new_custom_error_span},
    smt_name_of,
};


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
            return deffun::ENV.eval_defined(*id, &values);
        }
        if let Expr::Const(a) = self {
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
}

enum_ownedexpr!();

impl OwnedExpr {
    pub fn from_term(term: &SyGuSTerm, env: &[(&str, u64)]) -> parse::Result<Self> {
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
            if name.eq_ignore_ascii_case("true") {
                Some(Ok(BitVec::from_u64(1, 1)))
            } else if name.eq_ignore_ascii_case("false") {
                Some(Ok(BitVec::from_u64(0, 1)))
            } else if let Some(digits) = name.strip_prefix("#x") {
                let bits = digits.len() * 4;
                Some(crate::parse::constraint::parse_bv_digits(digits, 16, bits.max(1)))
            } else if let Some(digits) = name.strip_prefix("#b") {
                let bits = digits.len();
                Some(crate::parse::constraint::parse_bv_digits(digits, 2, bits.max(1)))
            } else if let Some(digits) = name.strip_prefix("#d") {
                Some(crate::parse::constraint::parse_bv_digits(digits, 10, 64))
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
                } else {
                    Err(new_custom_error_span(
                        "Unrecongnized Variable".into(),
                        empty_span(),
                    ))
                }
            }
            SyGuSTerm::Literal(lit) => Ok(Self::Const(crate::parse::literal_to_value(lit)?)),
            SyGuSTerm::Annotated(inner, _) => Self::from_term(inner, env),
            SyGuSTerm::Application(id, args) => {
                let opname = symbol_name(id);
                if args.len() == 1 {
                    if let Some((hi, lo)) = extract_indices(id) {
                        return Ok(Self::Extract(
                            Self::from_term(&args[0], env)?.into(),
                            hi,
                            lo,
                        ));
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
                operator2!("bvule", BVule);
                operator2!("bvult", BVult);
                operator2!("bvsle", BVsle);
                operator2!("bvslt", BVslt);
                if opname == "bvugt" && args.len() == 2 {
                    return Ok(Self::BVult(Box::new(Self::from_term(&args[1], env)?), Box::new(Self::from_term(&args[0], env)?)));
                }
                if opname == "bvuge" && args.len() == 2 {
                    return Ok(Self::BVule(Box::new(Self::from_term(&args[1], env)?), Box::new(Self::from_term(&args[0], env)?)));
                }
                if opname == "bvsgt" && args.len() == 2 {
                    return Ok(Self::BVslt(Box::new(Self::from_term(&args[1], env)?), Box::new(Self::from_term(&args[0], env)?)));
                }
                if opname == "bvsge" && args.len() == 2 {
                    return Ok(Self::BVsle(Box::new(Self::from_term(&args[1], env)?), Box::new(Self::from_term(&args[0], env)?)));
                }
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
                if let Some(fid) = deffun::ENV.lookup(opname, args.len()) {
                    return Ok(Self::Func(
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
            SyGuSTerm::Let(bindings, body) => {
                let mut extended_env = env.to_vec();
                let mut lowered = Vec::with_capacity(bindings.len());
                for binding in bindings {
                    let value = Self::from_term(&binding.term, &extended_env)?;
                    let width = value.width() as u64;
                    let leaked = Box::leak(binding.name.clone().into_boxed_str()) as &'static str;
                    extended_env.push((leaked, width));
                    lowered.push((binding.name.clone(), value));
                }
                let mut expr = Self::from_term(body, &extended_env)?;
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

    fn eval_let_chain(&self, args: &[BitVec]) -> Result<BitVec, DivideByZero> {
        let mut scoped = args.to_vec();
        let mut current = self;
        loop {
            match current {
                OwnedExpr::Let(_, value, body) => {
                    let bound = value.eval(&scoped)?;
                    scoped.push(bound);
                    current = body;
                }
                other => return other.eval(&scoped),
            }
        }
    }


    pub fn eval(&self, args: &[BitVec]) -> Result<BitVec, DivideByZero> {
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
        if let OwnedExpr::Var(a, _) = self {
            return Ok(args[*a].clone());
        }
        if let OwnedExpr::Concat(a, b) = self {
            let lhs = a.eval(args)?;
            let rhs = b.eval(args)?;
            return Ok(lhs.concat(&rhs));
        }
        if let OwnedExpr::Extract(a, hi, lo) = self {
            let value = a.eval(args)?;
            return Ok(value.extract(*hi, *lo));
        }
        if let OwnedExpr::Func(id, exprs) = self {
            let values = exprs
                .iter()
                .map(|expr| expr.eval(args))
                .collect::<Result<Vec<_>, _>>()?;
            return deffun::ENV.eval_defined(*id, &values);
        }
        if let OwnedExpr::Const(a) = self {
            return Ok(a.clone());
        }
        if let OwnedExpr::Let(_, _, _) = self {
            return self.eval_let_chain(args);
        }
        if let OwnedExpr::Ite(e1, e2, e3) = self {
            return Ok(op::ite(e1.eval(args)?, e2.eval(args)?, e3.eval(args)?));
        }
        if let OwnedExpr::BVule(a, b) = self { return Ok(op::ule(a.eval(args)?, b.eval(args)?)); }
        if let OwnedExpr::BVult(a, b) = self { return Ok(op::ult(a.eval(args)?, b.eval(args)?)); }
        if let OwnedExpr::BVsle(a, b) = self { return Ok(op::sle(a.eval(args)?, b.eval(args)?)); }
        if let OwnedExpr::BVslt(a, b) = self { return Ok(op::slt(a.eval(args)?, b.eval(args)?)); }
        all_ops!(arity nonzero);
        panic!("should not reach here.");
    }
}
