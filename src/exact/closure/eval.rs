//! Value-level evaluation against `deffun::ENV` with a closure parameter.
//!
//! All eval functions take a single `closure_value` that is bound to every
//! reference of the closure synth-fun (named by `closure_name`) encountered
//! during evaluation — either via `closure_arg_values` resolving the env's
//! recorded closure-arg slots, or via direct substitution in `OwnedExpr::Var`.


use crate::enumerate::expr::OwnedExpr;
use crate::enumerate::value::Value;
use crate::parse::{self, deffun, new_custom_error_span};


use super::spec::empty_span;

pub fn eval_owned_with_closure(
    expr: &OwnedExpr,
    env: &deffun::Environ,
    closure_value: &Value,
    closure_name: &str,
) -> parse::Result<Value> {
    match expr {
        OwnedExpr::Const(v) => Ok(v.clone()),
        OwnedExpr::Var(_, _) => Ok(closure_value.clone()),
        OwnedExpr::Concat(a, b) => Ok(eval_owned_with_closure(a, env, closure_value, closure_name)?
            .concat(&eval_owned_with_closure(b, env, closure_value, closure_name)?)),
        OwnedExpr::Extract(a, hi, lo) => Ok(eval_owned_with_closure(a, env, closure_value, closure_name)?
            .extract(*hi, *lo)),
        OwnedExpr::Not(a) => Ok(eval_owned_with_closure(a, env, closure_value, closure_name)?.bitnot()),
        OwnedExpr::Neg(a) => Ok(eval_owned_with_closure(a, env, closure_value, closure_name)?.neg()),
        OwnedExpr::Add(a, b) => Ok(eval_owned_with_closure(a, env, closure_value, closure_name)?
            .add(eval_owned_with_closure(b, env, closure_value, closure_name)?)),
        OwnedExpr::Xor(a, b) => Ok(eval_owned_with_closure(a, env, closure_value, closure_name)?
            .bitxor(eval_owned_with_closure(b, env, closure_value, closure_name)?)),
        OwnedExpr::And(a, b) => Ok(eval_owned_with_closure(a, env, closure_value, closure_name)?
            .bitand(eval_owned_with_closure(b, env, closure_value, closure_name)?)),
        OwnedExpr::Or(a, b) => Ok(eval_owned_with_closure(a, env, closure_value, closure_name)?
            .bitor(eval_owned_with_closure(b, env, closure_value, closure_name)?)),
        OwnedExpr::Mul(a, b) => Ok(eval_owned_with_closure(a, env, closure_value, closure_name)?
            .mul(eval_owned_with_closure(b, env, closure_value, closure_name)?)),
        OwnedExpr::Sub(a, b) => Ok(eval_owned_with_closure(a, env, closure_value, closure_name)?
            .sub(eval_owned_with_closure(b, env, closure_value, closure_name)?)),
        OwnedExpr::LShr(a, b) => Ok(eval_owned_with_closure(a, env, closure_value, closure_name)?
            .lshr(eval_owned_with_closure(b, env, closure_value, closure_name)?)),
        OwnedExpr::AShr(a, b) => Ok(eval_owned_with_closure(a, env, closure_value, closure_name)?
            .ashr(eval_owned_with_closure(b, env, closure_value, closure_name)?)),
        OwnedExpr::Shl(a, b) => Ok(eval_owned_with_closure(a, env, closure_value, closure_name)?
            .shl(eval_owned_with_closure(b, env, closure_value, closure_name)?)),
        OwnedExpr::UDiv(a, b) => eval_owned_with_closure(a, env, closure_value, closure_name)?
            .udiv(eval_owned_with_closure(b, env, closure_value, closure_name)?)
            .ok_or_else(|| new_custom_error_span("lfp: divide-by-zero".into(), empty_span())),
        OwnedExpr::URem(a, b) => eval_owned_with_closure(a, env, closure_value, closure_name)?
            .urem(eval_owned_with_closure(b, env, closure_value, closure_name)?)
            .ok_or_else(|| new_custom_error_span("lfp: divide-by-zero".into(), empty_span())),
        OwnedExpr::SDiv(a, b) => eval_owned_with_closure(a, env, closure_value, closure_name)?
            .sdiv(eval_owned_with_closure(b, env, closure_value, closure_name)?)
            .ok_or_else(|| new_custom_error_span("lfp: divide-by-zero".into(), empty_span())),
        OwnedExpr::SRem(a, b) => eval_owned_with_closure(a, env, closure_value, closure_name)?
            .srem(eval_owned_with_closure(b, env, closure_value, closure_name)?)
            .ok_or_else(|| new_custom_error_span("lfp: divide-by-zero".into(), empty_span())),
        OwnedExpr::Fop0Dyn(id) => {
            let args = closure_arg_values(env, *id, 0, closure_value, closure_name);
            env.eval_defined(*id, 0, &args)
                .map_err(|_| new_custom_error_span(format!("lfp: divide-by-zero in {}", env.name(*id, 0)), empty_span()))
        }
        OwnedExpr::Fop1Dyn(id, a) => {
            let mut args = vec![eval_owned_with_closure(a, env, closure_value, closure_name)?];
            args.extend(closure_arg_values(env, *id, 1, closure_value, closure_name));
            env.eval_defined(*id, 1, &args)
                .map_err(|_| new_custom_error_span(format!("lfp: divide-by-zero in {}", env.name(*id, 1)), empty_span()))
        }
        OwnedExpr::Fop2Dyn(id, a, b) => {
            let mut args = vec![
                eval_owned_with_closure(a, env, closure_value, closure_name)?,
                eval_owned_with_closure(b, env, closure_value, closure_name)?,
            ];
            args.extend(closure_arg_values(env, *id, 2, closure_value, closure_name));
            env.eval_defined(*id, 2, &args)
                .map_err(|_| new_custom_error_span(format!("lfp: divide-by-zero in {}", env.name(*id, 2)), empty_span()))
        }
        OwnedExpr::FopDyn(id, exprs) => {
            let nargs = exprs.len();
            let mut args = exprs
                .iter()
                .map(|arg| eval_owned_with_closure(arg, env, closure_value, closure_name))
                .collect::<parse::Result<Vec<_>>>()?;
            args.extend(closure_arg_values(env, *id, nargs, closure_value, closure_name));
            env.eval_defined(*id, nargs, &args)
                .map_err(|_| new_custom_error_span(format!("lfp: divide-by-zero in {}", env.name(*id, nargs)), empty_span()))
        }
        OwnedExpr::Ite(cond, then_e, else_e) => {
            let c = eval_owned_with_closure(cond, env, closure_value, closure_name)?;
            if c.is_zero() {
                eval_owned_with_closure(then_e, env, closure_value, closure_name)
            } else {
                eval_owned_with_closure(else_e, env, closure_value, closure_name)
            }
        }
        OwnedExpr::Let(_, _, _) => expr
            .eval(std::slice::from_ref(closure_value))
            .map_err(|_| new_custom_error_span("lfp: let-eval failed".into(), empty_span())),
    }
}

/// Resolve the value of each closure synth-fun the define-fun references.
/// The closure path knows only one closure synth-fun (the LFP target);
/// any others are bound to zero as a placeholder.
pub fn closure_arg_values(
    env: &deffun::Environ,
    id: usize,
    nargs: usize,
    closure_value: &Value,
    closure_name: &str,
) -> Vec<Value> {
    let names = env.closure_args(id, nargs);
    let bits = env.closure_arg_bits(id, nargs);
    names
        .iter()
        .zip(bits.iter())
        .map(|(n, b)| {
            if *n == closure_name {
                closure_value.clone()
            } else {
                Value::from_u64(0, *b)
            }
        })
        .collect()
}





pub fn compute_full_lfp(
    env: &deffun::Environ,
    g_expr: &OwnedExpr,
    closure_name: &str,
    bits: usize,
) -> parse::Result<Value> {
    let mut rhs_s = Value::from_u64(0, bits);
    for _ in 0..=bits {
        let next = eval_owned_with_closure(g_expr, env, &rhs_s, closure_name)?;
        if next == rhs_s {
            return Ok(next);
        }
        rhs_s = next;
    }
    Err(new_custom_error_span(
        "lfp: full LFP did not converge".into(),
        empty_span(),
    ))
}
