//! Closure-aware evaluation: like `OwnedExpr::eval` but with `closure_value`
//! bound to every reference of the closure synth-fun named `closure_name`
//! (either as a bare `Var` placeholder or via the env-tracked closure-arg
//! slots that `Environ::eval_defined` expects). All `Fop*Dyn` sites go
//! through `eval::eval_defined_with_closure`, which handles closure-arg
//! assembly + cross-call memoization in one place.

use crate::enumerate::expr::OwnedExpr;
use crate::enumerate::value::Value;
use crate::exact::{eval_defined_with_closure, util::empty_span};
use crate::parse::{self, deffun, new_custom_error_span};

impl OwnedExpr {
    /// Closure-aware evaluation. `closure_value` substitutes for both
    /// (a) bare `Var` placeholders that the parser emits when the operator's
    /// grammar references the closure synth-fun by name, and (b) the
    /// env-tracked closure-arg slots that each `define-fun` body uses.
    pub fn eval_with_closure(
        &self,
        env: &deffun::Environ,
        closure_value: &Value,
        closure_name: &str,
    ) -> parse::Result<Value> {
        let closure = Some((closure_name, closure_value));
        let div_by_zero = || new_custom_error_span("lfp: divide-by-zero".into(), empty_span());
        let fn_div_by_zero = |id: usize, nargs: usize| {
            new_custom_error_span(
                format!("lfp: divide-by-zero in {}", env.name(id, nargs)),
                empty_span(),
            )
        };
        match self {
            OwnedExpr::Const(v) => Ok(v.clone()),
            OwnedExpr::Var(_, _) => Ok(closure_value.clone()),
            OwnedExpr::Concat(a, b) => Ok(a
                .eval_with_closure(env, closure_value, closure_name)?
                .concat(&b.eval_with_closure(env, closure_value, closure_name)?)),
            OwnedExpr::Extract(a, hi, lo) => Ok(a
                .eval_with_closure(env, closure_value, closure_name)?
                .extract(*hi, *lo)),
            OwnedExpr::Not(a) => Ok(a.eval_with_closure(env, closure_value, closure_name)?.bitnot()),
            OwnedExpr::Neg(a) => Ok(a.eval_with_closure(env, closure_value, closure_name)?.neg()),
            OwnedExpr::Add(a, b) => Ok(a
                .eval_with_closure(env, closure_value, closure_name)?
                .add(b.eval_with_closure(env, closure_value, closure_name)?)),
            OwnedExpr::Xor(a, b) => Ok(a
                .eval_with_closure(env, closure_value, closure_name)?
                .bitxor(b.eval_with_closure(env, closure_value, closure_name)?)),
            OwnedExpr::And(a, b) => Ok(a
                .eval_with_closure(env, closure_value, closure_name)?
                .bitand(b.eval_with_closure(env, closure_value, closure_name)?)),
            OwnedExpr::Or(a, b) => Ok(a
                .eval_with_closure(env, closure_value, closure_name)?
                .bitor(b.eval_with_closure(env, closure_value, closure_name)?)),
            OwnedExpr::Mul(a, b) => Ok(a
                .eval_with_closure(env, closure_value, closure_name)?
                .mul(b.eval_with_closure(env, closure_value, closure_name)?)),
            OwnedExpr::Sub(a, b) => Ok(a
                .eval_with_closure(env, closure_value, closure_name)?
                .sub(b.eval_with_closure(env, closure_value, closure_name)?)),
            OwnedExpr::LShr(a, b) => Ok(a
                .eval_with_closure(env, closure_value, closure_name)?
                .lshr(b.eval_with_closure(env, closure_value, closure_name)?)),
            OwnedExpr::AShr(a, b) => Ok(a
                .eval_with_closure(env, closure_value, closure_name)?
                .ashr(b.eval_with_closure(env, closure_value, closure_name)?)),
            OwnedExpr::Shl(a, b) => Ok(a
                .eval_with_closure(env, closure_value, closure_name)?
                .shl(b.eval_with_closure(env, closure_value, closure_name)?)),
            OwnedExpr::UDiv(a, b) => a
                .eval_with_closure(env, closure_value, closure_name)?
                .udiv(b.eval_with_closure(env, closure_value, closure_name)?)
                .ok_or_else(div_by_zero),
            OwnedExpr::URem(a, b) => a
                .eval_with_closure(env, closure_value, closure_name)?
                .urem(b.eval_with_closure(env, closure_value, closure_name)?)
                .ok_or_else(div_by_zero),
            OwnedExpr::SDiv(a, b) => a
                .eval_with_closure(env, closure_value, closure_name)?
                .sdiv(b.eval_with_closure(env, closure_value, closure_name)?)
                .ok_or_else(div_by_zero),
            OwnedExpr::SRem(a, b) => a
                .eval_with_closure(env, closure_value, closure_name)?
                .srem(b.eval_with_closure(env, closure_value, closure_name)?)
                .ok_or_else(div_by_zero),
            OwnedExpr::Fop0Dyn(id) => {
                eval_defined_with_closure(*id, 0, &[], closure).map_err(|_| fn_div_by_zero(*id, 0))
            }
            OwnedExpr::Fop1Dyn(id, a) => {
                let args = [a.eval_with_closure(env, closure_value, closure_name)?];
                eval_defined_with_closure(*id, 1, &args, closure).map_err(|_| fn_div_by_zero(*id, 1))
            }
            OwnedExpr::Fop2Dyn(id, a, b) => {
                let args = [
                    a.eval_with_closure(env, closure_value, closure_name)?,
                    b.eval_with_closure(env, closure_value, closure_name)?,
                ];
                eval_defined_with_closure(*id, 2, &args, closure).map_err(|_| fn_div_by_zero(*id, 2))
            }
            OwnedExpr::FopDyn(id, exprs) => {
                let nargs = exprs.len();
                let args = exprs
                    .iter()
                    .map(|arg| arg.eval_with_closure(env, closure_value, closure_name))
                    .collect::<parse::Result<Vec<_>>>()?;
                eval_defined_with_closure(*id, nargs, &args, closure)
                    .map_err(|_| fn_div_by_zero(*id, nargs))
            }
            OwnedExpr::Ite(cond, then_e, else_e) => {
                let c = cond.eval_with_closure(env, closure_value, closure_name)?;
                if c.as_bool().holds() {
                    then_e.eval_with_closure(env, closure_value, closure_name)
                } else {
                    else_e.eval_with_closure(env, closure_value, closure_name)
                }
            }
            OwnedExpr::Let(_, _, _) => self
                .eval(std::slice::from_ref(closure_value))
                .map_err(|_| new_custom_error_span("lfp: let-eval failed".into(), empty_span())),
        }
    }

    /// Iterate `self` as the body of a closure synth-fun until reaching a
    /// `bits`-wide fixpoint, starting from all-zeros. Bounded by `bits + 1`
    /// iterations (monotone Boolean lattice height).
    pub fn full_lfp(
        &self,
        env: &deffun::Environ,
        closure_name: &str,
        bits: usize,
    ) -> parse::Result<Value> {
        let mut rhs_s = Value::from_u64(0, bits);
        for _ in 0..=bits {
            let next = self.eval_with_closure(env, &rhs_s, closure_name)?;
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
}
