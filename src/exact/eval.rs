use crate::enumerate::{expr::OwnedExpr, grammar::build_owned_application, value::Value};

use super::{ExactEvalCache, TemplateExpr};

pub fn evaluate_template_value(
    template: &TemplateExpr,
    args: &[Value],
    cache: &mut ExactEvalCache,
) -> Result<Value, ()> {
    match template {
        TemplateExpr::Slot(i) => Ok(args[*i].clone()),
        TemplateExpr::Leaf(expr) => cache
            .leaves
            .entry(expr.clone())
            .or_insert_with(|| expr.eval(&[]).ok())
            .clone()
            .ok_or(()),
        TemplateExpr::App(id, parts) => {
            let values = parts
                .iter()
                .map(|part| evaluate_template_value(part, args, cache))
                .collect::<Result<Vec<_>, _>>()?;
            let const_args = values
                .iter()
                .cloned()
                .map(OwnedExpr::Const)
                .collect::<Vec<_>>();
            build_owned_application(id, &const_args)
                .ok()
                .and_then(|expr| expr.eval(&[]).ok())
                .ok_or(())
        }
    }
}

pub fn evaluate_fop1(fid: usize, arg: &Value) -> Result<Value, ()> {
    let value = crate::parse::deffun::ENV
        .eval_defined(fid, 1, std::slice::from_ref(arg))
        .ok();
    value.ok_or(())
}

pub fn evaluate_fop2(fid: usize, lhs: &Value, rhs: &Value) -> Result<Value, ()> {
    let args = [lhs.clone(), rhs.clone()];
    let value = crate::parse::deffun::ENV.eval_defined(fid, 2, &args).ok();
    value.ok_or(())
}

pub fn evaluate_fopn(fid: usize, args: &[Value]) -> Result<Value, ()> {
    let arity = args.len();
    let value = crate::parse::deffun::ENV
        .eval_defined(fid, arity, args)
        .ok();
    value.ok_or(())
}
