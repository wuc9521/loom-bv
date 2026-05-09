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

pub fn evaluate_fop1(fid: usize, arg: &Value, cache: &mut ExactEvalCache) -> Result<Value, ()> {
    cache
        .fop1
        .entry((fid, arg.clone()))
        .or_insert_with(|| {
            crate::parse::deffun::ENV
                .apply(fid, 1)
                .eval(std::slice::from_ref(arg))
                .ok()
        })
        .clone()
        .ok_or(())
}

pub fn evaluate_fop2(
    fid: usize,
    lhs: &Value,
    rhs: &Value,
    cache: &mut ExactEvalCache,
) -> Result<Value, ()> {
    let args = [lhs.clone(), rhs.clone()];
    cache
        .fop2
        .entry((fid, lhs.clone(), rhs.clone()))
        .or_insert_with(|| crate::parse::deffun::ENV.apply(fid, 2).eval(&args).ok())
        .clone()
        .ok_or(())
}

pub fn evaluate_fopn(fid: usize, args: &[Value], cache: &mut ExactEvalCache) -> Result<Value, ()> {
    cache
        .fopn
        .entry((fid, args.to_vec()))
        .or_insert_with(|| {
            crate::parse::deffun::ENV
                .apply(fid, args.len())
                .eval(args)
                .ok()
        })
        .clone()
        .ok_or(())
}
