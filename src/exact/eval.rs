use std::collections::hash_map::Entry;
use std::time::Instant;

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
    let start = Instant::now();
    let key = (fid, arg.clone());
    let (hit, value) = match cache.fop1.entry(key) {
        Entry::Occupied(entry) => (true, entry.get().clone()),
        Entry::Vacant(entry) => (
            false,
            entry
                .insert(
                    crate::parse::deffun::ENV
                        .apply(fid, 1)
                        .eval(std::slice::from_ref(arg))
                        .ok(),
                )
                .clone(),
        ),
    };
    cache.record_eval(1, fid, hit, start.elapsed());
    value.ok_or(())
}

pub fn evaluate_fop2(
    fid: usize,
    lhs: &Value,
    rhs: &Value,
    cache: &mut ExactEvalCache,
) -> Result<Value, ()> {
    let start = Instant::now();
    let args = [lhs.clone(), rhs.clone()];
    let key = (fid, lhs.clone(), rhs.clone());
    let (hit, value) = match cache.fop2.entry(key) {
        Entry::Occupied(entry) => (true, entry.get().clone()),
        Entry::Vacant(entry) => (
            false,
            entry
                .insert(crate::parse::deffun::ENV.apply(fid, 2).eval(&args).ok())
                .clone(),
        ),
    };
    cache.record_eval(2, fid, hit, start.elapsed());
    value.ok_or(())
}

pub fn evaluate_fopn(fid: usize, args: &[Value], cache: &mut ExactEvalCache) -> Result<Value, ()> {
    let start = Instant::now();
    let arity = args.len();
    let key = (fid, args.to_vec());
    let (hit, value) = match cache.fopn.entry(key) {
        Entry::Occupied(entry) => (true, entry.get().clone()),
        Entry::Vacant(entry) => (
            false,
            entry
                .insert(crate::parse::deffun::ENV.apply(fid, arity).eval(args).ok())
                .clone(),
        ),
    };
    cache.record_eval(arity, fid, hit, start.elapsed());
    value.ok_or(())
}
