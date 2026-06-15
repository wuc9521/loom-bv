//! Core data types for the exact-nullary search engine: `Node` /
//! `Grammar` / `ExactRule` describe the compiled grammar, `Candidate`
//! is the search-time tuple of (NodeId, value, value_top), and
//! `ExactEvalCache` is the leaf-eval memo used by `TemplateExpr::evaluate`.

use rustc_hash::FxHashMap;

use crate::enumerate::{
    expr::OwnedExpr,
    grammar::{RuleClass, TemplateExpr},
    value::BitVec,
};

pub type NodeId = usize;

pub struct Node {
    pub nt_idx: usize,
    pub rule_idx: usize,
    pub children: Vec<NodeId>,
}

#[derive(Clone)]
pub struct Grammar<'a> {
    pub nts: Vec<(&'a str, Vec<ExactRule>)>,
    pub start: usize,
}

#[derive(Clone)]
pub enum ExactRule {
    Alias(usize),
    Leaf(OwnedExpr),
    Op {
        fid: usize,
        child_nts: Vec<usize>,
        class: RuleClass,
    },
    GenericTemplate {
        template: TemplateExpr,
        child_nts: Vec<usize>,
        base_size: usize,
    },
}

#[derive(Default)]
pub struct ExactEvalCache {
    pub leaves: FxHashMap<OwnedExpr, Option<BitVec>>,
}

impl TemplateExpr {
    pub fn evaluate(
        &self,
        args: &[BitVec],
        cache: &mut ExactEvalCache,
    ) -> Result<BitVec, ()> {
        match self {
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
                    .map(|part| part.evaluate(args, cache))
                    .collect::<Result<Vec<_>, _>>()?;
                eval_op_on_values(id.get_name(), &values)
            }
        }
    }

    pub fn evaluate_with_args(
        &self,
        synth_args: &[BitVec],
        cache: &mut ExactEvalCache,
    ) -> Result<BitVec, ()> {
        match self {
            TemplateExpr::Slot(_) => Err(()),
            TemplateExpr::Leaf(expr) => {
                if synth_args.is_empty() {
                    cache
                        .leaves
                        .entry(expr.clone())
                        .or_insert_with(|| expr.eval(&[]).ok())
                        .clone()
                        .ok_or(())
                } else {
                    expr.eval(synth_args).map_err(|_| ())
                }
            }
            TemplateExpr::App(id, parts) => {
                let values = parts
                    .iter()
                    .map(|part| part.evaluate_with_args(synth_args, cache))
                    .collect::<Result<Vec<_>, _>>()?;
                eval_op_on_values(id.get_name(), &values)
            }
        }
    }

    pub fn evaluate_with_args_and_children(
        &self,
        synth_args: &[BitVec],
        children: &[BitVec],
        cache: &mut ExactEvalCache,
    ) -> Result<BitVec, ()> {
        match self {
            TemplateExpr::Slot(i) => Ok(children[*i].clone()),
            TemplateExpr::Leaf(expr) => {
                if synth_args.is_empty() {
                    cache
                        .leaves
                        .entry(expr.clone())
                        .or_insert_with(|| expr.eval(&[]).ok())
                        .clone()
                        .ok_or(())
                } else {
                    expr.eval(synth_args).map_err(|_| ())
                }
            }
            TemplateExpr::App(id, parts) => {
                let values = parts
                    .iter()
                    .map(|part| part.evaluate_with_args_and_children(synth_args, children, cache))
                    .collect::<Result<Vec<_>, _>>()?;
                eval_op_on_values(id.get_name(), &values)
            }
        }
    }
}

fn eval_op_on_values(op: &str, values: &[BitVec]) -> Result<BitVec, ()> {
    use crate::enumerate::op;
    use crate::parse::deffun;
    match (op, values.len()) {
        ("bvnot" | "not", 1) => Ok(values[0].clone().bitnot()),
        ("bvneg", 1) => Ok(values[0].clone().neg()),
        ("bvand", 2) => Ok(values[0].clone().bitand(values[1].clone())),
        ("bvor", 2) => Ok(values[0].clone().bitor(values[1].clone())),
        ("bvxor", 2) | ("=", 2) => Ok(values[0].clone().bitxor(values[1].clone())),
        ("bvadd", 2) => Ok(values[0].clone().add(values[1].clone())),
        ("bvsub", 2) => Ok(values[0].clone().sub(values[1].clone())),
        ("bvmul", 2) => Ok(values[0].clone().mul(values[1].clone())),
        ("bvudiv", 2) => values[0].clone().udiv(values[1].clone()).ok_or(()),
        ("bvurem", 2) => values[0].clone().urem(values[1].clone()).ok_or(()),
        ("bvsdiv", 2) => values[0].clone().sdiv(values[1].clone()).ok_or(()),
        ("bvsrem", 2) => values[0].clone().srem(values[1].clone()).ok_or(()),
        ("bvlshr", 2) => Ok(values[0].clone().lshr(values[1].clone())),
        ("bvashr", 2) => Ok(values[0].clone().ashr(values[1].clone())),
        ("bvshl", 2) => Ok(values[0].clone().shl(values[1].clone())),
        ("concat", 2) => Ok(values[0].concat(&values[1])),
        ("bvule", 2) => Ok(op::ule(values[0].clone(), values[1].clone())),
        ("bvult", 2) => Ok(op::ult(values[0].clone(), values[1].clone())),
        ("bvsle", 2) => Ok(op::sle(values[0].clone(), values[1].clone())),
        ("bvslt", 2) => Ok(op::slt(values[0].clone(), values[1].clone())),
        ("bvugt", 2) => Ok(op::ult(values[1].clone(), values[0].clone())),
        ("bvuge", 2) => Ok(op::ule(values[1].clone(), values[0].clone())),
        ("bvsgt", 2) => Ok(op::slt(values[1].clone(), values[0].clone())),
        ("bvsge", 2) => Ok(op::sle(values[1].clone(), values[0].clone())),
        ("and", n) if n >= 2 => {
            let mut acc = values[0].clone();
            for a in &values[1..] { acc = acc.bitor(a.clone()); }
            Ok(acc)
        }
        ("or", n) if n >= 2 => {
            let mut acc = values[0].clone();
            for a in &values[1..] { acc = acc.bitand(a.clone()); }
            Ok(acc)
        }
        ("ite", 3) => Ok(op::ite(values[0].clone(), values[1].clone(), values[2].clone())),
        _ => {
            if let Some(fid) = deffun::ENV.lookup(op, values.len()) {
                deffun::ENV.eval_defined(fid, values, &[]).map_err(|_| ())
            } else {
                Err(())
            }
        }
    }
}

/// A search-time candidate term in a sub-NT pool.
///
/// `values` holds one evaluation per example (K values). In direct mode with
/// K=1, this degenerates to a single value. In fixpoint mode, `values_top`
/// holds evaluations at `aux=top` — together with `values` (at `aux=0`) they
/// form the two-sample fingerprint for sound sub-NT dedup. Start-NT candidates
#[derive(Clone)]
pub struct Candidate {
    pub node: NodeId,
    pub values: Vec<BitVec>,
}
