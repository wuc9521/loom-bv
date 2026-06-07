//! Core data types for the exact-nullary search engine: `Node` /
//! `Grammar` / `ExactRule` describe the compiled grammar, `Candidate`
//! is the search-time tuple of (NodeId, value, value_top), and
//! `ExactEvalCache` is the leaf-eval memo used by `TemplateExpr::evaluate`.

use rustc_hash::FxHashMap;

use crate::enumerate::{
    expr::OwnedExpr,
    grammar::{build_owned_application, RuleClass, TemplateExpr},
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
    /// Evaluate a `TemplateExpr` rule from the exact-search grammar at
    /// concrete argument values. Caches the leaf evaluations because the
    /// same constant leaf appears across many template instantiations.
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
                let const_args = values.into_iter().map(OwnedExpr::Const).collect::<Vec<_>>();
                build_owned_application(id, &const_args)
                    .ok()
                    .and_then(|expr| expr.eval(&[]).ok())
                    .ok_or(())
            }
        }
    }

    /// Evaluate a childless template with synth-fun example args.
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
                let const_args = values.into_iter().map(OwnedExpr::Const).collect::<Vec<_>>();
                build_owned_application(id, &const_args)
                    .ok()
                    .and_then(|expr| expr.eval(&[]).ok())
                    .ok_or(())
            }
        }
    }

    /// Evaluate a template with both synth-fun args and child-NT slot values.
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
                let const_args = values.into_iter().map(OwnedExpr::Const).collect::<Vec<_>>();
                build_owned_application(id, &const_args)
                    .ok()
                    .and_then(|expr| expr.eval(&[]).ok())
                    .ok_or(())
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
/// in fixpoint mode store the converged LFP in `values` and `None` in
/// `values_top`.
#[derive(Clone)]
pub struct Candidate {
    pub node: NodeId,
    pub values: Vec<BitVec>,
    pub values_top: Option<Vec<BitVec>>,
}
