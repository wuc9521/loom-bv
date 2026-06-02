//! Core data types for the exact-nullary search engine: `Node` /
//! `ExactGrammar` / `ExactRule` describe the compiled grammar, `Candidate`
//! is the search-time tuple of (NodeId, value, value_top), and
//! `ExactEvalCache` is the leaf-eval memo used by `TemplateExpr::evaluate`.

use rustc_hash::FxHashMap;

use crate::enumerate::{
    expr::OwnedExpr,
    grammar::{build_owned_application, TemplateExpr},
    value::Value,
};

pub type NodeId = usize;

pub struct Node {
    pub nt_idx: usize,
    pub rule_idx: usize,
    pub children: Vec<NodeId>,
}

#[derive(Clone)]
pub struct ExactGrammar<'a> {
    pub nts: Vec<(&'a str, Vec<ExactRule>)>,
    pub start: usize,
}

#[derive(Clone)]
pub enum ExactRule {
    Alias(usize),
    Leaf(OwnedExpr),
    Unary {
        fid: usize,
        child_nt: usize,
    },
    Binary {
        fid: usize,
        lhs_nt: usize,
        rhs_nt: usize,
    },
    Nary {
        fid: usize,
        child_nts: Vec<usize>,
    },
    GenericTemplate {
        template: TemplateExpr,
        child_nts: Vec<usize>,
        base_size: usize,
    },
}

#[derive(Default)]
pub struct ExactEvalCache {
    pub leaves: FxHashMap<OwnedExpr, Option<Value>>,
}

impl TemplateExpr {
    /// Evaluate a `TemplateExpr` rule from the exact-search grammar at
    /// concrete argument values. Caches the leaf evaluations because the
    /// same constant leaf appears across many template instantiations.
    pub fn evaluate(
        &self,
        args: &[Value],
        cache: &mut ExactEvalCache,
    ) -> Result<Value, ()> {
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
}

/// A search-time candidate term in a sub-NT pool.
///
/// `value` is the candidate's evaluation at `aux=0` (or the only eval in
/// direct mode). `value_top` is set only in fixpoint mode and holds the
/// evaluation at `aux=top` — together they form the two-sample fingerprint
/// used for sound sub-NT dedup. Start-NT candidates in fixpoint mode store
/// the converged LFP in `value` and `None` in `value_top`.
#[derive(Clone)]
pub struct Candidate {
    pub node: NodeId,
    pub value: Value,
    pub value_top: Option<Value>,
}
