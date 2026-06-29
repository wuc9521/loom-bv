//! Evaluation primitives for the exact-nullary search.
//!
//! - `Grammar::materialize_node` / `Grammar::eval_node_at`:
//!   walks over the Node DAG. Used by the LFP-mode Kleene loop and by
//!   the final solution materialization.

use crate::enumerate::{expr::OwnedExpr, value::BitVec};
use crate::exact::relevance;
use crate::exact::types::{ExactRule, Grammar, Node, NodeId};
use crate::parse::deffun;
use crate::{debg, info};

// ---------------------------------------------------------------------------
//  Grammar — Node-DAG materialization and evaluation
// ---------------------------------------------------------------------------

impl<'a> Grammar<'a> {
    pub fn log_relevance_summary(
        &self,
        relevant_bits: &[Vec<usize>],
        num_examples: usize,
        spec_bits: usize,
    ) {
        let total_kept: usize = relevant_bits.iter().map(Vec::len).sum();
        let mut total_full: usize = 0;
        for (i, (_, rules)) in self.nts.iter().enumerate() {
            if i == self.start {
                total_full += spec_bits;
            } else {
                total_full += relevance::nt_output_bits(rules);
            }
        }
        info!(
            "relevance: {}/{} bits relevant ({:.1}%), {} examples",
            total_kept,
            total_full,
            total_kept as f64 / total_full as f64 * 100.0,
            num_examples
        );
        for (i, (bits, (_, rules))) in relevant_bits.iter().zip(self.nts.iter()).enumerate() {
            let nt_total = if i == self.start {
                spec_bits
            } else {
                relevance::nt_output_bits(rules)
            };
            debg!("  nt[{}]: {}/{} bits relevant", i, bits.len(), nt_total);
        }
    }

    /// Materialize the subtree rooted at `node_id` into a flat `OwnedExpr`.
    /// Used to print the final solution and (in fallback paths) to evaluate
    /// `GenericTemplate` nodes that don't support closure-aware DAG eval.
    pub fn materialize_node(&self, node_id: NodeId, nodes: &[Node]) -> Option<OwnedExpr> {
        let node = &nodes[node_id];
        match &self.nts[node.nt_idx].1[node.rule_idx] {
            ExactRule::Alias(_) => self.materialize_node(node.children[0], nodes),
            ExactRule::Leaf(expr) => Some(expr.clone()),
            ExactRule::Op { fid, .. } => Some(OwnedExpr::Func(
                *fid,
                node.children
                    .iter()
                    .map(|child| self.materialize_node(*child, nodes))
                    .collect::<Option<Vec<_>>>()?,
            )),
            ExactRule::GenericTemplate { template, .. } => {
                let child_exprs = node
                    .children
                    .iter()
                    .map(|child| self.materialize_node(*child, nodes))
                    .collect::<Option<Vec<_>>>()?;
                template.instantiate(&child_exprs).ok()
            }
        }
    }

    /// Evaluate `node_id`'s value at the given closure `bindings` by walking
    /// the Node DAG directly. Cross-root sharing flows through the
    /// thread-local memo on `Environ::eval_defined`.
    pub fn eval_node_at(
        &self,
        node_id: NodeId,
        nodes: &[Node],
        bindings: &[(&str, &BitVec)],
    ) -> Option<BitVec> {
        let node = &nodes[node_id];
        match &self.nts[node.nt_idx].1[node.rule_idx] {
            ExactRule::Alias(_) => self.eval_node_at(node.children[0], nodes, bindings),
            ExactRule::Leaf(expr) => expr.eval_with_bindings(&[], bindings).ok(),
            ExactRule::Op { fid, .. } => {
                let mut args = Vec::with_capacity(node.children.len());
                for child in &node.children {
                    args.push(self.eval_node_at(*child, nodes, bindings)?);
                }
                deffun::ENV.eval_defined(*fid, &args, bindings).ok()
            }
            ExactRule::GenericTemplate { .. } => {
                // Templates fall back through OwnedExpr::eval_with_bindings.
                let expr = self.materialize_node(node_id, nodes)?;
                expr.eval_with_bindings(&[], bindings).ok()
            }
        }
    }
}
