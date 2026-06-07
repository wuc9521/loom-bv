//! Evaluation primitives for the exact-nullary search.
//!
//! - `eval_defined_with_closure`: the single entry point for evaluating a
//!   define-fun in the search, with optional closure-arg binding (LFP path)
//!   and a thread-local cross-call memo keyed on `(fid, args, aux)`.
//! - `EvalCache`: the memo cache itself, controlled via static methods
//!   (`EvalCache::enable` / `EvalCache::dump_and_disable`).
//! - `Grammar::materialize_node` / `Grammar::eval_node_at`:
//!   walks over the Node DAG. Used by the LFP-mode Kleene loop and by
//!   the final solution materialization.

use rustc_hash::FxHashMap;

use crate::enumerate::{expr::OwnedExpr, value::BitVec};
use crate::exact::relevance;
use crate::exact::types::{Grammar, ExactRule, Node, NodeId};
use crate::{debg, info};
use crate::parse::deffun;

// ---------------------------------------------------------------------------
//  EvalCache — thread-local memo for `eval_defined_with_closure`
// ---------------------------------------------------------------------------
//
// `Environ::eval_defined` takes `args.len() + closure_args.len()` values:
// the real args first, then the current value of each closure synth-fun the
// body references. `eval_defined_with_closure` is the search-side wrapper
// that owns three concerns at once:
//
//   1. *Closure-arg assembly*: build the appended-closure args list when
//      the define-fun reads any closure synth-funs. `closure = None`
//      (direct mode with no closures anywhere) is a fast pass-through.
//   2. *Cross-call memoization*: in the fixpoint search the same
//      `(fid, args)` tuple recurs many times across candidates and Kleene
//      iterations. The cache catches them; enabled by `EvalCache::enable`
//      from the LFP frontend, disabled in direct mode.
//   3. *Dispatch* to `Environ::eval_defined`.

/// Cache state for `eval_defined_with_closure`. The key is a `u64` hash of
/// `(fid, nargs, args..., closure args...)` computed inline at the call
/// site. Storing the structural key (`Box<[BitVec]>`) cost one heap
/// allocation per probe — significant on a 2M+ call hot path even at 92%
/// hit rate. Collision risk for a u64 key with ~200k entries is on the
/// order of 10⁻⁹ (birthday paradox), well below the threshold where a
/// real synthesizer could see a wrong-answer due to it.
#[derive(Default)]
struct EvalCacheState {
    map: FxHashMap<u64, BitVec>,
    hits: u64,
    misses: u64,
    enabled: bool,
}

thread_local! {
    static STATE: std::cell::RefCell<EvalCacheState> =
        std::cell::RefCell::new(EvalCacheState::default());
}

/// ZST whose static methods control the thread-local `EVAL_CACHE`.
pub struct EvalCache;

impl EvalCache {
    pub fn enable() {
        STATE.with(|c| {
            let mut c = c.borrow_mut();
            c.map.clear();
            c.hits = 0;
            c.misses = 0;
            c.enabled = true;
        });
    }

    pub fn dump_and_disable(tag: &str) {
        STATE.with(|c| {
            let mut c = c.borrow_mut();
            let total = c.hits + c.misses;
            let rate = if total > 0 {
                c.hits as f64 / total as f64 * 100.0
            } else {
                0.0
            };
            info!(
                "{}: eval_defined memo: {} calls, {} hits ({:.1}%), {} cached entries",
                tag,
                total,
                c.hits,
                rate,
                c.map.len()
            );
            c.map.clear();
            c.hits = 0;
            c.misses = 0;
            c.enabled = false;
        });
    }
}

#[inline]
pub fn eval_defined_with_closure(
    fid: usize,
    args: &[BitVec],
    closure: Option<(&str, &BitVec)>,
) -> Result<BitVec, ()> {
    let f = deffun::ENV.deffun(fid);

    STATE.with(|c| {
        let mut c = c.borrow_mut();
        if !c.enabled {
            return f.eval(&deffun::ENV, args, closure).map_err(|_| ());
        }
        let key = f.hash_call(args, closure);
        if let Some(v) = c.map.get(&key).cloned() {
            c.hits += 1;
            return Ok(v);
        }
        c.misses += 1;
        let v = f.eval(&deffun::ENV, args, closure).map_err(|_| ())?;
        c.map.insert(key, v.clone());
        Ok(v)
    })
}

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
            ExactRule::Op { fid, child_nts: _ } => {
                Some(OwnedExpr::Func(
                    *fid,
                    node.children
                        .iter()
                        .map(|child| self.materialize_node(*child, nodes))
                        .collect::<Option<Vec<_>>>()?,
                ))
            }
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

    /// Evaluate `node_id`'s value at the given `aux` by walking the Node DAG
    /// directly. Replaces the older `materialize_node → eval_with_closure`
    /// path, avoiding the per-root `Box` allocation chain. Cross-root
    /// sharing still flows through `EVAL_CACHE` keyed on `(fid, args, aux)`.
    pub fn eval_node_at(
        &self,
        node_id: NodeId,
        nodes: &[Node],
        aux: &BitVec,
        closure_name: &str,
    ) -> Option<BitVec> {
        let node = &nodes[node_id];
        match &self.nts[node.nt_idx].1[node.rule_idx] {
            ExactRule::Alias(_) => self.eval_node_at(node.children[0], nodes, aux, closure_name),
            ExactRule::Leaf(expr) => expr.eval_with_closure(&deffun::ENV, aux, closure_name).ok(),
            ExactRule::Op { fid, .. } => {
                let mut args = Vec::with_capacity(node.children.len());
                for child in &node.children {
                    args.push(self.eval_node_at(*child, nodes, aux, closure_name)?);
                }
                eval_defined_with_closure(*fid, &args, Some((closure_name, aux))).ok()
            }
            ExactRule::GenericTemplate { .. } => {
                // Templates don't support closure binding in the DAG walk;
                // LFP-mode benchmarks don't use them today. Fallback
                // materializes this subtree and uses the OwnedExpr path so
                // we stay correct.
                let expr = self.materialize_node(node_id, nodes)?;
                expr.eval_with_closure(&deffun::ENV, aux, closure_name).ok()
            }
        }
    }
}
