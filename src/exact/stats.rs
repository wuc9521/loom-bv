//! Opt-in sub-NT dedup-potential measurement (gated by `DELIS_DEDUP_STATS=1`).
//!
//! For each (nt_idx, size) we count: pushed candidates, distinct values at
//! `aux=0`, and distinct `(value@0, value@top)` pairs. The gap between
//! "pushed" and "distinct@(0,top)" upper-bounds the candidate-count
//! reduction from the multi-sample sub-NT dedup; the gap between
//! "distinct@0" and "distinct@(0,top)" measures how many recursive
//! sub-terms single-sample dedup would have wrongly collapsed.
//!
//! Diagnostic only: drives no search decisions. All methods are no-ops
//! when the env var is unset.

use rustc_hash::{FxHashMap, FxHashSet};

use crate::enumerate::value::Value;
use crate::exact::types::{Grammar, Node, NodeId};
use crate::info;

#[derive(Default)]
struct DedupBucket {
    pushed: u64,
    at_zero: FxHashSet<Value>,
    at_pair: FxHashSet<(Value, Value)>,
}

#[derive(Default)]
struct State {
    enabled: bool,
    bits: usize,
    per_nt_size: FxHashMap<(usize, usize), DedupBucket>,
}

thread_local! {
    static STATE: std::cell::RefCell<State> = std::cell::RefCell::new(State::default());
}

/// ZST whose static methods control the thread-local dedup-stats state.
pub struct DedupStats;

impl DedupStats {
    pub fn enable_if_env(bits: usize) {
        if std::env::var("DELIS_DEDUP_STATS").as_deref() != Ok("1") {
            return;
        }
        STATE.with(|c| {
            let mut c = c.borrow_mut();
            c.enabled = true;
            c.bits = bits;
            c.per_nt_size.clear();
        });
    }

    pub fn snapshot_line(tag: &str) {
        STATE.with(|c| {
            let c = c.borrow();
            if !c.enabled {
                return;
            }
            let mut total_pushed: u64 = 0;
            let mut total_at_zero: u64 = 0;
            let mut total_at_pair: u64 = 0;
            let mut per_nt_pair: FxHashMap<usize, u64> = FxHashMap::default();
            for ((nt, _size), b) in c.per_nt_size.iter() {
                total_pushed += b.pushed;
                total_at_zero += b.at_zero.len() as u64;
                total_at_pair += b.at_pair.len() as u64;
                *per_nt_pair.entry(*nt).or_default() += b.at_pair.len() as u64;
            }
            let collapse_pair = if total_at_pair > 0 {
                total_pushed as f64 / total_at_pair as f64
            } else {
                0.0
            };
            let mut nts: Vec<usize> = per_nt_pair.keys().copied().collect();
            nts.sort();
            let per_nt: Vec<(usize, u64)> = nts.iter().map(|n| (*n, per_nt_pair[n])).collect();
            info!(
                "{}: pushed={} distinct@0={} distinct@(0,top)={} collapse@(0,top)={:.1}x  per-nt-distinct={:?}",
                tag, total_pushed, total_at_zero, total_at_pair, collapse_pair, per_nt
            );
        });
    }

    pub fn dump_and_disable(tag: &str) {
        STATE.with(|c| {
            let mut c = c.borrow_mut();
            if !c.enabled {
                return;
            }
            let mut keys: Vec<(usize, usize)> = c.per_nt_size.keys().copied().collect();
            keys.sort();
            info!("{}: sub-NT dedup potential (pushed / distinct@0 / distinct@(0,top)):", tag);
            let mut total_pushed: u64 = 0;
            let mut total_at_zero: u64 = 0;
            let mut total_at_pair: u64 = 0;
            for (nt, size) in &keys {
                let b = &c.per_nt_size[&(*nt, *size)];
                total_pushed += b.pushed;
                total_at_zero += b.at_zero.len() as u64;
                total_at_pair += b.at_pair.len() as u64;
                info!(
                    "  nt[{}] size={}: pushed={} distinct@0={} distinct@(0,top)={}",
                    nt,
                    size,
                    b.pushed,
                    b.at_zero.len(),
                    b.at_pair.len()
                );
            }
            let collapse_0 = if total_at_zero > 0 {
                total_pushed as f64 / total_at_zero as f64
            } else {
                0.0
            };
            let collapse_pair = if total_at_pair > 0 {
                total_pushed as f64 / total_at_pair as f64
            } else {
                0.0
            };
            info!(
                "{}: TOTAL pushed={} distinct@0={} distinct@(0,top)={}  collapse@0={:.1}x collapse@(0,top)={:.1}x",
                tag, total_pushed, total_at_zero, total_at_pair, collapse_0, collapse_pair
            );
            c.enabled = false;
            c.per_nt_size.clear();
        });
    }

    /// Record a sub-NT candidate push. Called at the push site in fixpoint
    /// mode. No-op when the env var is unset. Computes `value@top` from
    /// scratch via a Node DAG walk — fine because this is diagnostic.
    pub fn record_push(
        nt_idx: usize,
        size: usize,
        node: NodeId,
        value_at_zero: &Value,
        grammar: &Grammar<'_>,
        nodes: &[Node],
        closure_name: &str,
    ) {
        let (enabled, bits) = STATE.with(|c| {
            let c = c.borrow();
            (c.enabled, c.bits)
        });
        if !enabled {
            return;
        }
        let aux_top = Value::zero(bits).bitnot();
        let Some(value_at_top) = grammar.eval_node_at(node, nodes, &aux_top, closure_name) else {
            return;
        };
        STATE.with(|c| {
            let mut c = c.borrow_mut();
            let entry = c.per_nt_size.entry((nt_idx, size)).or_default();
            entry.pushed += 1;
            entry.at_zero.insert(value_at_zero.clone());
            entry.at_pair.insert((value_at_zero.clone(), value_at_top));
        });
    }
}
