//! Exact (bit-precise) nullary synthesis: bottom-up enumeration over the
//! grammar with value-based dedup.
//!
//! Two modes, both running through [`search::Searcher`]:
//!
//! - **Direct** — each candidate is checked against the spec on reaching
//!   the start NT. Sub-NT pools are deduped on the candidate's single
//!   value (or its relevance projection).
//!
//! - **Fixpoint** (LFP) — used when the SyGuS input matches an
//!   [`lfp::LfpSpec`] (one or two synth-funs that encode a recursive
//!   equation). Sub-NT candidates carry a two-sample fingerprint
//!   `(value@aux=0, value@aux=top)` for sound dedup; each start-NT
//!   candidate is iterated to its LFP via Kleene with a per-iter
//!   negative-label early reject, and the converged LFP is matched
//!   against the spec.
//!
//! Cross-call evaluation is memoized via the thread-local
//! [`eval::EvalCache`]; sub-NT dedup health can be inspected via
//! [`stats::DedupStats`] (gated by `DELIS_DEDUP_STATS=1`).

pub mod bitspec;
pub mod closure;
pub mod dedup;
pub mod eval;
pub mod grammar;
pub mod lfp;
pub mod relevance;
pub mod search;
pub mod stats;
pub mod types;
pub mod util;

pub use bitspec::BitSpec;
pub use eval::{eval_defined_with_closure, EvalCache};
pub use stats::DedupStats;
pub use types::{ExactGrammar, ExactRule};

// Backward-compat free-function shims kept for the LFP frontend (lfp.rs)
// while we land the method-style API. These will be inlined once lfp.rs
// uses the new methods directly.
pub fn enable_eval_cache() {
    EvalCache::enable();
}
pub fn dump_and_disable_eval_cache(tag: &str) {
    EvalCache::dump_and_disable(tag);
}
pub fn enable_dedup_stats_if_env(bits: usize) {
    DedupStats::enable_if_env(bits);
}
pub fn dump_and_disable_dedup_stats(tag: &str) {
    DedupStats::dump_and_disable(tag);
}
