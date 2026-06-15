//! Trait abstracting "what the searcher checks at each Start-NT candidate".
//!
//! `Searcher` enumerates candidates bottom-up over a grammar. At each
//! Start-NT candidate it asks the verifier: does this candidate satisfy
//! the search target?
//!
//! Two implementations:
//!
//! - [`Constraint`]: the existing PBE / structural shape — checks the
//!   per-example output values against masked targets and evaluates
//!   structural exprs against `set_candidate(entry_idx, …)`.
//!
//! - `FwdDeclsProblem`: SyGuS 2.1 `fwd-decls` mode — before the bit
//!   asserts can be evaluated, the auxiliary forward-declared synth-funs
//!   must be brought to their LFP. The verifier iterates
//!   `c := baseline ∨ propagation(entry, c)` until stable, sets each
//!   auxiliary via `set_candidate(idx, …)`, then evaluates the bit
//!   asserts against the entry-point synth-fun.
//!
//! Shared between the two: the enumeration loop, dedup, COI pruning,
//! grammar materialisation, eval cache, candidate intern map. The
//! *only* place the two differ is the per-candidate verify step.

use crate::enumerate::expr::OwnedExpr;
use crate::enumerate::value::BitVec;
use crate::exact::bitspec::{Constraint, Example};
use crate::exact::types::Grammar;

pub trait Verifier {
    /// Number of PBE examples. For structural / fwd-decls specs: 0.
    fn num_examples(&self) -> usize;

    /// Bit-width of the entry-point synth-fun's output sort.
    fn output_bits(&self) -> usize;

    /// `i`-th example's arg list. Only called when `i < num_examples()`.
    fn example_args(&self, i: usize) -> &[BitVec];

    /// Compute per-NT relevant bits, if possible (for COI pruning).
    /// Structural-only specs (fwd-decls) typically return `None`.
    fn compute_relevant_bits(&self, grammar: &Grammar<'_>) -> Option<Vec<Vec<usize>>>;

    /// PBE-compose target: returns `Some(examples)` if the spec admits
    /// bit-extract decomposition (the `try_compose` path). fwd-decls /
    /// structural specs return `None`.
    fn pbe_examples(&self) -> Option<&[Example]>;

    /// Per-Start-NT-candidate verification. `values` is the candidate's
    /// per-example evaluation (empty for structural-only specs).
    /// `materialize` is a one-shot accessor for the candidate's
    /// `OwnedExpr` — verifiers that need the expression (structural,
    /// fwd-decls) call it; PBE verifiers never invoke it, so the
    /// Searcher pays no DAG-walk / clone cost on every candidate.
    /// Returns `true` iff the candidate satisfies the spec.
    fn verify(
        &self,
        values: &[BitVec],
        materialize: &mut dyn FnMut() -> Option<OwnedExpr>,
    ) -> bool;
}

impl Verifier for Constraint {
    fn num_examples(&self) -> usize {
        Constraint::num_examples(self)
    }
    fn output_bits(&self) -> usize {
        self.bits
    }
    fn example_args(&self, i: usize) -> &[BitVec] {
        &self.examples[i].args
    }
    fn compute_relevant_bits(&self, grammar: &Grammar<'_>) -> Option<Vec<Vec<usize>>> {
        Constraint::compute_relevant_bits(self, grammar)
    }
    fn pbe_examples(&self) -> Option<&[Example]> {
        if self.examples.is_empty() {
            None
        } else {
            Some(&self.examples)
        }
    }
    fn verify(
        &self,
        values: &[BitVec],
        _materialize: &mut dyn FnMut() -> Option<OwnedExpr>,
    ) -> bool {
        Constraint::matches(self, values)
    }
}
