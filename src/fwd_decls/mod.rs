//! SyGuS 2.1 `fwd-decls` mode.
//!
//! In this mode the input file has multiple `synth-fun`s. One (the
//! *entry point*) has a grammar — that's the candidate the search
//! enumerates over. The others are forward-declared and appear as
//! terminals in the entry-point's grammar; their values are determined
//! by fixpoint constraints of shape
//! `(= aux (bvor aux_baseline (aux_propagation entry)))`.
//!
//! The verifier ([`problem::FwdDeclsProblem`]) iterates each auxiliary
//! to its LFP for the current entry-point candidate (a few steps over a
//! finite Boolean lattice), then evaluates the remaining bit asserts.
//! The enumeration loop, dedup, etc. are shared with the exact path via
//! [`crate::exact::verifier::Verifier`].

pub mod problem;
pub mod verifier;

pub use problem::FwdDeclsProblem;
