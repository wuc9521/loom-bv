//! LFP synthesis backend. See `spec::LfpSpec` for the patterns this module
//! recognizes; everything below the spec is variant-agnostic.
//!
//! Single search strategy: enumerate operator terms smallest-first, compute
//! the LFP per candidate, dedup by start-NT-projected LFP, return the first
//! candidate whose LFP satisfies the label constraints. This is the same
//! shape the old multisynth had; the previous split into bottom_up/top_down
//! was an ad-hoc optimization that dropped projection dedup on the
//! non-tabulating path and caused the Reg-benchmark perf regression.

use crate::info;
use crate::parse::{self, deffun};

mod eval;
mod spec;
mod top_down;

pub use spec::LfpSpec;

impl<'a> LfpSpec<'a> {
    /// Drive the LFP-closure search for this spec: compute backward-relevance
    /// over the closure bits, then enumerate operator terms via the top-down
    /// engine and return the first one whose LFP satisfies the labels.
    pub fn search(&self, env: &deffun::Environ) -> parse::Result<Option<String>> {
        let (nt_bits, closure_bits) = self.closure_relevant_bits()?;
        info!(
            "{}: closure bits = {}/{}; start output bits = {}/{}",
            self.variant_tag(),
            closure_bits.len(),
            self.bits(),
            nt_bits.first().map(Vec::len).unwrap_or(0),
            self.bits()
        );
        let start_relevant = nt_bits.into_iter().next().unwrap_or_default();
        top_down::search(self, env, &start_relevant)
    }
}
