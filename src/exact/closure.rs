//! Closure bindings for the fwd-decls / LFP-mode search.
//!
//! In fwd-decls mode the search treats each candidate tuple as the
//! body of one or more closure synth-funs. Each evaluation needs to
//! substitute concrete `BitVec`s by name. `Bindings` holds the current
//! aux state for the Kleene loop, plus a saturated `top` state for the
//! sub-NT pair-dedup sample.
//!
//! Direct (non-fwd-decls) mode is represented as `Option::None` at the
//! call site; this struct never holds a "no closure" sentinel.

use crate::enumerate::value::BitVec;

pub struct Bindings {
    pub aux_names: Vec<String>,
    pub aux_zero: Vec<BitVec>,
    pub aux_top: Vec<BitVec>,
}

impl Bindings {
    /// Single-aux constructor (legacy LFP path).
    pub fn single(name: impl Into<String>, bits: usize) -> Self {
        Self {
            aux_names: vec![name.into()],
            aux_zero: vec![BitVec::zero(bits)],
            aux_top: vec![BitVec::zero(bits).bitnot()],
        }
    }

    /// N-aux constructor: each entry is `(name, bits)`. Initial states are
    /// `0` for the Kleene start sample and `top = ~0` for the dedup pair.
    pub fn new(slots: impl IntoIterator<Item = (String, usize)>) -> Self {
        let mut aux_names = Vec::new();
        let mut aux_zero = Vec::new();
        let mut aux_top = Vec::new();
        for (name, bits) in slots {
            aux_names.push(name);
            aux_zero.push(BitVec::zero(bits));
            aux_top.push(BitVec::zero(bits).bitnot());
        }
        Self { aux_names, aux_zero, aux_top }
    }

    pub fn len(&self) -> usize {
        self.aux_names.len()
    }

    pub fn name(&self, idx: usize) -> &str {
        &self.aux_names[idx]
    }

    pub fn zero(&self, idx: usize) -> &BitVec {
        &self.aux_zero[idx]
    }

    pub fn top(&self, idx: usize) -> &BitVec {
        &self.aux_top[idx]
    }

    /// Build the lookup slice for the `aux=0` Kleene-start sample.
    pub fn bindings_zero(&self) -> Vec<(&str, &BitVec)> {
        self.aux_names
            .iter()
            .zip(self.aux_zero.iter())
            .map(|(n, v)| (n.as_str(), v))
            .collect()
    }

    /// Build the lookup slice for the `aux=top` dedup-pair sample.
    pub fn bindings_top(&self) -> Vec<(&str, &BitVec)> {
        self.aux_names
            .iter()
            .zip(self.aux_top.iter())
            .map(|(n, v)| (n.as_str(), v))
            .collect()
    }
}
