//! Sub-NT dedup machinery for the exact-nullary search.
//!
//! Three modes:
//! - `Exact`: dedup by raw `Value`. Direct (non-fixpoint) mode default.
//! - `Projected`: dedup by `Value` projected onto a per-NT relevant-bit
//!   index. Direct mode when backward-relevance is computed up-front.
//! - `Pair`: dedup sub-NT candidates by `(value@aux=0, value@aux=top)`
//!   pairs, while the start-NT pool dedups by single LFP value. Fixpoint
//!   mode; recovers sub-NT sharing that single-sample `aux=0` would
//!   incorrectly collapse for recursive sub-terms.

use std::collections::hash_map::Entry;

use rustc_hash::FxHashMap;

use crate::enumerate::value::Value;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct ProjectionKey(Vec<u64>);

pub enum SeenMode {
    Exact(Vec<FxHashMap<Value, usize>>),
    Projected {
        relevant_bits: Vec<Vec<usize>>,
        maps: Vec<FxHashMap<ProjectionKey, usize>>,
    },
    /// Fixpoint-mode dedup: sub-NTs use `(value@0, value@top)` pairs;
    /// the start-NT pool uses a single `Value` (the converged LFP).
    Pair {
        sub_maps: Vec<FxHashMap<(Value, Value), usize>>,
        start_lfp: FxHashMap<Value, usize>,
        start_nt: usize,
    },
}

impl SeenMode {
    pub fn exact(nt_count: usize) -> Self {
        SeenMode::Exact(vec![FxHashMap::default(); nt_count])
    }

    pub fn projected(relevant_bits: Vec<Vec<usize>>) -> Self {
        let nt_count = relevant_bits.len();
        SeenMode::Projected {
            relevant_bits,
            maps: (0..nt_count).map(|_| FxHashMap::default()).collect(),
        }
    }

    pub fn pair(nt_count: usize, start_nt: usize) -> Self {
        SeenMode::Pair {
            sub_maps: (0..nt_count).map(|_| FxHashMap::default()).collect(),
            start_lfp: FxHashMap::default(),
            start_nt,
        }
    }

    /// Single-value dedup. Used by direct mode for all NTs, and by Pair
    /// mode at the start NT only (where `value` is the converged LFP).
    pub fn contains_or_insert(&mut self, nt: usize, value: &Value, size: usize) -> bool {
        match self {
            SeenMode::Exact(maps) => match maps[nt].entry(value.clone()) {
                Entry::Occupied(_) => true,
                Entry::Vacant(e) => {
                    e.insert(size);
                    false
                }
            },
            SeenMode::Projected { relevant_bits, maps } => {
                let key = value.project(&relevant_bits[nt]);
                match maps[nt].entry(key) {
                    Entry::Occupied(_) => true,
                    Entry::Vacant(e) => {
                        e.insert(size);
                        false
                    }
                }
            }
            SeenMode::Pair { start_lfp, start_nt, .. } => {
                debug_assert_eq!(nt, *start_nt, "Pair mode: contains_or_insert is start-NT only");
                match start_lfp.entry(value.clone()) {
                    Entry::Occupied(_) => true,
                    Entry::Vacant(e) => {
                        e.insert(size);
                        false
                    }
                }
            }
        }
    }

    /// Two-sample pair dedup. Only valid in Pair mode; returns `false`
    /// (i.e. "not seen, please push without dedup") in other modes so the
    /// caller can use a uniform code path.
    pub fn contains_or_insert_pair(
        &mut self,
        nt: usize,
        value_zero: &Value,
        value_top: &Value,
        size: usize,
    ) -> bool {
        let SeenMode::Pair { sub_maps, .. } = self else { return false; };
        match sub_maps[nt].entry((value_zero.clone(), value_top.clone())) {
            Entry::Occupied(_) => true,
            Entry::Vacant(e) => {
                e.insert(size);
                false
            }
        }
    }
}

impl Value {
    pub(crate) fn project(&self, bits: &[usize]) -> ProjectionKey {
        ProjectionKey(self.project_bits(bits))
    }
}
