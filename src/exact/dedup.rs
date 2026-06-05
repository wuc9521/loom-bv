use std::collections::hash_map::Entry;

use rustc_hash::FxHashMap;

use crate::enumerate::value::Value;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct ProjectionKey(Vec<u64>);

pub enum SeenMode {
    /// Dedup by flat-concat of all K example values. K=1 degenerates to exact
    /// single-value dedup.
    MultiExact {
        maps: Vec<FxHashMap<Vec<Value>, usize>>,
    },
    /// Dedup by flat-concat of K projected values onto per-NT relevant bits.
    MultiProjected {
        relevant_bits: Vec<Vec<usize>>,
        num_examples: usize,
        maps: Vec<FxHashMap<ProjectionKey, usize>>,
    },
    /// Fixpoint-mode dedup: sub-NTs use `(values@0, values@top)` pairs;
    /// the start-NT pool uses a single `Value` (the converged LFP).
    Pair {
        sub_maps: Vec<FxHashMap<(Value, Value), usize>>,
        start_lfp: FxHashMap<Value, usize>,
        start_nt: usize,
    },
}

impl SeenMode {
    pub fn multi_exact(nt_count: usize, _num_examples: usize) -> Self {
        SeenMode::MultiExact {
            maps: vec![FxHashMap::default(); nt_count],
        }
    }

    pub fn multi_projected(relevant_bits: Vec<Vec<usize>>, num_examples: usize) -> Self {
        let nt_count = relevant_bits.len();
        SeenMode::MultiProjected {
            relevant_bits,
            num_examples,
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

    pub fn contains_or_insert_multi(
        &mut self,
        nt: usize,
        values: &[Value],
        size: usize,
    ) -> bool {
        match self {
            SeenMode::MultiExact { maps } => {
                match maps[nt].entry(values.to_vec()) {
                    Entry::Occupied(_) => true,
                    Entry::Vacant(e) => {
                        e.insert(size);
                        false
                    }
                }
            }
            SeenMode::MultiProjected { relevant_bits, num_examples, maps } => {
                let key = project_multi(values, &relevant_bits[nt], *num_examples);
                match maps[nt].entry(key) {
                    Entry::Occupied(_) => true,
                    Entry::Vacant(e) => {
                        e.insert(size);
                        false
                    }
                }
            }
            SeenMode::Pair { .. } => {
                panic!("contains_or_insert_multi should not be called in Pair mode");
            }
        }
    }

    /// Single-value dedup for start-NT in Pair (LFP) mode.
    pub fn contains_or_insert_lfp(&mut self, value: &Value, size: usize) -> bool {
        let SeenMode::Pair { start_lfp, .. } = self else {
            panic!("contains_or_insert_lfp called outside Pair mode");
        };
        match start_lfp.entry(value.clone()) {
            Entry::Occupied(_) => true,
            Entry::Vacant(e) => {
                e.insert(size);
                false
            }
        }
    }

    /// Two-sample pair dedup for sub-NTs in LFP mode.
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

fn project_multi(values: &[Value], relevant_bits: &[usize], _num_examples: usize) -> ProjectionKey {
    let mut words = Vec::new();
    for value in values {
        words.extend(value.project_bits(relevant_bits));
    }
    ProjectionKey(words)
}
