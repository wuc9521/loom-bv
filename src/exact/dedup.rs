use std::collections::hash_map::Entry;

use rustc_hash::FxHashMap;

use crate::enumerate::value::BitVec;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct ProjectionKey(Vec<u64>);

pub enum SeenMode {
    /// Dedup by flat-concat of all K example values. K=1 degenerates to exact
    /// single-value dedup.
    MultiExact {
        maps: Vec<FxHashMap<Vec<BitVec>, usize>>,
    },
    /// Dedup by flat-concat of K projected values onto per-NT relevant bits.
    MultiProjected {
        relevant_bits: Vec<Vec<usize>>,
        num_examples: usize,
        maps: Vec<FxHashMap<ProjectionKey, usize>>,
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

    pub fn contains_or_insert_multi(
        &mut self,
        nt: usize,
        values: &[BitVec],
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
        }
    }
}

fn project_multi(values: &[BitVec], relevant_bits: &[usize], _num_examples: usize) -> ProjectionKey {
    let mut words = Vec::new();
    for value in values {
        words.extend(value.project_bits(relevant_bits));
    }
    ProjectionKey(words)
}
