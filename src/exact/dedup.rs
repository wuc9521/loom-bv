use std::collections::hash_map::Entry;

use rustc_hash::FxHashMap;

use crate::enumerate::value::BitVec;

pub enum SeenMode {
    /// Dedup by flat-concat of all K example values. K=1 degenerates to exact
    /// single-value dedup.
    ExactValues {
        maps: Vec<FxHashMap<Vec<u64>, usize>>,
    },
    /// Dedup by flat-concat of K projected values onto per-NT relevant bits.
    ProjectedValues {
        relevant_bits: Vec<Vec<usize>>,
        maps: Vec<FxHashMap<Vec<u64>, usize>>,
    },
}

impl SeenMode {
    pub fn exact_values(nt_count: usize) -> Self {
        SeenMode::ExactValues {
            maps: vec![FxHashMap::default(); nt_count],
        }
    }

    pub fn projected_values(relevant_bits: Vec<Vec<usize>>) -> Self {
        let nt_count = relevant_bits.len();
        SeenMode::ProjectedValues {
            relevant_bits,
            maps: (0..nt_count).map(|_| FxHashMap::default()).collect(),
        }
    }

    pub fn contains_or_insert_values(
        &mut self,
        nt: usize,
        values: &[BitVec],
        size: usize,
    ) -> bool {
        match self {
            SeenMode::ExactValues { maps } => insert_key(&mut maps[nt], exact_value_key(values), size),
            SeenMode::ProjectedValues {
                relevant_bits,
                maps,
            } => insert_key(&mut maps[nt], projected_value_key(values, &relevant_bits[nt]), size),
        }
    }
}

fn insert_key(map: &mut FxHashMap<Vec<u64>, usize>, key: Vec<u64>, size: usize) -> bool {
    match map.entry(key) {
        Entry::Occupied(_) => true,
        Entry::Vacant(e) => {
            e.insert(size);
            false
        }
    }
}

fn exact_value_key(values: &[BitVec]) -> Vec<u64> {
    let words_per_value = values.first().map(|v| v.bits().div_ceil(64)).unwrap_or(0);
    let mut words = Vec::with_capacity(values.len() * words_per_value);
    for value in values {
        value.u64_words_into(&mut words);
    }
    words
}

fn projected_value_key(values: &[BitVec], relevant_bits: &[usize]) -> Vec<u64> {
    let mut words = Vec::with_capacity(values.len() * relevant_bits.len().div_ceil(64));
    for value in values {
        value.project_bits_into(relevant_bits, &mut words);
    }
    words
}
