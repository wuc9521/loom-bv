//! Bit-set / bit-dependency primitives used by the relevance analyses.
//! These are internal datastructures only — they live here so that
//! `relevance::mod` (which drives the lazy worklist) and `relevance::deps`
//! (which computes per-op bit dependencies) can both reuse them without
//! either depending on the other.

#[derive(Clone, Copy)]
pub struct WorkItem {
    pub nt_idx: usize,
    pub rule_idx: usize,
}

impl WorkItem {
    pub fn new(nt_idx: usize, rule_idx: usize) -> Self {
        Self { nt_idx, rule_idx }
    }
}

#[derive(Clone, Default)]
pub struct BitSet {
    pub words: Vec<u64>,
}

impl BitSet {
    pub fn new(bits: usize) -> Self {
        Self {
            words: vec![0; bits.div_ceil(64)],
        }
    }

    pub fn full(bits: usize) -> Self {
        let mut set = Self::new(bits);
        let full_words = bits / 64;
        for word in &mut set.words[..full_words] {
            *word = u64::MAX;
        }
        let rem = bits % 64;
        if rem != 0 {
            set.words[full_words] = (1u64 << rem) - 1;
        }
        set
    }

    pub fn insert(&mut self, bit: usize) {
        let word = bit / 64;
        if word < self.words.len() {
            self.words[word] |= 1u64 << (bit % 64);
        }
    }

    pub fn union_inplace(&mut self, other: &Self) {
        for (lhs, rhs) in self.words.iter_mut().zip(other.words.iter()) {
            *lhs |= *rhs;
        }
    }

    /// Union `other` into `self`, returning a `BitSet` of just the bits
    /// that were newly added (i.e. set in `other` but not previously in
    /// `self`).
    pub fn union_delta(&mut self, other: &Self) -> Self {
        let mut delta = Self {
            words: vec![0; self.words.len()],
        };
        for ((lhs, rhs), delta_word) in self
            .words
            .iter_mut()
            .zip(other.words.iter())
            .zip(delta.words.iter_mut())
        {
            let new_bits = *rhs & !*lhs;
            *lhs |= *rhs;
            *delta_word = new_bits;
        }
        delta
    }

    pub fn is_empty(&self) -> bool {
        self.words.iter().all(|word| *word == 0)
    }

    pub fn take(&mut self) -> Self {
        std::mem::replace(
            self,
            Self {
                words: vec![0; self.words.len()],
            },
        )
    }

    pub fn iter_ones(&self) -> impl Iterator<Item = usize> + '_ {
        self.words.iter().enumerate().flat_map(|(word_idx, word)| {
            let mut word = *word;
            std::iter::from_fn(move || {
                if word == 0 {
                    return None;
                }
                let bit = word.trailing_zeros() as usize;
                word &= word - 1;
                Some(word_idx * 64 + bit)
            })
        })
    }
}

/// Per-argument bit-dependency record: for each input slot `i`, which bits
/// of that slot some output bit depends on.
#[derive(Clone)]
pub struct BitDep {
    pub per_arg: Vec<BitSet>,
}

impl BitDep {
    pub fn empty(arg_bits: &[usize]) -> Self {
        Self {
            per_arg: arg_bits.iter().map(|bits| BitSet::new(*bits)).collect(),
        }
    }

    pub fn full(arg_bits: &[usize]) -> Self {
        Self {
            per_arg: arg_bits.iter().map(|bits| BitSet::full(*bits)).collect(),
        }
    }

    pub fn single_slot(arg_bits: &[usize], arg_idx: usize, bit: usize) -> Self {
        let mut dep = Self::empty(arg_bits);
        dep.per_arg[arg_idx].insert(bit);
        dep
    }

    pub fn union_inplace(&mut self, other: &Self) {
        for (lhs, rhs) in self.per_arg.iter_mut().zip(other.per_arg.iter()) {
            lhs.union_inplace(rhs);
        }
    }
}
