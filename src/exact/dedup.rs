use std::collections::hash_map::Entry;

use rustc_hash::FxHashMap;

use crate::enumerate::value::BitVec;

/// Initial capacity for each per-NT dedup map. Skips the first several
/// power-of-two rehashes that showed up as `reserve_rehash` in profiles.
/// Heuristic, not a hard bound — maps still grow past this as needed.
const SEEN_MAP_INIT_CAP: usize = 256;

/// When true, dedup keys on a 128-bit fingerprint of the value words instead
/// of the exact word vector. This drops the per-candidate key allocation and
/// the full-key `memcmp` on every hash hit (both were top leaves in profiles).
///
/// SOUNDNESS: two candidates with *different* value vectors collide only if
/// their 128-bit fingerprints are equal. By the birthday bound, reaching even
/// a 1e-9 collision probability requires ~2.6e19 distinct candidates; these
/// searches enumerate far fewer (<1e9), so a fingerprint match implies
/// observational equivalence in all realistic runs. Set to `false` to restore
/// exact keys (allocates a `Vec<u64>` per probe and compares full words).
const USE_FINGERPRINT_DEDUP: bool = true;

pub enum SeenMode {
    /// Ablation: retain distinct candidates even when their values agree.
    Disabled,
    /// Dedup by flat-concat of all K example values. K=1 degenerates to exact
    /// single-value dedup.
    ExactValues {
        maps: Vec<FxHashMap<u128, usize>>,
        /// Reused across probes so building the key never reallocates.
        scratch: Vec<u64>,
    },
    /// Dedup by flat-concat of K projected values onto per-NT relevant bits.
    ProjectedValues {
        relevant_bits: Vec<Vec<usize>>,
        maps: Vec<FxHashMap<u128, usize>>,
        scratch: Vec<u64>,
    },
}

fn new_maps(nt_count: usize) -> Vec<FxHashMap<u128, usize>> {
    (0..nt_count)
        .map(|_| FxHashMap::with_capacity_and_hasher(SEEN_MAP_INIT_CAP, Default::default()))
        .collect()
}

impl SeenMode {
    pub fn exact_values(nt_count: usize) -> Self {
        SeenMode::ExactValues {
            maps: new_maps(nt_count),
            scratch: Vec::new(),
        }
    }

    pub fn projected_values(relevant_bits: Vec<Vec<usize>>) -> Self {
        let nt_count = relevant_bits.len();
        SeenMode::ProjectedValues {
            maps: new_maps(nt_count),
            relevant_bits,
            scratch: Vec::new(),
        }
    }

    pub fn contains_or_insert_values(
        &mut self,
        nt: usize,
        values: &[BitVec],
        size: usize,
    ) -> bool {
        // Fill the reused scratch buffer with this candidate's key words, then
        // reduce to a fixed-width fingerprint. `maps` and `scratch` are disjoint
        // fields, so the mutable borrows don't conflict.
        let (map, key) = match self {
            SeenMode::Disabled => return false,
            SeenMode::ExactValues { maps, scratch } => {
                scratch.clear();
                for value in values {
                    value.u64_words_into(scratch);
                }
                (&mut maps[nt], key_of(scratch))
            }
            SeenMode::ProjectedValues {
                relevant_bits,
                maps,
                scratch,
            } => {
                scratch.clear();
                let bits = &relevant_bits[nt];
                for value in values {
                    value.project_bits_into(bits, scratch);
                }
                (&mut maps[nt], key_of(scratch))
            }
        };
        match map.entry(key) {
            Entry::Occupied(_) => true,
            Entry::Vacant(e) => {
                e.insert(size);
                false
            }
        }
    }
}

/// Reduce the concatenated key words to the 128-bit map key. With
/// `USE_FINGERPRINT_DEDUP` off, packs the raw words instead (exact, but only
/// correct while keys fit in 128 bits — used for debugging/comparison).
#[inline]
fn key_of(words: &[u64]) -> u128 {
    if USE_FINGERPRINT_DEDUP {
        fingerprint128(words)
    } else {
        // Exact fallback: only valid when the key is <=128 bits. Intended for
        // A/B checking against the fingerprint path, not production use.
        let lo = words.first().copied().unwrap_or(0) as u128;
        let hi = words.get(1).copied().unwrap_or(0) as u128;
        (hi << 64) | lo
    }
}

/// MurmurHash3 64-bit finalizer: excellent avalanche in ~5 ops.
#[inline(always)]
fn fmix64(mut z: u64) -> u64 {
    z ^= z >> 33;
    z = z.wrapping_mul(0xff51afd7ed558ccd);
    z ^= z >> 33;
    z = z.wrapping_mul(0xc4ceb9fe1a85ec53);
    z ^= z >> 33;
    z
}

/// 128-bit fingerprint of the value words via two independently-seeded,
/// fmix64-avalanched lanes. A collision needs both 64-bit lanes to collide at
/// once; see the `USE_FINGERPRINT_DEDUP` note for the soundness argument.
#[inline]
fn fingerprint128(words: &[u64]) -> u128 {
    let len = words.len() as u64;
    let mut h1 = 0x9E3779B97F4A7C15u64 ^ len.wrapping_mul(0x9E3779B97F4A7C15);
    let mut h2 = 0xC2B2AE3D27D4EB4Fu64 ^ len.wrapping_mul(0xC2B2AE3D27D4EB4F);
    for &w in words {
        h1 = fmix64(h1 ^ w);
        h2 = fmix64(h2.rotate_left(31).wrapping_add(w).wrapping_add(1));
    }
    ((h1 as u128) << 64) | (h2 as u128)
}
