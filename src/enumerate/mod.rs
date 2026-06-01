use iter_fixed::{IntoIteratorFixed, IteratorFixed};
use std::array;
// use fnv::FnvHashMap as HashMap;
use std::collections::HashMap;

use derive_more::{DebugCustom, Deref, From};

use self::expr::Expr;

pub mod algo;
pub mod algo_multi;
pub mod config;
pub mod expr;
pub mod grammar;
pub mod macros;
pub mod op;
pub mod store;
pub mod utils;
pub mod value;

#[repr(C, align(32))]
#[derive(From, Deref, DebugCustom, Clone, Copy, PartialEq, Eq, Hash)]
#[debug(fmt = "{:x}", *_0)]
pub struct Bv<const N: usize>(pub [u64; N]);

impl<const N: usize> Bv<N> {
    pub fn into_iter_fixed(self) -> IteratorFixed<array::IntoIter<u64, N>, N> {
        self.0.into_iter_fixed()
    }
}

impl<const N: usize> std::ops::Not for Bv<N> {
    type Output = Bv<N>;

    fn not(self) -> Self::Output {
        op::bv::not(self)
    }
}
impl<const N: usize> std::ops::BitAnd for Bv<N> {
    type Output = Bv<N>;

    fn bitand(self, rhs: Self) -> Self::Output {
        op::bv::and(self, rhs)
    }
}
impl<const N: usize> std::ops::BitOr for Bv<N> {
    type Output = Bv<N>;

    fn bitor(self, rhs: Self) -> Self::Output {
        op::bv::or(self, rhs)
    }
}
impl<const N: usize> std::ops::BitXor for Bv<N> {
    type Output = Bv<N>;

    fn bitxor(self, rhs: Self) -> Self::Output {
        op::bv::xor(self, rhs)
    }
}
impl<const N: usize> std::ops::Sub for Bv<N> {
    type Output = Bv<N>;

    fn sub(self, rhs: Self) -> Self::Output {
        op::bv::sub(self, rhs)
    }
}

impl<const N: usize> Bv<N> {
    pub const ONES: Self = Bv([u64::MAX; N]);
    pub const ZEROS: Self = Bv([u64::MIN; N]);
    pub fn count(&self) -> u32 {
        self.0.iter().map(|x| x.count_ones()).sum()
    }
    pub fn count_zeros(&self) -> u32 {
        self.0.iter().map(|x| x.count_zeros()).sum()
    }

    pub fn imples(&self, other: &Self) -> bool {
        self.iter().zip(other.iter()).all(|(a, b)| !a & b == 0)
    }

    pub fn any_eq(&self, other: &Self) -> bool {
        self.iter().zip(other.iter()).any(|(a, b)| a == b)
    }

    /// Extract bits `[lo..=hi]` from each lane independently. Bits above 63
    /// don't exist within a single lane, so requesting them yields zeros.
    pub fn extract(self, hi: u64, lo: u64) -> Self {
        if lo >= 64 {
            return Self::ZEROS;
        }
        let width = hi.saturating_sub(lo).saturating_add(1).min(64);
        let mask = if width >= 64 { u64::MAX } else { (1u64 << width) - 1 };
        Bv(self.map(|lane| (lane >> lo) & mask))
    }

    /// Concatenate `self` (high bits) with `rhs` (low bits), where `rhs`
    /// occupies the bottom `rhs_bits`. Per-lane: `(self << rhs_bits) | rhs`.
    pub fn concat_low(self, rhs: Self, rhs_bits: usize) -> Self {
        if rhs_bits >= 64 {
            return rhs;
        }
        let shift = rhs_bits as u32;
        let mask = if rhs_bits == 0 { 0 } else { (1u64 << shift) - 1 };
        Bv(self
            .into_iter_fixed()
            .zip(rhs.into_iter_fixed())
            .map(|(l, r)| (l << shift) | (r & mask))
            .collect())
    }
}

#[cfg(test)]
mod tests {
    use std::simd::Simd;

    #[test]
    fn test_unchecked() {
        let a: Simd<_, 2> = [i64::MIN; 2].into();
        println!("{:?}", a + a);
    }
}

pub trait Algo<'a, const N: usize> {
    fn len(&self) -> usize;
    fn count(&self) -> usize;
    fn count2(&self) -> usize;
    fn size(&self) -> usize;
    fn map_size(&self) -> usize;
    fn expr_size(&self) -> usize;
    fn map(&self) -> &HashMap<Bv<N>, Option<&'a Expr<'a>>>;
}
