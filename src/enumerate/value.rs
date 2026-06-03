use std::fmt;
use std::sync::Arc;

use num_bigint::{BigInt, BigUint, Sign};
use num_traits::{One, Signed, ToPrimitive, Zero};

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Value {
    Small { bits: usize, raw: u64 },
    Big { bits: usize, raw: Arc<BigUint> },
}

impl Value {
    pub fn bits(&self) -> usize {
        match self {
            Value::Small { bits, .. } | Value::Big { bits, .. } => *bits,
        }
    }

    pub fn from_u64(raw: u64, bits: usize) -> Self {
        if bits <= 64 {
            let mask = mask_u64(bits);
            let raw = raw & mask;
            Value::Small {
                bits,
                raw,
            }
        } else {
            let raw = truncate_big(BigUint::from(raw), bits);
            Value::Big {
                bits,
                raw: Arc::new(raw),
            }
        }
    }

    pub fn from_biguint(raw: BigUint, bits: usize) -> Self {
        if bits <= 64 {
            let raw = (raw & BigUint::from(mask_u64(bits))).to_u64().unwrap_or(0);
            Value::Small {
                bits,
                raw,
            }
        } else {
            let raw = truncate_big(raw, bits);
            Value::Big {
                bits,
                raw: Arc::new(raw),
            }
        }
    }

    pub fn zero(bits: usize) -> Self {
        Self::from_u64(0, bits)
    }

    pub fn is_zero(&self) -> bool {
        match self {
            Value::Small { raw, .. } => *raw == 0,
            Value::Big { raw, .. } => raw.as_ref().is_zero(),
        }
    }

    /// Reinterpret this `Value` as a Bool in dryadsynth's negative-logic
    /// internal encoding (SMT-true ↔ all bits 0, SMT-false ↔ any bit 1).
    /// `(= a b)` is parsed as `Xor(a, b)` so the bit-zero result means
    /// "equal" = "SMT-true"; `and`/`or` invert to internal `Or`/`And` for
    /// the same reason. Use this whenever a `Value` should be read as a
    /// SyGuS Bool — it makes the convention visible at the use site and
    /// prevents accidental `!is_zero()` flips.
    pub fn as_bool(&self) -> BoolValue<'_> {
        BoolValue(self)
    }

    pub fn as_u64_lossy(&self) -> u64 {
        match self {
            Value::Small { raw, .. } => *raw,
            Value::Big { raw, .. } => raw.as_ref().to_u64().unwrap_or(0),
        }
    }

    pub fn to_biguint(&self) -> BigUint {
        match self {
            Value::Small { raw, .. } => BigUint::from(*raw),
            Value::Big { raw, .. } => raw.as_ref().clone(),
        }
    }

    pub fn bit(&self, bit: usize) -> bool {
        if bit >= self.bits() {
            return false;
        }
        match self {
            Value::Small { raw, .. } => ((*raw >> bit) & 1) == 1,
            // `BigUint::bit` is O(1) direct limb access. The previous
            // `iter_u64_digits().nth(limb)` was O(limb) — iterated digits
            // from the start every call. Showed up at ~3% self-time on
            // Reg/0024 from the BitCircuit interpreter's per-bit input reads.
            Value::Big { raw, .. } => raw.as_ref().bit(bit as u64),
        }
    }

    pub fn extract(&self, hi: u64, lo: u64) -> Self {
        let width = (hi - lo + 1) as usize;
        if width == 1 {
            return Self::from_u64(self.bit(lo as usize) as u64, 1);
        }
        match self {
            Value::Small { raw, .. } => Self::extract_small(*raw, width, lo),
            Value::Big { raw, .. } => Self::extract_big(raw.as_ref(), width, lo),
        }
    }

    pub fn concat(&self, rhs: &Self) -> Self {
        match (self, rhs) {
            (
                Value::Small {
                    bits: lhs_bits,
                    raw: lhs,
                },
                Value::Small {
                    bits: rhs_bits,
                    raw: rhs,
                },
            ) if lhs_bits + rhs_bits <= 64 => {
                Value::from_u64((lhs << rhs_bits) | rhs, lhs_bits + rhs_bits)
            }
            _ => Self::concat_big(self, rhs),
        }
    }

    pub fn project_bits(&self, bits: &[usize]) -> Vec<u64> {
        let mut words = Vec::with_capacity(bits.len().div_ceil(64));
        let mut current = 0u64;
        match self {
            Value::Small { raw, bits: width } => {
                for (idx, bit) in bits.iter().enumerate() {
                    if *bit < *width && (((*raw >> *bit) & 1) == 1) {
                        current |= 1u64 << (idx % 64);
                    }
                    if idx % 64 == 63 {
                        words.push(current);
                        current = 0;
                    }
                }
            }
            Value::Big { raw, bits: width } => {
                let digits = raw.as_ref().to_u64_digits();
                for (idx, bit) in bits.iter().enumerate() {
                    if *bit < *width {
                        let limb = *bit / 64;
                        let offset = *bit % 64;
                        if digits
                            .get(limb)
                            .map(|digit| ((digit >> offset) & 1) == 1)
                            .unwrap_or(false)
                        {
                            current |= 1u64 << (idx % 64);
                        }
                    }
                    if idx % 64 == 63 {
                        words.push(current);
                        current = 0;
                    }
                }
            }
        }
        if !bits.is_empty() && bits.len() % 64 != 0 {
            words.push(current);
        }
        words
    }

    pub fn to_smt_hex(&self) -> String {
        let bits = self.bits();
        let hex_len = bits.div_ceil(4).max(1);
        let v = match self {
            Value::Small { raw, .. } => format!("{:x}", raw),
            Value::Big { raw, .. } => format!("{:x}", raw.as_ref()),
        };
        let padded = if v.len() >= hex_len {
            v
        } else {
            format!("{:0>width$}", v, width = hex_len)
        };
        format!("#x{}", padded)
    }

    pub fn bitnot(self) -> Self {
        let bits = self.bits();
        if bits <= 64 {
            let raw = !self.as_u64_lossy() & mask_u64(bits);
            Self::from_u64(raw, bits)
        } else {
            let all_ones = (BigUint::one() << bits) - BigUint::one();
            Self::from_biguint(all_ones ^ self.to_biguint(), bits)
        }
    }

    pub fn bitand(self, rhs: Self) -> Self {
        let bits = self.bits();
        if bits <= 64 {
            Self::from_u64(self.as_u64_lossy() & rhs.as_u64_lossy(), bits)
        } else {
            Self::from_biguint(self.to_biguint() & rhs.to_biguint(), bits)
        }
    }

    pub fn bitor(self, rhs: Self) -> Self {
        let bits = self.bits();
        if bits <= 64 {
            Self::from_u64(self.as_u64_lossy() | rhs.as_u64_lossy(), bits)
        } else {
            Self::from_biguint(self.to_biguint() | rhs.to_biguint(), bits)
        }
    }

    pub fn bitxor(self, rhs: Self) -> Self {
        let bits = self.bits();
        if bits <= 64 {
            Self::from_u64(self.as_u64_lossy() ^ rhs.as_u64_lossy(), bits)
        } else {
            Self::from_biguint(self.to_biguint() ^ rhs.to_biguint(), bits)
        }
    }

    pub fn add(self, rhs: Self) -> Self {
        let bits = self.bits();
        if bits <= 64 {
            Self::from_u64(self.as_u64_lossy().wrapping_add(rhs.as_u64_lossy()), bits)
        } else {
            Self::from_biguint(self.to_biguint() + rhs.to_biguint(), bits)
        }
    }

    pub fn sub(self, rhs: Self) -> Self {
        let bits = self.bits();
        if bits <= 64 {
            Self::from_u64(self.as_u64_lossy().wrapping_sub(rhs.as_u64_lossy()), bits)
        } else {
            let modulo = BigUint::one() << bits;
            let a = self.to_biguint();
            let b = rhs.to_biguint();
            let r = if a >= b { a - b } else { modulo.clone() - (b - a) };
            Self::from_biguint(r, bits)
        }
    }

    pub fn mul(self, rhs: Self) -> Self {
        let bits = self.bits();
        if bits <= 64 {
            Self::from_u64(self.as_u64_lossy().wrapping_mul(rhs.as_u64_lossy()), bits)
        } else {
            Self::from_biguint(self.to_biguint() * rhs.to_biguint(), bits)
        }
    }

    pub fn neg(self) -> Self {
        Self::zero(self.bits()).sub(self)
    }

    pub fn shl(self, rhs: Self) -> Self {
        let bits = self.bits();
        let s = rhs.to_biguint().to_usize().unwrap_or(usize::MAX);
        if s >= bits {
            return Self::zero(bits);
        }
        if bits <= 64 {
            Self::from_u64(self.as_u64_lossy() << s, bits)
        } else {
            Self::from_biguint(self.to_biguint() << s, bits)
        }
    }

    pub fn lshr(self, rhs: Self) -> Self {
        let bits = self.bits();
        let s = rhs.to_biguint().to_usize().unwrap_or(usize::MAX);
        if s >= bits {
            return Self::zero(bits);
        }
        if bits <= 64 {
            Self::from_u64(self.as_u64_lossy() >> s, bits)
        } else {
            Self::from_biguint(self.to_biguint() >> s, bits)
        }
    }

    pub fn ashr(self, rhs: Self) -> Self {
        let bits = self.bits();
        let s = rhs.to_biguint().to_usize().unwrap_or(usize::MAX);
        if s >= bits {
            return if self.is_negative() {
                Self::from_biguint((BigUint::one() << bits) - BigUint::one(), bits)
            } else {
                Self::zero(bits)
            };
        }
        if bits <= 64 {
            let v = self.as_u64_lossy();
            let sign = 1u64 << (bits - 1);
            if v & sign == 0 {
                Self::from_u64(v >> s, bits)
            } else {
                let fill = if s == 0 { 0 } else { (!0u64) << (bits - s) };
                Self::from_u64((v >> s) | fill, bits)
            }
        } else {
            let signed = self.to_signed_bigint();
            let shifted = signed >> s;
            Self::from_signed_bigint(shifted, bits)
        }
    }

    pub fn udiv(self, rhs: Self) -> Option<Self> {
        if rhs.is_zero() {
            return None;
        }
        let bits = self.bits();
        if bits <= 64 {
            Some(Self::from_u64(self.as_u64_lossy() / rhs.as_u64_lossy(), bits))
        } else {
            Some(Self::from_biguint(self.to_biguint() / rhs.to_biguint(), bits))
        }
    }

    pub fn urem(self, rhs: Self) -> Option<Self> {
        if rhs.is_zero() {
            return None;
        }
        let bits = self.bits();
        if bits <= 64 {
            Some(Self::from_u64(self.as_u64_lossy() % rhs.as_u64_lossy(), bits))
        } else {
            Some(Self::from_biguint(self.to_biguint() % rhs.to_biguint(), bits))
        }
    }

    pub fn sdiv(self, rhs: Self) -> Option<Self> {
        if rhs.is_zero() {
            return None;
        }
        let bits = self.bits();
        let a = self.to_signed_bigint();
        let b = rhs.to_signed_bigint();
        Some(Self::from_signed_bigint(a / b, bits))
    }

    pub fn srem(self, rhs: Self) -> Option<Self> {
        if rhs.is_zero() {
            return None;
        }
        let bits = self.bits();
        let a = self.to_signed_bigint();
        let b = rhs.to_signed_bigint();
        Some(Self::from_signed_bigint(a % b, bits))
    }

    fn is_negative(&self) -> bool {
        let bits = self.bits();
        if bits == 0 {
            return false;
        }
        if bits <= 64 {
            (self.as_u64_lossy() >> (bits - 1)) & 1 == 1
        } else {
            let v = self.to_biguint();
            ((&v >> (bits - 1)) & BigUint::one()) == BigUint::one()
        }
    }

    fn to_signed_bigint(&self) -> BigInt {
        let bits = self.bits();
        let unsigned = self.to_biguint();
        if bits == 0 {
            return BigInt::zero();
        }
        let sign_bit = BigUint::one() << (bits - 1);
        if (&unsigned & &sign_bit).is_zero() {
            BigInt::from_biguint(Sign::Plus, unsigned)
        } else {
            BigInt::from_biguint(Sign::Plus, unsigned) - BigInt::from_biguint(Sign::Plus, BigUint::one() << bits)
        }
    }

    fn from_signed_bigint(v: BigInt, bits: usize) -> Self {
        let modulo = BigInt::from_biguint(Sign::Plus, BigUint::one() << bits);
        let mut rem = v % &modulo;
        if rem.is_negative() {
            rem += &modulo;
        }
        let as_unsigned = rem.to_biguint().unwrap_or_else(BigUint::zero);
        Self::from_biguint(as_unsigned, bits)
    }

    #[inline]
    fn extract_small(raw: u64, width: usize, lo: u64) -> Self {
        Self::from_u64(raw >> lo, width)
    }

    fn extract_big(raw: &BigUint, width: usize, lo: u64) -> Self {
        let shifted = raw >> (lo as usize);
        let mask = (BigUint::one() << width) - BigUint::one();
        Self::from_biguint(shifted & mask, width)
    }

    fn concat_big(lhs: &Self, rhs: &Self) -> Self {
        let rhs_bits = rhs.bits();
        let total_bits = lhs.bits() + rhs_bits;
        // Build the result in place: `<<=` and `|=` mutate the local
        // BigUint instead of allocating intermediates for `<<` and `|`.
        // The result occupies exactly `total_bits` bits by construction
        // (no high bits beyond), so the mask-and-truncate that
        // `from_biguint` would do on its `bits > 64` branch is redundant —
        // build the Big variant directly.
        let mut raw = lhs.to_biguint();
        raw <<= rhs_bits;
        match rhs {
            Value::Small { raw: rhs_raw, .. } => {
                if *rhs_raw != 0 {
                    raw |= BigUint::from(*rhs_raw);
                }
            }
            Value::Big { raw: rhs_raw, .. } => {
                raw |= rhs_raw.as_ref();
            }
        }
        if total_bits <= 64 {
            Value::Small {
                bits: total_bits,
                raw: raw.to_u64().unwrap_or(0) & mask_u64(total_bits),
            }
        } else {
            Value::Big {
                bits: total_bits,
                raw: Arc::new(raw),
            }
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_smt_hex())
    }
}

/// View of a `Value` interpreted as a SyGuS Bool under the internal
/// negative-logic convention. Holds when the underlying value is zero.
#[derive(Clone, Copy)]
pub struct BoolValue<'a>(&'a Value);

impl<'a> BoolValue<'a> {
    /// `true` iff the wrapped value encodes SMT-true (bit pattern all-zero).
    pub fn holds(&self) -> bool {
        self.0.is_zero()
    }
}

fn truncate_big(v: BigUint, bits: usize) -> BigUint {
    if bits == 0 {
        return BigUint::zero();
    }
    let mask = (BigUint::one() << bits) - BigUint::one();
    v & mask
}

fn mask_u64(bits: usize) -> u64 {
    if bits == 0 {
        0
    } else if bits >= 64 {
        u64::MAX
    } else {
        (1u64 << bits) - 1
    }
}
