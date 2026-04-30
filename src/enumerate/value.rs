use std::fmt;

use num_bigint::{BigInt, BigUint, Sign};
use num_traits::{One, Signed, ToPrimitive, Zero};

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Value {
    Small { bits: usize, raw: u64 },
    Big { bits: usize, raw: BigUint },
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
            Value::Small {
                bits,
                raw: raw & mask,
            }
        } else {
            Value::Big {
                bits,
                raw: truncate_big(BigUint::from(raw), bits),
            }
        }
    }

    pub fn from_biguint(raw: BigUint, bits: usize) -> Self {
        if bits <= 64 {
            Value::Small {
                bits,
                raw: (raw & BigUint::from(mask_u64(bits))).to_u64().unwrap_or(0),
            }
        } else {
            Value::Big {
                bits,
                raw: truncate_big(raw, bits),
            }
        }
    }

    pub fn zero(bits: usize) -> Self {
        Self::from_u64(0, bits)
    }

    pub fn is_zero(&self) -> bool {
        match self {
            Value::Small { raw, .. } => *raw == 0,
            Value::Big { raw, .. } => raw.is_zero(),
        }
    }

    pub fn as_u64_lossy(&self) -> u64 {
        match self {
            Value::Small { raw, .. } => *raw,
            Value::Big { raw, .. } => raw.to_u64().unwrap_or(0),
        }
    }

    pub fn to_biguint(&self) -> BigUint {
        match self {
            Value::Small { raw, .. } => BigUint::from(*raw),
            Value::Big { raw, .. } => raw.clone(),
        }
    }

    pub fn bit(&self, bit: usize) -> bool {
        if bit >= self.bits() {
            return false;
        }
        match self {
            Value::Small { raw, .. } => ((*raw >> bit) & 1) == 1,
            Value::Big { raw, .. } => {
                let limb = bit / 64;
                let offset = bit % 64;
                raw.iter_u64_digits()
                    .nth(limb)
                    .map(|digit| ((digit >> offset) & 1) == 1)
                    .unwrap_or(false)
            }
        }
    }

    pub fn to_smt_hex(&self) -> String {
        let bits = self.bits();
        let hex_len = bits.div_ceil(4).max(1);
        let v = match self {
            Value::Small { raw, .. } => format!("{:x}", raw),
            Value::Big { raw, .. } => format!("{:x}", raw),
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
                let fill = (!0u64) << (bits - s);
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
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_smt_hex())
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
