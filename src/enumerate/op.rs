use crate::enumerate::value::Value;

use super::expr::DivideByZero;

#[inline(always)]
pub fn not(v1: Value) -> Value {
    v1.bitnot()
}
#[inline(always)]
pub fn neg(v1: Value) -> Value {
    v1.neg()
}
#[inline(always)]
pub fn add(v1: Value, v2: Value) -> Value {
    v1.add(v2)
}
#[inline(always)]
pub fn mul(v1: Value, v2: Value) -> Value {
    v1.mul(v2)
}
#[inline(always)]
pub fn sub(v1: Value, v2: Value) -> Value {
    v1.sub(v2)
}
#[inline(always)]
pub fn xor(v1: Value, v2: Value) -> Value {
    v1.bitxor(v2)
}
#[inline(always)]
pub fn and(v1: Value, v2: Value) -> Value {
    v1.bitand(v2)
}
#[inline(always)]
pub fn or(v1: Value, v2: Value) -> Value {
    v1.bitor(v2)
}
#[inline(always)]
pub fn udiv(v1: Value, v2: Value) -> Result<Value, DivideByZero> {
    v1.udiv(v2).ok_or(DivideByZero)
}
#[inline(always)]
pub fn urem(v1: Value, v2: Value) -> Result<Value, DivideByZero> {
    v1.urem(v2).ok_or(DivideByZero)
}

#[inline(always)]
pub fn lshr(this: Value, that: Value) -> Value {
    this.lshr(that)
}
#[inline(always)]
pub fn ashr(this: Value, that: Value) -> Value {
    this.ashr(that)
}
#[inline(always)]
pub fn shl(this: Value, that: Value) -> Value {
    this.shl(that)
}
#[inline(always)]
pub fn sdiv(this: Value, that: Value) -> Result<Value, DivideByZero> {
    this.sdiv(that).ok_or(DivideByZero)
}
#[inline(always)]
pub fn srem(this: Value, that: Value) -> Result<Value, DivideByZero> {
    this.srem(that).ok_or(DivideByZero)
}

#[inline(always)]
pub fn ite(v1: Value, v2: Value, v3: Value) -> Value {
    if v1.is_zero() {
        v2
    } else {
        v3
    }
}

#[inline(always)]
fn u64_not(v1: u64) -> u64 {
    !v1
}
#[inline(always)]
fn u64_neg(v1: u64) -> u64 {
    (0i64.wrapping_sub(v1 as i64)) as u64
}
#[inline(always)]
fn u64_add(v1: u64, v2: u64) -> u64 {
    v1.wrapping_add(v2)
}
#[inline(always)]
fn u64_mul(v1: u64, v2: u64) -> u64 {
    v1.wrapping_mul(v2)
}
#[inline(always)]
fn u64_sub(v1: u64, v2: u64) -> u64 {
    v1.wrapping_sub(v2)
}
#[inline(always)]
fn u64_xor(v1: u64, v2: u64) -> u64 {
    v1 ^ v2
}
#[inline(always)]
fn u64_and(v1: u64, v2: u64) -> u64 {
    v1 & v2
}
#[inline(always)]
fn u64_or(v1: u64, v2: u64) -> u64 {
    v1 | v2
}
#[inline(always)]
fn u64_lshr(this: u64, that: u64) -> u64 {
    if that >= 64 {
        0
    } else {
        this >> that
    }
}
#[inline(always)]
fn u64_shl(this: u64, that: u64) -> u64 {
    if that >= 64 {
        0
    } else {
        this << that
    }
}
#[inline(always)]
fn u64_ashr(this: u64, that: u64) -> u64 {
    if that >= 64 {
        0
    } else {
        ((this as i64) >> (that as i64)) as u64
    }
}
#[inline(always)]
fn u64_udiv(v1: u64, v2: u64) -> u64 {
    v1.checked_div(v2).unwrap_or(0)
}
#[inline(always)]
fn u64_urem(v1: u64, v2: u64) -> u64 {
    v1.checked_rem(v2).unwrap_or(0)
}
#[inline(always)]
fn u64_sdiv(v1: u64, v2: u64) -> u64 {
    if v2 == 0 {
        0
    } else {
        (v1 as i64).overflowing_div(v2 as i64).0 as u64
    }
}
#[inline(always)]
fn u64_srem(v1: u64, v2: u64) -> u64 {
    if v2 == 0 {
        0
    } else {
        (v1 as i64).overflowing_rem(v2 as i64).0 as u64
    }
}
#[inline(always)]
fn u64_ite(v1: u64, v2: u64, v3: u64) -> u64 {
    if v1 == 0 {
        v2
    } else {
        v3
    }
}

pub mod bv {

    use crate::enumerate::Bv;

    #[inline(always)]
    pub fn not<const N: usize>(v1: Bv<N>) -> Bv<N> {
        v1.map(super::u64_not).into()
    }
    #[inline(always)]
    pub fn neg<const N: usize>(v1: Bv<N>) -> Bv<N> {
        v1.map(super::u64_neg).into()
    }
    #[inline(always)]
    pub fn add<const N: usize>(v1: Bv<N>, v2: Bv<N>) -> Bv<N> {
        Bv(v1
            .into_iter_fixed()
            .zip(v2.into_iter_fixed())
            .map(|(a, b)| super::u64_add(a, b))
            .collect())
    }
    #[inline(always)]
    pub fn xor<const N: usize>(v1: Bv<N>, v2: Bv<N>) -> Bv<N> {
        Bv(v1
            .into_iter_fixed()
            .zip(v2.into_iter_fixed())
            .map(|(a, b)| super::u64_xor(a, b))
            .collect())
    }
    #[inline(always)]
    pub fn and<const N: usize>(v1: Bv<N>, v2: Bv<N>) -> Bv<N> {
        Bv(v1
            .into_iter_fixed()
            .zip(v2.into_iter_fixed())
            .map(|(a, b)| super::u64_and(a, b))
            .collect())
    }
    #[inline(always)]
    pub fn or<const N: usize>(v1: Bv<N>, v2: Bv<N>) -> Bv<N> {
        Bv(v1
            .into_iter_fixed()
            .zip(v2.into_iter_fixed())
            .map(|(a, b)| super::u64_or(a, b))
            .collect())
    }
    #[inline(always)]
    pub fn mul<const N: usize>(v1: Bv<N>, v2: Bv<N>) -> Bv<N> {
        Bv(v1
            .into_iter_fixed()
            .zip(v2.into_iter_fixed())
            .map(|(a, b)| super::u64_mul(a, b))
            .collect())
    }
    #[inline(always)]
    pub fn sub<const N: usize>(v1: Bv<N>, v2: Bv<N>) -> Bv<N> {
        Bv(v1
            .into_iter_fixed()
            .zip(v2.into_iter_fixed())
            .map(|(a, b)| super::u64_sub(a, b))
            .collect())
    }
    #[inline(always)]
    pub fn lshr<const N: usize>(v1: Bv<N>, v2: Bv<N>) -> Bv<N> {
        Bv(v1
            .into_iter_fixed()
            .zip(v2.into_iter_fixed())
            .map(|(a, b)| super::u64_lshr(a, b))
            .collect())
    }
    #[inline(always)]
    pub fn shl<const N: usize>(v1: Bv<N>, v2: Bv<N>) -> Bv<N> {
        Bv(v1
            .into_iter_fixed()
            .zip(v2.into_iter_fixed())
            .map(|(a, b)| super::u64_shl(a, b))
            .collect())
    }
    #[inline(always)]
    pub fn udiv<const N: usize>(v1: Bv<N>, v2: Bv<N>) -> Bv<N> {
        Bv(v1
            .into_iter_fixed()
            .zip(v2.into_iter_fixed())
            .map(|(a, b)| super::u64_udiv(a, b))
            .collect())
    }
    #[inline(always)]
    pub fn sdiv<const N: usize>(v1: Bv<N>, v2: Bv<N>) -> Bv<N> {
        Bv(v1
            .into_iter_fixed()
            .zip(v2.into_iter_fixed())
            .map(|(a, b)| super::u64_sdiv(a, b))
            .collect())
    }
    #[inline(always)]
    pub fn urem<const N: usize>(v1: Bv<N>, v2: Bv<N>) -> Bv<N> {
        Bv(v1
            .into_iter_fixed()
            .zip(v2.into_iter_fixed())
            .map(|(a, b)| super::u64_urem(a, b))
            .collect())
    }
    #[inline(always)]
    pub fn srem<const N: usize>(v1: Bv<N>, v2: Bv<N>) -> Bv<N> {
        Bv(v1
            .into_iter_fixed()
            .zip(v2.into_iter_fixed())
            .map(|(a, b)| super::u64_srem(a, b))
            .collect())
    }
    #[inline(always)]
    pub fn ashr<const N: usize>(v1: Bv<N>, v2: Bv<N>) -> Bv<N> {
        Bv(v1
            .into_iter_fixed()
            .zip(v2.into_iter_fixed())
            .map(|(a, b)| super::u64_ashr(a, b))
            .collect())
    }
    #[inline(always)]
    pub fn ite<const N: usize>(v1: Bv<N>, v2: Bv<N>, v3: Bv<N>) -> Bv<N> {
        Bv(v1
            .into_iter_fixed()
            .zip(v2.into_iter_fixed())
            .zip(v3.into_iter_fixed())
            .map(|((a, b), c)| super::u64_ite(a, b, c))
            .collect())
    }

}
