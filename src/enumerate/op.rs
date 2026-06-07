use crate::enumerate::value::BitVec;

use super::expr::DivideByZero;

#[inline(always)]
pub fn not(v1: BitVec) -> BitVec {
    v1.bitnot()
}
#[inline(always)]
pub fn neg(v1: BitVec) -> BitVec {
    v1.neg()
}
#[inline(always)]
pub fn add(v1: BitVec, v2: BitVec) -> BitVec {
    v1.add(v2)
}
#[inline(always)]
pub fn mul(v1: BitVec, v2: BitVec) -> BitVec {
    v1.mul(v2)
}
#[inline(always)]
pub fn sub(v1: BitVec, v2: BitVec) -> BitVec {
    v1.sub(v2)
}
#[inline(always)]
pub fn xor(v1: BitVec, v2: BitVec) -> BitVec {
    v1.bitxor(v2)
}
#[inline(always)]
pub fn and(v1: BitVec, v2: BitVec) -> BitVec {
    v1.bitand(v2)
}
#[inline(always)]
pub fn or(v1: BitVec, v2: BitVec) -> BitVec {
    v1.bitor(v2)
}
#[inline(always)]
pub fn udiv(v1: BitVec, v2: BitVec) -> Result<BitVec, DivideByZero> {
    v1.udiv(v2).ok_or(DivideByZero)
}
#[inline(always)]
pub fn urem(v1: BitVec, v2: BitVec) -> Result<BitVec, DivideByZero> {
    v1.urem(v2).ok_or(DivideByZero)
}

#[inline(always)]
pub fn lshr(this: BitVec, that: BitVec) -> BitVec {
    this.lshr(that)
}
#[inline(always)]
pub fn ashr(this: BitVec, that: BitVec) -> BitVec {
    this.ashr(that)
}
#[inline(always)]
pub fn shl(this: BitVec, that: BitVec) -> BitVec {
    this.shl(that)
}
#[inline(always)]
pub fn sdiv(this: BitVec, that: BitVec) -> Result<BitVec, DivideByZero> {
    this.sdiv(that).ok_or(DivideByZero)
}
#[inline(always)]
pub fn srem(this: BitVec, that: BitVec) -> Result<BitVec, DivideByZero> {
    this.srem(that).ok_or(DivideByZero)
}

#[inline(always)]
pub fn ite(v1: BitVec, v2: BitVec, v3: BitVec) -> BitVec {
    // dryadsynth's internal Bool encoding is negative: a Bool expression is
    // represented by a BV that is 0 iff the underlying SMT condition is
    // *true* (e.g. SMT `(= A B)` is parsed as `Xor(A, B)`, which is 0 iff
    // A == B). So when v1.is_zero() the SMT cond is true and we return the
    // then-branch v2.
    if v1.is_zero() {
        v2
    } else {
        v3
    }
}

#[inline(always)]
pub fn ule(a: BitVec, b: BitVec) -> BitVec {
    BitVec::from_u64(if a.ule(&b) { 0 } else { 1 }, 1)
}
#[inline(always)]
pub fn ult(a: BitVec, b: BitVec) -> BitVec {
    BitVec::from_u64(if a.ult(&b) { 0 } else { 1 }, 1)
}
#[inline(always)]
pub fn sle(a: BitVec, b: BitVec) -> BitVec {
    BitVec::from_u64(if a.sle(&b) { 0 } else { 1 }, 1)
}
#[inline(always)]
pub fn slt(a: BitVec, b: BitVec) -> BitVec {
    BitVec::from_u64(if a.slt(&b) { 0 } else { 1 }, 1)
}

