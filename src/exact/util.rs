//! Small helpers used by `exact/lfp.rs`. The bit-extract helpers live in
//! `parse::constraint` (the canonical home for SyGuS-term parsing); this
//! module just re-exports `empty_span` and the bit-index helper.

use sygus_parser::ast::Identifier;

pub use crate::parse::constraint::{empty_span, extract_indices_from_identifier};

/// `((_ extract i i) target)` — yields `Some(i)` only when single-bit.
pub fn extract_single_bit_idx(id: &Identifier) -> Option<usize> {
    let (hi, lo) = extract_indices_from_identifier(id)?;
    (hi == lo).then_some(hi)
}
