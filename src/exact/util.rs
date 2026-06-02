//! Helpers shared between `exact/spec.rs` and `exact/lfp.rs`.

use pest::Span;
use sygus_parser::ast::{Identifier, Index};

pub fn empty_span() -> Span<'static> {
    Span::new("", 0, 0).expect("empty span should be valid")
}

pub fn numeral_index(idx: &Index) -> Option<usize> {
    match idx {
        Index::Numeral(v) => Some(*v),
        Index::Symbol(_) => None,
    }
}

/// Parse `(_ extract hi lo)` indices from an Identifier in any of the forms
/// `Indexed("extract", [hi, lo])`, `Indexed("_", ["extract", hi, lo])`, or
/// a parenthesised string fallback. Returns `None` if it's not an extract.
pub fn extract_indices_from_identifier(id: &Identifier) -> Option<(usize, usize)> {
    match id {
        Identifier::Indexed(sym, idxs) if sym == "extract" && idxs.len() >= 2 => {
            match (numeral_index(&idxs[0]), numeral_index(&idxs[1])) {
                (Some(hi), Some(lo)) => Some((hi, lo)),
                _ => None,
            }
        }
        Identifier::Indexed(sym, idxs) if sym == "_" && idxs.len() >= 3 => {
            match (&idxs[0], numeral_index(&idxs[1]), numeral_index(&idxs[2])) {
                (Index::Symbol(op), Some(hi), Some(lo)) if op == "extract" => Some((hi, lo)),
                _ => None,
            }
        }
        _ => None,
    }
    .or_else(|| {
        let text = id.to_string();
        let parts = text
            .trim_matches(|c| c == '(' || c == ')')
            .split_whitespace()
            .collect::<Vec<_>>();
        match parts.as_slice() {
            ["_", "extract", hi, lo] | ["extract", hi, lo] => {
                match (hi.parse::<usize>(), lo.parse::<usize>()) {
                    (Ok(hi), Ok(lo)) => Some((hi, lo)),
                    _ => None,
                }
            }
            _ => None,
        }
    })
}

/// `((_ extract i i) target)` — yields `Some(i)` only when single-bit.
pub fn extract_single_bit_idx(id: &Identifier) -> Option<usize> {
    let (hi, lo) = extract_indices_from_identifier(id)?;
    (hi == lo).then_some(hi)
}
