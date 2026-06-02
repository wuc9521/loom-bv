//! Closure binding for the LFP-mode search.
//!
//! In fixpoint mode the search treats the candidate as the body of a
//! recursive synth-fun named `closure_name`. Each evaluation needs to
//! substitute a concrete `Value` for `closure_name` — either `zero` (the
//! sub-NT fingerprint sample) or `top` (the second sample for the pair
//! dedup key). Bundling them into one struct replaces the four loose
//! locals (`closure_zero` / `closure_top` / `closure_binding` /
//! `closure_binding_top`) that used to be threaded through the search.
//!
//! Direct (non-fixpoint) mode is represented as `Option::None` at the
//! call site; this struct never holds a "no closure" sentinel.

use crate::enumerate::value::Value;

pub struct Closure {
    pub name: String,
    pub zero: Value,
    pub top: Value,
}

impl Closure {
    pub fn new(name: impl Into<String>, bits: usize) -> Self {
        Self {
            name: name.into(),
            zero: Value::zero(bits),
            top: Value::zero(bits).bitnot(),
        }
    }

    /// `Some(...)` binding to pass to `eval_defined_with_closure` for the
    /// `aux=0` sample.
    pub fn binding_zero(&self) -> (&str, &Value) {
        (&self.name, &self.zero)
    }

    /// `Some(...)` binding for the `aux=top` sample.
    pub fn binding_top(&self) -> (&str, &Value) {
        (&self.name, &self.top)
    }
}
