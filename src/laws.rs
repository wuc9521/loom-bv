//! Operator algebra recognized from a program's `(assume …)` laws.
//!
//! A SyGuS/FACET program may declare equational laws about its operators
//! (e.g. associativity of a concatenation, that an alternation list is a set).
//! This module recognizes such laws purely by their equation *shape* — it never
//! assumes constructor names — and exposes them as flags any synthesis mode can
//! use: the const-hole enumerator uses them to canonicalize and dedup candidate
//! terms, and the value enumerator's `RuleClass` can be populated from them for
//! define-fun operators it otherwise refuses to probe.

use std::collections::{HashMap, HashSet};

use sygus_parser::ast::SyGuSTerm;

/// Algebraic properties of grammar/term operators, recognized from `(assume …)`.
#[derive(Default, Debug)]
pub struct OpLaws {
    /// Binary commutative operators: `(F x y) = (F y x)`.
    pub binary_comm: HashSet<String>,
    /// Binary idempotent operators: `(F x x) = x`.
    pub binary_idemp: HashSet<String>,
    /// Associative operators (nested applications flatten into a sequence).
    pub assoc: HashSet<String>,
    /// "Set-cons" operators: an unordered collection built along a spine.
    /// Maps op → (element-arg index, spine-arg index).
    pub set_ops: HashMap<String, (usize, usize)>,
    /// The collection is order-insensitive (sort elements).
    pub set_commute: bool,
    /// The collection is duplicate-insensitive (dedup elements).
    pub set_idemp: bool,
    /// Set-cons elements that are neutral for a specific cons operator.
    /// For example, a CFG self-unit production `S -> S` can be dropped from the
    /// rule set without changing the least language.
    pub set_drop: HashMap<String, HashSet<String>>,
}

impl OpLaws {
    /// Recognize laws from a list of `(assume …)` equation terms.
    pub fn from_assumes(assumes: &[&SyGuSTerm]) -> Self {
        let mut laws = OpLaws::default();
        for t in assumes {
            let Some(("=", l, r)) = as_bin(t) else {
                continue;
            };
            if let Some(f) = rec_assoc(l, r) {
                laws.assoc.insert(f);
            }
            if let Some(f) = rec_assoc(r, l) {
                laws.assoc.insert(f);
            }
            if let Some(f) = rec_commute(l, r) {
                laws.binary_comm.insert(f);
            }
            if let Some(f) = rec_idemp(l, r).or_else(|| rec_idemp(r, l)) {
                laws.binary_idemp.insert(f);
            }
            if let Some((f, g)) = rec_spine_commute(l, r) {
                laws.set_ops.insert(f, (0, 1));
                laws.set_ops.insert(g, (0, 1));
                laws.set_commute = true;
            }
            if let Some(f) = rec_spine_idemp(l, r) {
                laws.set_ops.entry(f).or_insert((0, 1));
                laws.set_idemp = true;
            }
            if let Some((f, elem)) = rec_spine_drop(l, r).or_else(|| rec_spine_drop(r, l)) {
                laws.set_ops.entry(f.clone()).or_insert((0, 1));
                laws.set_drop.entry(f).or_default().insert(elem);
            }
        }
        laws
    }
}

impl OpLaws {
    pub fn binary_class(&self, op: &str) -> crate::enumerate::grammar::RuleClass {
        crate::enumerate::grammar::RuleClass {
            commutative: self.binary_comm.contains(op),
            idempotent: self.binary_idemp.contains(op),
            associative: self.assoc.contains(op),
            ..Default::default()
        }
    }
}

/// A binary application `(F a b)` → `(F, a, b)`.
fn as_bin(t: &SyGuSTerm) -> Option<(&str, &SyGuSTerm, &SyGuSTerm)> {
    match t {
        SyGuSTerm::Application(id, args) if args.len() == 2 => {
            Some((id.get_name(), &args[0], &args[1]))
        }
        _ => None,
    }
}

fn as_var(t: &SyGuSTerm) -> Option<&str> {
    match t {
        SyGuSTerm::Identifier(id) => Some(id.get_name()),
        _ => None,
    }
}

/// `(F x y) = (F y x)` ⇒ `F` commutative.
fn rec_commute(l: &SyGuSTerm, r: &SyGuSTerm) -> Option<String> {
    let (f, x, y) = as_bin(l)?;
    let (fr, y2, x2) = as_bin(r)?;
    let (x, y, x2, y2) = (as_var(x)?, as_var(y)?, as_var(x2)?, as_var(y2)?);
    if f == fr && x == x2 && y == y2 && x != y {
        Some(f.to_string())
    } else {
        None
    }
}

/// `(F x x) = x` ⇒ `F` idempotent.
fn rec_idemp(l: &SyGuSTerm, r: &SyGuSTerm) -> Option<String> {
    let (f, x, y) = as_bin(l)?;
    let (x, y, r) = (as_var(x)?, as_var(y)?, as_var(r)?);
    if x == y && x == r {
        Some(f.to_string())
    } else {
        None
    }
}

/// `(F (F x y) z) = (F x (F y z))` ⇒ `F` associative.
fn rec_assoc(l: &SyGuSTerm, r: &SyGuSTerm) -> Option<String> {
    let (f, l0, l1) = as_bin(l)?;
    let (fr, r0, r1) = as_bin(r)?;
    let (fa, x, y) = as_bin(l0)?;
    let (fb, y2, z2) = as_bin(r1)?;
    let (x, y, z) = (as_var(x)?, as_var(y)?, as_var(l1)?);
    let (x2, y2, z2) = (as_var(r0)?, as_var(y2)?, as_var(z2)?);
    if f == fr && fa == f && fb == f && x == x2 && y == y2 && z == z2 {
        Some(f.to_string())
    } else {
        None
    }
}

/// `(F a (G b t)) = (F b (G a t))` ⇒ `F`,`G` are cons-cells of an unordered
/// collection (element at arg0, spine at arg1).
fn rec_spine_commute(l: &SyGuSTerm, r: &SyGuSTerm) -> Option<(String, String)> {
    let (f, a, li) = as_bin(l)?;
    let (g, b, t1) = as_bin(li)?;
    let (fr, b2, ri) = as_bin(r)?;
    let (gr, a2, t2) = as_bin(ri)?;
    let (a, b, t1) = (as_var(a)?, as_var(b)?, as_var(t1)?);
    let (b2, a2, t2) = (as_var(b2)?, as_var(a2)?, as_var(t2)?);
    if f == fr && g == gr && a == a2 && b == b2 && t1 == t2 && a != b {
        Some((f.to_string(), g.to_string()))
    } else {
        None
    }
}

/// `(F a (F a t)) = (F a t)` ⇒ `F`'s collection is duplicate-insensitive.
fn rec_spine_idemp(l: &SyGuSTerm, r: &SyGuSTerm) -> Option<String> {
    let (f, a, li) = as_bin(l)?;
    let (f2, a2, t1) = as_bin(li)?;
    let (fr, a3, t2) = as_bin(r)?;
    let (a, a2, a3) = (as_var(a)?, as_var(a2)?, as_var(a3)?);
    if f == f2 && f == fr && a == a2 && a == a3 && as_var(t1)? == as_var(t2)? {
        Some(f.to_string())
    } else {
        None
    }
}

/// `(F elem t) = t` ⇒ `elem` is neutral in `F`'s collection spine.
fn rec_spine_drop(l: &SyGuSTerm, r: &SyGuSTerm) -> Option<(String, String)> {
    let (f, elem, tail) = as_bin(l)?;
    let tail = as_var(tail)?;
    if as_var(r)? == tail {
        Some((f.to_string(), term_key(elem)?))
    } else {
        None
    }
}

fn term_key(t: &SyGuSTerm) -> Option<String> {
    match t {
        SyGuSTerm::Identifier(id) => Some(id.get_name().to_string()),
        SyGuSTerm::Application(id, args) => {
            if args.is_empty() {
                Some(id.get_name().to_string())
            } else {
                let parts = args.iter().map(term_key).collect::<Option<Vec<_>>>()?;
                Some(format!("({} {})", id.get_name(), parts.join(" ")))
            }
        }
        SyGuSTerm::Annotated(inner, _) => term_key(inner),
        _ => None,
    }
}
