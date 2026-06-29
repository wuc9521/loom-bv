use std::collections::HashMap;

use crate::{
    enumerate::{expr::OwnedExpr, value::BitVec},
    exact::Constraint,
    solutions::Solutions,
};

// ---------------------------------------------------------------------------
// Slice-level operations on Vec<BitVec>
// ---------------------------------------------------------------------------

fn slice_imples(a: &[BitVec], b: &[BitVec]) -> bool {
    a.iter().zip(b.iter()).all(|(ai, bi)| {
        // a implies b iff !a | b == all-ones
        ai.clone().bitnot().bitor(bi.clone()).is_ones()
    })
}

fn slice_count(a: &[BitVec]) -> u32 {
    a.iter().map(|v| v.count_ones()).sum()
}

fn slice_count_zeros(a: &[BitVec]) -> u32 {
    a.iter().map(|v| v.count_zeros()).sum()
}

fn slice_and(a: &[BitVec], b: &[BitVec]) -> Vec<BitVec> {
    a.iter()
        .zip(b.iter())
        .map(|(ai, bi)| ai.clone().bitand(bi.clone()))
        .collect()
}

fn slice_or(a: &[BitVec], b: &[BitVec]) -> Vec<BitVec> {
    a.iter()
        .zip(b.iter())
        .map(|(ai, bi)| ai.clone().bitor(bi.clone()))
        .collect()
}

fn slice_not(a: &[BitVec]) -> Vec<BitVec> {
    a.iter().map(|v| v.clone().bitnot()).collect()
}

fn slice_xor(a: &[BitVec], b: &[BitVec]) -> Vec<BitVec> {
    a.iter()
        .zip(b.iter())
        .map(|(ai, bi)| ai.clone().bitxor(bi.clone()))
        .collect()
}

fn slice_sub(a: &[BitVec], b: &[BitVec]) -> Vec<BitVec> {
    a.iter()
        .zip(b.iter())
        .map(|(ai, bi)| ai.clone().sub(bi.clone()))
        .collect()
}

fn slice_eq(a: &[BitVec], b: &[BitVec]) -> bool {
    a.iter().zip(b.iter()).all(|(ai, bi)| ai == bi)
}

fn slice_is_zeros(a: &[BitVec]) -> bool {
    a.iter().all(|v| v.is_zero())
}

// ---------------------------------------------------------------------------
// Reverse Rule
// ---------------------------------------------------------------------------

pub struct ReverseRule {
    output: Vec<BitVec>,
    start_map: HashMap<Vec<BitVec>, OwnedExpr>,
    pub add: bool,
    pub xor: bool,
}

impl ReverseRule {
    pub fn new(output: &[BitVec]) -> Self {
        Self {
            output: output.to_vec(),
            start_map: HashMap::new(),
            add: true,
            xor: true,
        }
    }

    pub fn insert(&mut self, values: &[BitVec], expr: OwnedExpr) {
        self.start_map.entry(values.to_vec()).or_insert(expr);
    }

    pub fn try_reverse(&self, expr: &OwnedExpr, values: &[BitVec]) -> Option<OwnedExpr> {
        if self.add {
            let key = slice_sub(&self.output, values);
            if let Some(partner) = self.start_map.get(&key) {
                return Some(OwnedExpr::Add(
                    Box::new(expr.clone()),
                    Box::new(partner.clone()),
                ));
            }
        }
        if self.xor {
            let key = slice_xor(&self.output, values);
            if let Some(partner) = self.start_map.get(&key) {
                return Some(OwnedExpr::Xor(
                    Box::new(expr.clone()),
                    Box::new(partner.clone()),
                ));
            }
        }
        None
    }
}

// ---------------------------------------------------------------------------
// Combine Rule
// ---------------------------------------------------------------------------

#[derive(Clone)]
enum CombineEntry {
    And(OwnedExpr, Vec<BitVec>),
    Or(OwnedExpr, Vec<BitVec>),
}

pub struct CombineRule {
    n: usize,
    mask: Vec<BitVec>,
    output: Vec<BitVec>,
    entries: Vec<CombineEntry>,
}

impl CombineRule {
    pub fn new(output: &[BitVec]) -> Self {
        let n = output.len();
        let mask: Vec<BitVec> = output.iter().map(|v| BitVec::ones(v.bits())).collect();
        Self {
            n,
            mask,
            output: output.to_vec(),
            entries: Vec::new(),
        }
    }

    pub fn test(
        &mut self,
        expr: &OwnedExpr,
        values: &[BitVec],
        spec: &Constraint,
    ) -> Option<OwnedExpr> {
        let mask_count = slice_count(&self.mask);

        // AND: values implies output
        if slice_imples(values, &self.output) {
            let masked_v = slice_and(&self.mask, values);
            let and_count = slice_count(&masked_v);
            let and_cnstr = mask_count - and_count > 2 * (self.n as u32);
            if and_cnstr
                && 3 * slice_count_zeros(values) > slice_count_zeros(&self.output)
                && (self.n >= spec.len() || spec.test_and(expr))
            {
                let committed = slice_or(&slice_not(&self.mask), values);
                self.entries
                    .push(CombineEntry::And(expr.clone(), committed));
                self.mask = slice_and(&self.mask, values);
            }
        }

        // OR: output implies values
        if slice_imples(&self.output, values) {
            let not_v = slice_not(values);
            let masked_not_v = slice_and(&self.mask, &not_v);
            let or_count = slice_count(&masked_not_v);
            let or_cnstr = mask_count - or_count > 2 * (self.n as u32);
            if or_cnstr
                && 3 * slice_count(values) > slice_count(&self.output)
                && (self.n >= spec.len() || spec.test_or(expr))
            {
                let committed = slice_and(&self.mask, values);
                self.entries.push(CombineEntry::Or(expr.clone(), committed));
                self.mask = slice_and(&self.mask, &not_v);
            }
        }

        // Check if mask ∧ (values ⊕ output) == 0 → assembled full solution
        let diff = slice_xor(values, &self.output);
        let residual = slice_and(&self.mask, &diff);
        if slice_is_zeros(&residual) && !self.entries.is_empty() {
            return self.collect_expr(expr, values);
        }
        None
    }

    fn collect_expr(&self, base_expr: &OwnedExpr, base_values: &[BitVec]) -> Option<OwnedExpr> {
        let mut res = base_expr.clone();
        let mut value = base_values.to_vec();
        let mut size = 0usize;
        for entry in self.entries.iter().rev() {
            match entry {
                CombineEntry::And(e, first) => {
                    if !slice_eq(&slice_and(&value, first), &value) {
                        res = OwnedExpr::And(Box::new(e.clone()), Box::new(res));
                        value = slice_and(&value, first);
                        size += 1;
                    }
                }
                CombineEntry::Or(e, first) => {
                    if !slice_eq(&slice_or(&value, first), &value) {
                        res = OwnedExpr::Or(Box::new(e.clone()), Box::new(res));
                        value = slice_or(&value, first);
                        size += 1;
                    }
                }
            }
        }
        if size > 4 {
            return None;
        }
        Some(res)
    }
}

// ---------------------------------------------------------------------------
// Unified Deductive State
// ---------------------------------------------------------------------------

pub struct DeductiveState {
    reverse: ReverseRule,
    combine: CombineRule,
    enable_combine: bool,
    pub count: usize,
}

impl DeductiveState {
    pub fn new(output: &[BitVec], enable_reverse: bool, enable_combine: bool) -> Self {
        let mut reverse = ReverseRule::new(output);
        if !enable_reverse {
            reverse.add = false;
            reverse.xor = false;
        }
        Self {
            reverse,
            combine: CombineRule::new(output),
            enable_combine,
            count: 0,
        }
    }

    pub fn on_candidate(
        &mut self,
        expr: &OwnedExpr,
        values: &[BitVec],
        sol: &mut Solutions,
        spec: &Constraint,
    ) -> Result<(), ()> {
        self.count += 1;

        self.reverse.insert(values, expr.clone());

        if let Some(derived) = self.reverse.try_reverse(expr, values) {
            if sol.add_solution_owned(&derived, self.count) {
                return Err(());
            }
        }

        if self.enable_combine {
            if let Some(derived) = self.combine.test(expr, values, spec) {
                if sol.add_solution_owned(&derived, self.count) {
                    return Err(());
                }
            }
        }

        Ok(())
    }
}
