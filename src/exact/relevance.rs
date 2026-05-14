use rustc_hash::FxHashMap;
use std::collections::VecDeque;

use crate::{
    enumerate::{expr::OwnedExpr, grammar::TemplateExpr},
    parse::deffun,
};

use super::{ExactGrammar, ExactRule, NullarySpec};

#[derive(Clone, Default)]
struct BitSet {
    words: Vec<u64>,
}

impl BitSet {
    fn new(bits: usize) -> Self {
        Self {
            words: vec![0; bits.div_ceil(64)],
        }
    }

    fn full(bits: usize) -> Self {
        let mut set = Self::new(bits);
        let full_words = bits / 64;
        for word in &mut set.words[..full_words] {
            *word = u64::MAX;
        }
        let rem = bits % 64;
        if rem != 0 {
            set.words[full_words] = (1u64 << rem) - 1;
        }
        set
    }

    fn insert(&mut self, bit: usize) {
        let word = bit / 64;
        if word < self.words.len() {
            self.words[word] |= 1u64 << (bit % 64);
        }
    }

    fn insert_new(&mut self, bit: usize) -> bool {
        let word = bit / 64;
        if word >= self.words.len() {
            return false;
        }
        let mask = 1u64 << (bit % 64);
        let old = self.words[word];
        self.words[word] |= mask;
        old & mask == 0
    }

    fn union_inplace(&mut self, other: &Self) {
        for (lhs, rhs) in self.words.iter_mut().zip(other.words.iter()) {
            *lhs |= *rhs;
        }
    }

    fn iter_ones(&self) -> impl Iterator<Item = usize> + '_ {
        self.words.iter().enumerate().flat_map(|(word_idx, word)| {
            let mut word = *word;
            std::iter::from_fn(move || {
                if word == 0 {
                    return None;
                }
                let bit = word.trailing_zeros() as usize;
                word &= word - 1;
                Some(word_idx * 64 + bit)
            })
        })
    }
}

#[derive(Clone)]
struct BitDep {
    per_arg: Vec<BitSet>,
}

impl BitDep {
    fn empty(arg_bits: &[usize]) -> Self {
        Self {
            per_arg: arg_bits.iter().map(|bits| BitSet::new(*bits)).collect(),
        }
    }

    fn full(arg_bits: &[usize]) -> Self {
        Self {
            per_arg: arg_bits.iter().map(|bits| BitSet::full(*bits)).collect(),
        }
    }

    fn single_slot(arg_bits: &[usize], arg_idx: usize, bit: usize) -> Self {
        let mut dep = Self::empty(arg_bits);
        dep.per_arg[arg_idx].insert(bit);
        dep
    }

    fn union_inplace(&mut self, other: &Self) {
        for (lhs, rhs) in self.per_arg.iter_mut().zip(other.per_arg.iter()) {
            lhs.union_inplace(rhs);
        }
    }
}

type DepCache = FxHashMap<(usize, usize, usize), Option<BitDep>>;
type TemplateDepCache = FxHashMap<(usize, usize), Option<BitDep>>;

pub fn compute_relevant_bits_for_spec(
    grammar: &ExactGrammar<'_>,
    spec: &NullarySpec,
) -> Option<Vec<Vec<usize>>> {
    let NullarySpec::BitConstraints {
        bits,
        known_bits,
        structural,
    } = spec
    else {
        return None;
    };
    if !structural.is_empty() || known_bits.is_empty() {
        return None;
    }

    let nt_bits = grammar
        .nts
        .iter()
        .map(|(_, rules)| nt_output_bits(rules))
        .collect::<Vec<_>>();
    if nt_bits.get(grammar.start).copied() != Some(*bits) {
        return None;
    }

    let mut dep_cache = DepCache::default();
    let mut template_dep_cache = TemplateDepCache::default();
    let mut relevant = nt_bits
        .iter()
        .map(|bits| BitSet::new(*bits))
        .collect::<Vec<_>>();
    let mut worklist = VecDeque::new();
    for bit in known_bits.keys() {
        if relevant[grammar.start].insert_new(*bit) {
            worklist.push_back((grammar.start, *bit));
        }
    }

    while let Some((nt_idx, bit)) = worklist.pop_front() {
        for rule in &grammar.nts[nt_idx].1 {
            match rule {
                ExactRule::Alias(child_nt) => {
                    if relevant[*child_nt].insert_new(bit) {
                        worklist.push_back((*child_nt, bit));
                    }
                }
                ExactRule::Leaf(_) => {}
                ExactRule::Unary { fid, child_nt } => {
                    let Some(dep) = get_deffun_dep_bit(*fid, 1, bit, &mut dep_cache) else {
                        return None;
                    };
                    propagate_dep(&dep, 0, *child_nt, &mut relevant, &mut worklist);
                }
                ExactRule::Binary {
                    fid,
                    lhs_nt,
                    rhs_nt,
                } => {
                    let Some(dep) = get_deffun_dep_bit(*fid, 2, bit, &mut dep_cache) else {
                        return None;
                    };
                    propagate_dep(&dep, 0, *lhs_nt, &mut relevant, &mut worklist);
                    propagate_dep(&dep, 1, *rhs_nt, &mut relevant, &mut worklist);
                }
                ExactRule::Nary { fid, child_nts } => {
                    let Some(dep) = get_deffun_dep_bit(*fid, child_nts.len(), bit, &mut dep_cache)
                    else {
                        return None;
                    };
                    for (arg_idx, child_nt) in child_nts.iter().enumerate() {
                        propagate_dep(&dep, arg_idx, *child_nt, &mut relevant, &mut worklist);
                    }
                }
                ExactRule::GenericTemplate {
                    template,
                    child_nts,
                    ..
                } => {
                    let slot_bits = child_nts
                        .iter()
                        .map(|child_nt| nt_bits[*child_nt])
                        .collect::<Vec<_>>();
                    let dep = compute_template_dep_bit(
                        template,
                        &slot_bits,
                        bit,
                        &mut dep_cache,
                        &mut template_dep_cache,
                    );
                    let Some(dep) = dep else {
                        return None;
                    };
                    for (arg_idx, child_nt) in child_nts.iter().enumerate() {
                        propagate_dep(&dep, arg_idx, *child_nt, &mut relevant, &mut worklist);
                    }
                }
            }
        }
    }

    let relevant_bits = relevant
        .into_iter()
        .map(|bits| bits.iter_ones().collect::<Vec<_>>())
        .collect::<Vec<_>>();
    let reduced_any = relevant_bits
        .iter()
        .zip(nt_bits.iter())
        .any(|(rel, bits)| rel.len() < *bits);
    reduced_any.then_some(relevant_bits)
}

fn propagate_dep(
    dep: &BitDep,
    arg_idx: usize,
    child_nt: usize,
    relevant: &mut [BitSet],
    worklist: &mut VecDeque<(usize, usize)>,
) {
    let Some(bits) = dep.per_arg.get(arg_idx) else {
        return;
    };
    let child_relevant = &mut relevant[child_nt];
    for child_bit in bits.iter_ones() {
        if child_relevant.insert_new(child_bit) {
            worklist.push_back((child_nt, child_bit));
        }
    }
}

pub fn nt_output_bits(rules: &[ExactRule]) -> usize {
    for rule in rules {
        match rule {
            ExactRule::Alias(_) => {}
            ExactRule::Leaf(expr) => return expr.width(),
            ExactRule::Unary { fid, .. } => return deffun::ENV.ret_bits(*fid, 1),
            ExactRule::Binary { fid, .. } => return deffun::ENV.ret_bits(*fid, 2),
            ExactRule::Nary { fid, child_nts } => {
                return deffun::ENV.ret_bits(*fid, child_nts.len())
            }
            ExactRule::GenericTemplate { template, .. } => return template.output_bits(),
        }
    }
    1
}

fn get_deffun_dep_bit(
    fid: usize,
    nargs: usize,
    bit: usize,
    cache: &mut DepCache,
) -> Option<BitDep> {
    if let Some(dep) = cache.get(&(fid, nargs, bit)) {
        return dep.clone();
    }
    let arg_bits = deffun::ENV.arg_bits(fid, nargs).to_vec();
    let dep = compute_expr_dep_bit(deffun::ENV.apply(fid, nargs), &arg_bits, bit, cache);
    cache.insert((fid, nargs, bit), dep.clone());
    dep
}

fn compute_template_dep_bit(
    template: &TemplateExpr,
    slot_bits: &[usize],
    bit: usize,
    cache: &mut DepCache,
    template_cache: &mut TemplateDepCache,
) -> Option<BitDep> {
    let key = (template as *const TemplateExpr as usize, bit);
    if let Some(dep) = template_cache.get(&key) {
        return dep.clone();
    }

    let dep = match template {
        TemplateExpr::Slot(slot) => {
            let bits = *slot_bits.get(*slot)?;
            (bit < bits).then(|| BitDep::single_slot(slot_bits, *slot, bit))
        }
        TemplateExpr::Leaf(expr) => compute_expr_dep_bit(expr, slot_bits, bit, cache),
        TemplateExpr::App(id, parts) => {
            let fid = deffun::ENV.lookup(id.get_name(), parts.len())?;
            let outer = get_deffun_dep_bit(fid, parts.len(), bit, cache)?;
            let mut combined = BitDep::empty(slot_bits);
            for (arg_idx, bits) in outer.per_arg.iter().enumerate() {
                let part = parts.get(arg_idx)?;
                for inner_bit in bits.iter_ones() {
                    let dep = compute_template_dep_bit(
                        part,
                        slot_bits,
                        inner_bit,
                        cache,
                        template_cache,
                    )?;
                    combined.union_inplace(&dep);
                }
            }
            Some(combined)
        }
    };
    template_cache.insert(key, dep.clone());
    dep
}

fn compute_expr_dep_bit(
    expr: &OwnedExpr,
    arg_bits: &[usize],
    bit: usize,
    cache: &mut DepCache,
) -> Option<BitDep> {
    match expr {
        OwnedExpr::Const(value) => (bit < value.bits()).then(|| BitDep::empty(arg_bits)),
        OwnedExpr::Var(idx) => {
            let bits = *arg_bits.get(*idx)?;
            (bit < bits).then(|| BitDep::single_slot(arg_bits, *idx, bit))
        }
        OwnedExpr::Let(_, _, _) => compute_let_dep_bit(expr, arg_bits, bit, cache),
        OwnedExpr::Extract(inner, hi, lo) => {
            let width = (*hi - *lo + 1) as usize;
            if bit >= width {
                return None;
            }
            compute_expr_dep_bit(inner, arg_bits, *lo as usize + bit, cache)
        }
        OwnedExpr::Concat(high, low) => {
            let low_bits = low.width();
            if bit < low_bits {
                compute_expr_dep_bit(low, arg_bits, bit, cache)
            } else {
                compute_expr_dep_bit(high, arg_bits, bit - low_bits, cache)
            }
        }
        OwnedExpr::Not(inner) => compute_expr_dep_bit(inner, arg_bits, bit, cache),
        OwnedExpr::And(lhs, rhs) | OwnedExpr::Or(lhs, rhs) | OwnedExpr::Xor(lhs, rhs) => {
            let mut dep = compute_expr_dep_bit(lhs, arg_bits, bit, cache)?;
            let rhs_dep = compute_expr_dep_bit(rhs, arg_bits, bit, cache)?;
            dep.union_inplace(&rhs_dep);
            Some(dep)
        }
        OwnedExpr::Ite(cond, then_expr, else_expr) => {
            let mut dep = compute_expr_dep_bit(cond, arg_bits, 0, cache)?;
            dep.union_inplace(&compute_expr_dep_bit(then_expr, arg_bits, bit, cache)?);
            dep.union_inplace(&compute_expr_dep_bit(else_expr, arg_bits, bit, cache)?);
            Some(dep)
        }
        OwnedExpr::Fop0Dyn(fid) => get_deffun_dep_bit(*fid, 0, bit, cache),
        OwnedExpr::Fop1Dyn(fid, arg) => {
            let outer = get_deffun_dep_bit(*fid, 1, bit, cache)?;
            let mut combined = BitDep::empty(arg_bits);
            for inner_bit in outer.per_arg[0].iter_ones() {
                combined.union_inplace(&compute_expr_dep_bit(arg, arg_bits, inner_bit, cache)?);
            }
            Some(combined)
        }
        OwnedExpr::Fop2Dyn(fid, lhs, rhs) => {
            let outer = get_deffun_dep_bit(*fid, 2, bit, cache)?;
            let mut combined = BitDep::empty(arg_bits);
            for inner_bit in outer.per_arg[0].iter_ones() {
                combined.union_inplace(&compute_expr_dep_bit(lhs, arg_bits, inner_bit, cache)?);
            }
            for inner_bit in outer.per_arg[1].iter_ones() {
                combined.union_inplace(&compute_expr_dep_bit(rhs, arg_bits, inner_bit, cache)?);
            }
            Some(combined)
        }
        OwnedExpr::FopDyn(fid, args) => {
            let outer = get_deffun_dep_bit(*fid, args.len(), bit, cache)?;
            let mut combined = BitDep::empty(arg_bits);
            for (arg_idx, bits) in outer.per_arg.iter().enumerate() {
                let arg = args.get(arg_idx)?;
                for inner_bit in bits.iter_ones() {
                    combined.union_inplace(&compute_expr_dep_bit(arg, arg_bits, inner_bit, cache)?);
                }
            }
            Some(combined)
        }
        other => {
            let width = other.width();
            (bit < width).then(|| BitDep::full(arg_bits))
        }
    }
}

fn compute_let_dep_bit(
    expr: &OwnedExpr,
    arg_bits: &[usize],
    bit: usize,
    cache: &mut DepCache,
) -> Option<BitDep> {
    let base_nargs = arg_bits.len();
    let mut values = Vec::new();
    let mut extended_arg_bits = arg_bits.to_vec();
    let mut current = expr;

    while let OwnedExpr::Let(_, value, body) = current {
        values.push(value.as_ref());
        extended_arg_bits.push(value.width());
        current = body;
    }

    let mut dep = compute_expr_dep_bit(current, &extended_arg_bits, bit, cache)?;
    for (binding_idx, value) in values.into_iter().enumerate().rev() {
        let slot_idx = base_nargs + binding_idx;
        dep = collapse_bound_slot(dep, slot_idx, value, &extended_arg_bits, cache)?;
        extended_arg_bits.pop();
    }
    Some(dep)
}

fn collapse_bound_slot(
    dep: BitDep,
    slot_idx: usize,
    value: &OwnedExpr,
    scope_bits: &[usize],
    cache: &mut DepCache,
) -> Option<BitDep> {
    if dep.per_arg.len() != slot_idx + 1 {
        return None;
    }
    let mut combined = BitDep::empty(scope_bits);
    for (arg_idx, bits) in dep.per_arg.iter().enumerate() {
        if arg_idx < slot_idx {
            combined.per_arg[arg_idx].union_inplace(bits);
        } else {
            for bit in bits.iter_ones() {
                combined.union_inplace(&compute_expr_dep_bit(value, scope_bits, bit, cache)?);
            }
        }
    }
    Some(combined)
}
