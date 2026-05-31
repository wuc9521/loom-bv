use rustc_hash::FxHashMap;
use std::collections::VecDeque;

use crate::{
    enumerate::{expr::OwnedExpr, grammar::TemplateExpr},
    info,
    parse::deffun::{self, BitCircuitPlan, BoolAtom, BoolNode, DefineFunPlan, PlanInstr},
};

use super::{ExactGrammar, ExactRule, NullarySpec};

#[derive(Clone, Copy)]
struct WorkItem {
    nt_idx: usize,
    rule_idx: usize,
}

impl WorkItem {
    fn new(nt_idx: usize, rule_idx: usize) -> Self {
        Self { nt_idx, rule_idx }
    }
}

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

    fn union_inplace(&mut self, other: &Self) {
        for (lhs, rhs) in self.words.iter_mut().zip(other.words.iter()) {
            *lhs |= *rhs;
        }
    }

    fn union_delta(&mut self, other: &Self) -> Self {
        let mut delta = Self {
            words: vec![0; self.words.len()],
        };
        for ((lhs, rhs), delta_word) in self
            .words
            .iter_mut()
            .zip(other.words.iter())
            .zip(delta.words.iter_mut())
        {
            let new_bits = *rhs & !*lhs;
            *lhs |= *rhs;
            *delta_word = new_bits;
        }
        delta
    }

    fn is_empty(&self) -> bool {
        self.words.iter().all(|word| *word == 0)
    }

    fn take(&mut self) -> Self {
        std::mem::replace(
            self,
            Self {
                words: vec![0; self.words.len()],
            },
        )
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

pub struct LazyRelevance<'a> {
    grammar: &'a ExactGrammar<'a>,
    nt_bits: Vec<usize>,
    dep_cache: DepCache,
    template_dep_cache: TemplateDepCache,
    relevant: Vec<BitSet>,
    pending: Vec<Vec<BitSet>>,
    queued: Vec<Vec<bool>>,
    worklist: VecDeque<WorkItem>,
    complete: bool,
    /// If `Some(idx)`, the arg index of a "closure parameter" leaf: any Leaf
    /// rule of shape `Var(idx, _)` propagates its demanded bits back to the
    /// start NT's demand, modeling a closure constraint `param = g`. This is
    /// how cyk-style synthesis with a `cfg.rhs.S` LFP placeholder is
    /// captured for backward-relevance purposes.
    closure_param: Option<usize>,
    closure_relevant: Option<BitSet>,
}

impl<'a> LazyRelevance<'a> {
    pub fn new(grammar: &'a ExactGrammar<'a>, spec: &NullarySpec) -> Option<Self> {
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

        let mut relevant = nt_bits
            .iter()
            .map(|bits| BitSet::new(*bits))
            .collect::<Vec<_>>();
        let mut pending = grammar
            .nts
            .iter()
            .enumerate()
            .map(|(nt_idx, (_, rules))| {
                rules.iter()
                    .map(|_| BitSet::new(nt_bits[nt_idx]))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let mut queued = grammar
            .nts
            .iter()
            .map(|(_, rules)| vec![false; rules.len()])
            .collect::<Vec<_>>();
        let mut worklist = VecDeque::new();
        let mut start_demand = BitSet::new(*bits);
        for bit in known_bits.keys() {
            relevant[grammar.start].insert(*bit);
            start_demand.insert(*bit);
        }
        if !start_demand.is_empty() {
            for rule_idx in 0..grammar.nts[grammar.start].1.len() {
                pending[grammar.start][rule_idx].union_inplace(&start_demand);
                queued[grammar.start][rule_idx] = true;
                worklist.push_back(WorkItem::new(grammar.start, rule_idx));
            }
        }

        Some(Self {
            grammar,
            nt_bits,
            dep_cache: DepCache::default(),
            template_dep_cache: TemplateDepCache::default(),
            relevant,
            pending,
            queued,
            worklist,
            complete: false,
            closure_param: None,
            closure_relevant: None,
        })
    }

    /// Variant of [`Self::new`] that wires a "closure feedback" edge.  When
    /// `closure_param` is set, processing a `Leaf(Var(closure_param, _))`
    /// rule propagates its demanded bits back to the start NT, modeling the
    /// closure constraint of cyk-style synthesis (`param = g`).
    pub fn new_with_closure(
        grammar: &'a ExactGrammar<'a>,
        spec: &NullarySpec,
        closure_param: usize,
    ) -> Option<Self> {
        let mut this = Self::new(grammar, spec)?;
        this.closure_param = Some(closure_param);
        this.closure_relevant = Some(BitSet::new(this.nt_bits[grammar.start]));
        Some(this)
    }

    pub fn advance(&mut self, budget: usize) -> bool {
        if self.complete {
            return true;
        }
        for _ in 0..budget {
            let Some(item) = self.worklist.pop_front() else {
                self.complete = true;
                return true;
            };
            self.queued[item.nt_idx][item.rule_idx] = false;
            let demanded = self.pending[item.nt_idx][item.rule_idx].take();
            if demanded.is_empty() {
                continue;
            }
            let nt_rules = &self.grammar.nts[item.nt_idx].1;
            let Some(rule) = nt_rules.get(item.rule_idx) else {
                continue;
            };
            if !self.process_rule_item(item, &demanded, rule) {
                self.complete = true;
                return true;
            }
        }
        false
    }

    pub fn finish(self) -> Option<Vec<Vec<usize>>> {
        self.finish_with_closure().0
    }

    pub fn finish_with_closure(self) -> (Option<Vec<Vec<usize>>>, Option<Vec<usize>>) {
        let relevant_bits = self
            .relevant
            .into_iter()
            .map(|bits| bits.iter_ones().collect::<Vec<_>>())
            .collect::<Vec<_>>();
        let reduced_any = relevant_bits
            .iter()
            .zip(self.nt_bits.iter())
            .any(|(rel, bits)| rel.len() < *bits);
        if !reduced_any {
            info!("relevance: all bits relevant, no reduction");
        }
        let closure_bits = self
            .closure_relevant
            .map(|bits| bits.iter_ones().collect::<Vec<_>>())
            .filter(|bits| !bits.is_empty());
        (reduced_any.then_some(relevant_bits), closure_bits)
    }

    fn process_rule_item(&mut self, _item: WorkItem, demanded: &BitSet, rule: &ExactRule) -> bool {
        match rule {
            ExactRule::Alias(child_nt) => {
                self.propagate_bits(*child_nt, demanded);
                true
            }
            ExactRule::Leaf(expr) => {
                if let Some(closure_idx) = self.closure_param {
                    if let OwnedExpr::Var(i, _) = expr {
                        if *i == closure_idx {
                            // Closure feedback: bits demanded from the closure
                            // parameter become bits demanded from g (the start NT).
                            if let Some(closure_relevant) = &mut self.closure_relevant {
                                closure_relevant.union_inplace(demanded);
                            }
                            let start = self.grammar.start;
                            self.propagate_bits(start, demanded);
                        }
                    }
                }
                true
            }
            ExactRule::Unary { fid, child_nt } => {
                let Some(dep) = get_deffun_dep_bits(*fid, 1, demanded, &mut self.dep_cache) else {
                    return false;
                };
                self.propagate_dep(&dep, 0, *child_nt);
                true
            }
            ExactRule::Binary { fid, lhs_nt, rhs_nt } => {
                let Some(dep) = get_deffun_dep_bits(*fid, 2, demanded, &mut self.dep_cache)
                else {
                    return false;
                };
                self.propagate_dep(&dep, 0, *lhs_nt);
                self.propagate_dep(&dep, 1, *rhs_nt);
                true
            }
            ExactRule::Nary { fid, child_nts } => {
                let Some(dep) =
                    get_deffun_dep_bits(*fid, child_nts.len(), demanded, &mut self.dep_cache)
                else {
                    return false;
                };
                for (arg_idx, child_nt) in child_nts.iter().enumerate() {
                    self.propagate_dep(&dep, arg_idx, *child_nt);
                }
                true
            }
            ExactRule::GenericTemplate {
                template,
                child_nts,
                ..
            } => {
                let slot_bits = child_nts
                    .iter()
                    .map(|child_nt| self.nt_bits[*child_nt])
                    .collect::<Vec<_>>();
                let mut dep = BitDep::empty(&slot_bits);
                for bit in demanded.iter_ones() {
                    let Some(bit_dep) = compute_template_dep_bit(
                        template,
                        &slot_bits,
                        bit,
                        &mut self.dep_cache,
                        &mut self.template_dep_cache,
                    ) else {
                        return false;
                    };
                    dep.union_inplace(&bit_dep);
                }
                for (arg_idx, child_nt) in child_nts.iter().enumerate() {
                    self.propagate_dep(&dep, arg_idx, *child_nt);
                }
                true
            }
        }
    }

    fn propagate_bits(&mut self, nt_idx: usize, bits: &BitSet) {
        let delta = self.relevant[nt_idx].union_delta(bits);
        if delta.is_empty() {
            return;
        }
        for rule_idx in 0..self.pending[nt_idx].len() {
            self.pending[nt_idx][rule_idx].union_inplace(&delta);
            if !self.queued[nt_idx][rule_idx] {
                self.queued[nt_idx][rule_idx] = true;
                self.worklist.push_back(WorkItem::new(nt_idx, rule_idx));
            }
        }
    }

    fn propagate_dep(&mut self, dep: &BitDep, arg_idx: usize, child_nt: usize) {
        let Some(bits) = dep.per_arg.get(arg_idx) else {
            return;
        };
        self.propagate_bits(child_nt, bits);
    }
}

pub fn compute_relevant_bits_for_spec(
    grammar: &ExactGrammar<'_>,
    spec: &NullarySpec,
) -> Option<Vec<Vec<usize>>> {
    let mut lazy = LazyRelevance::new(grammar, spec)?;
    while !lazy.advance(1024) {}
    lazy.finish()
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
    let dep = match deffun::ENV.plan(fid, nargs) {
        DefineFunPlan::BitCircuit(plan) => compute_bit_circuit_dep_bit(plan, &arg_bits, bit),
        DefineFunPlan::Generic {
            root,
            slot_bits,
            instrs,
            ..
        } => compute_generic_dep_bit(*root, slot_bits, instrs, &arg_bits, bit, cache),
    };
    cache.insert((fid, nargs, bit), dep.clone());
    dep
}

fn get_deffun_dep_bits(
    fid: usize,
    nargs: usize,
    demanded: &BitSet,
    cache: &mut DepCache,
) -> Option<BitDep> {
    let arg_bits = deffun::ENV.arg_bits(fid, nargs).to_vec();
    match deffun::ENV.plan(fid, nargs) {
        DefineFunPlan::BitCircuit(plan) => Some(compute_bit_circuit_dep_bits(plan, &arg_bits, demanded)),
        DefineFunPlan::Generic {
            root,
            slot_bits,
            instrs,
            ..
        } => compute_generic_dep_bits(*root, slot_bits, instrs, &arg_bits, demanded, cache),
    }
}

fn compute_bit_circuit_dep_bit(
    plan: &BitCircuitPlan,
    arg_bits: &[usize],
    bit: usize,
) -> Option<BitDep> {
    if bit >= plan.ret_bits {
        return None;
    }

    fn atom_dep(
        atom: &BoolAtom,
        bindings: &[BoolNode],
        arg_bits: &[usize],
        memo: &mut FxHashMap<usize, BitDep>,
    ) -> Option<BitDep> {
        match atom {
            BoolAtom::Const(_) => Some(BitDep::empty(arg_bits)),
            BoolAtom::InputBit { arg, bit } => {
                let width = *arg_bits.get(*arg)?;
                (*bit < width).then(|| BitDep::single_slot(arg_bits, *arg, *bit))
            }
            BoolAtom::Temp(idx) => {
                if let Some(dep) = memo.get(idx) {
                    return Some(dep.clone());
                }
                let binding = bindings.get(*idx)?;
                let dep = match binding {
                    BoolNode::Atom(atom) | BoolNode::Not(atom) => {
                        atom_dep(atom, bindings, arg_bits, memo)?
                    }
                    BoolNode::And(lhs, rhs) | BoolNode::Or(lhs, rhs) | BoolNode::Xor(lhs, rhs) => {
                        let mut dep = atom_dep(lhs, bindings, arg_bits, memo)?;
                        dep.union_inplace(&atom_dep(rhs, bindings, arg_bits, memo)?);
                        dep
                    }
                    BoolNode::Ite(cond, then_atom, else_atom) => {
                        let mut dep = atom_dep(cond, bindings, arg_bits, memo)?;
                        dep.union_inplace(&atom_dep(then_atom, bindings, arg_bits, memo)?);
                        dep.union_inplace(&atom_dep(else_atom, bindings, arg_bits, memo)?);
                        dep
                    }
                };
                memo.insert(*idx, dep.clone());
                Some(dep)
            }
        }
    }

    let mut memo = FxHashMap::default();
    atom_dep(&plan.output_bits[bit], &plan.bindings, arg_bits, &mut memo)
}

fn compute_bit_circuit_dep_bits(
    plan: &BitCircuitPlan,
    arg_bits: &[usize],
    demanded: &BitSet,
) -> BitDep {
    fn visit_atom(
        atom: &BoolAtom,
        bindings: &[BoolNode],
        seen: &mut [bool],
        out: &mut BitDep,
    ) {
        match atom {
            BoolAtom::Const(_) => {}
            BoolAtom::InputBit { arg, bit } => out.per_arg[*arg].insert(*bit),
            BoolAtom::Temp(idx) => {
                if std::mem::replace(&mut seen[*idx], true) {
                    return;
                }
                match &bindings[*idx] {
                    BoolNode::Atom(atom) | BoolNode::Not(atom) => visit_atom(atom, bindings, seen, out),
                    BoolNode::And(lhs, rhs) | BoolNode::Or(lhs, rhs) | BoolNode::Xor(lhs, rhs) => {
                        visit_atom(lhs, bindings, seen, out);
                        visit_atom(rhs, bindings, seen, out);
                    }
                    BoolNode::Ite(cond, then_atom, else_atom) => {
                        visit_atom(cond, bindings, seen, out);
                        visit_atom(then_atom, bindings, seen, out);
                        visit_atom(else_atom, bindings, seen, out);
                    }
                }
            }
        }
    }

    let mut out = BitDep::empty(arg_bits);
    let mut seen = vec![false; plan.bindings.len()];
    for bit in demanded.iter_ones() {
        if bit < plan.ret_bits {
            visit_atom(&plan.output_bits[bit], &plan.bindings, &mut seen, &mut out);
        }
    }
    out
}

fn compute_generic_dep_bit(
    root: usize,
    slot_bits: &[usize],
    instrs: &[PlanInstr],
    arg_bits: &[usize],
    bit: usize,
    cache: &mut DepCache,
) -> Option<BitDep> {
    fn slot_dep(
        slot: usize,
        bit: usize,
        slot_bits: &[usize],
        instrs: &[PlanInstr],
        arg_bits: &[usize],
        cache: &mut DepCache,
        memo: &mut FxHashMap<(usize, usize), Option<BitDep>>,
    ) -> Option<BitDep> {
        if let Some(dep) = memo.get(&(slot, bit)) {
            return dep.clone();
        }
        let width = *slot_bits.get(slot)?;
        if bit >= width {
            memo.insert((slot, bit), None);
            return None;
        }
        let dep = if slot < arg_bits.len() {
            Some(BitDep::single_slot(arg_bits, slot, bit))
        } else {
            let instr = instrs.get(slot.checked_sub(arg_bits.len())?)?;
            match instr {
                PlanInstr::Const(_) => Some(BitDep::empty(arg_bits)),
                PlanInstr::Concat { lhs, rhs } => {
                    let rhs_bits = *slot_bits.get(*rhs)?;
                    if bit < rhs_bits {
                        slot_dep(*rhs, bit, slot_bits, instrs, arg_bits, cache, memo)
                    } else {
                        slot_dep(
                            *lhs,
                            bit - rhs_bits,
                            slot_bits,
                            instrs,
                            arg_bits,
                            cache,
                            memo,
                        )
                    }
                }
                PlanInstr::Extract { src, hi, lo } => {
                    let extract_width = (*hi - *lo + 1) as usize;
                    if bit >= extract_width {
                        None
                    } else {
                        slot_dep(
                            *src,
                            *lo as usize + bit,
                            slot_bits,
                            instrs,
                            arg_bits,
                            cache,
                            memo,
                        )
                    }
                }
                PlanInstr::Not { src } => {
                    slot_dep(*src, bit, slot_bits, instrs, arg_bits, cache, memo)
                }
                PlanInstr::And { lhs, rhs }
                | PlanInstr::Or { lhs, rhs }
                | PlanInstr::Xor { lhs, rhs } => {
                    let mut dep = slot_dep(*lhs, bit, slot_bits, instrs, arg_bits, cache, memo)?;
                    dep.union_inplace(&slot_dep(
                        *rhs, bit, slot_bits, instrs, arg_bits, cache, memo,
                    )?);
                    Some(dep)
                }
                PlanInstr::Ite {
                    cond,
                    then_slot,
                    else_slot,
                } => {
                    let mut dep = slot_dep(*cond, 0, slot_bits, instrs, arg_bits, cache, memo)?;
                    dep.union_inplace(&slot_dep(
                        *then_slot, bit, slot_bits, instrs, arg_bits, cache, memo,
                    )?);
                    dep.union_inplace(&slot_dep(
                        *else_slot, bit, slot_bits, instrs, arg_bits, cache, memo,
                    )?);
                    Some(dep)
                }
                PlanInstr::Fop0Dyn { fid } => get_deffun_dep_bit(*fid, 0, bit, cache),
                PlanInstr::Fop1Dyn { fid, arg } => {
                    let outer = get_deffun_dep_bit(*fid, 1, bit, cache)?;
                    let mut combined = BitDep::empty(arg_bits);
                    for inner_bit in outer.per_arg[0].iter_ones() {
                        combined.union_inplace(&slot_dep(
                            *arg, inner_bit, slot_bits, instrs, arg_bits, cache, memo,
                        )?);
                    }
                    Some(combined)
                }
                PlanInstr::Fop2Dyn { fid, lhs, rhs } => {
                    let outer = get_deffun_dep_bit(*fid, 2, bit, cache)?;
                    let mut combined = BitDep::empty(arg_bits);
                    for inner_bit in outer.per_arg[0].iter_ones() {
                        combined.union_inplace(&slot_dep(
                            *lhs, inner_bit, slot_bits, instrs, arg_bits, cache, memo,
                        )?);
                    }
                    for inner_bit in outer.per_arg[1].iter_ones() {
                        combined.union_inplace(&slot_dep(
                            *rhs, inner_bit, slot_bits, instrs, arg_bits, cache, memo,
                        )?);
                    }
                    Some(combined)
                }
                PlanInstr::FopDyn { fid, args } => {
                    let outer = get_deffun_dep_bit(*fid, args.len(), bit, cache)?;
                    let mut combined = BitDep::empty(arg_bits);
                    for (arg_idx, bits) in outer.per_arg.iter().enumerate() {
                        let arg_slot = *args.get(arg_idx)?;
                        for inner_bit in bits.iter_ones() {
                            combined.union_inplace(&slot_dep(
                                arg_slot, inner_bit, slot_bits, instrs, arg_bits, cache, memo,
                            )?);
                        }
                    }
                    Some(combined)
                }
                PlanInstr::Neg { .. }
                | PlanInstr::Add { .. }
                | PlanInstr::Mul { .. }
                | PlanInstr::Sub { .. }
                | PlanInstr::LShr { .. }
                | PlanInstr::AShr { .. }
                | PlanInstr::Shl { .. }
                | PlanInstr::UDiv { .. }
                | PlanInstr::URem { .. }
                | PlanInstr::SDiv { .. }
                | PlanInstr::SRem { .. } => Some(BitDep::full(arg_bits)),
            }
        };
        memo.insert((slot, bit), dep.clone());
        dep
    }

    let mut memo = FxHashMap::default();
    slot_dep(root, bit, slot_bits, instrs, arg_bits, cache, &mut memo)
}

fn compute_generic_dep_bits(
    root: usize,
    slot_bits: &[usize],
    instrs: &[PlanInstr],
    arg_bits: &[usize],
    demanded: &BitSet,
    cache: &mut DepCache,
) -> Option<BitDep> {
    fn enqueue_slot(
        slot: usize,
        bits: &BitSet,
        demanded_by_slot: &mut [BitSet],
        stack: &mut Vec<(usize, BitSet)>,
    ) {
        let delta = demanded_by_slot[slot].union_delta(bits);
        if !delta.is_empty() {
            stack.push((slot, delta));
        }
    }

    let mut out = BitDep::empty(arg_bits);
    let mut demanded_by_slot = slot_bits
        .iter()
        .map(|bits| BitSet::new(*bits))
        .collect::<Vec<_>>();
    let mut stack = Vec::<(usize, BitSet)>::new();
    enqueue_slot(root, demanded, &mut demanded_by_slot, &mut stack);

    while let Some((slot, delta)) = stack.pop() {
        if slot < arg_bits.len() {
            out.per_arg[slot].union_inplace(&delta);
            continue;
        }
        let instr = instrs.get(slot.checked_sub(arg_bits.len())?)?;
        match instr {
            PlanInstr::Const(_) => {}
            PlanInstr::Concat { lhs, rhs } => {
                let rhs_width = slot_bits[*rhs];
                let mut lhs_bits = BitSet::new(slot_bits[*lhs]);
                let mut rhs_bits = BitSet::new(rhs_width);
                for bit in delta.iter_ones() {
                    if bit < rhs_width {
                        rhs_bits.insert(bit);
                    } else {
                        lhs_bits.insert(bit - rhs_width);
                    }
                }
                enqueue_slot(*lhs, &lhs_bits, &mut demanded_by_slot, &mut stack);
                enqueue_slot(*rhs, &rhs_bits, &mut demanded_by_slot, &mut stack);
            }
            PlanInstr::Extract { src, lo, .. } => {
                let mut src_bits = BitSet::new(slot_bits[*src]);
                for bit in delta.iter_ones() {
                    src_bits.insert(*lo as usize + bit);
                }
                enqueue_slot(*src, &src_bits, &mut demanded_by_slot, &mut stack);
            }
            PlanInstr::Not { src } => {
                enqueue_slot(*src, &delta, &mut demanded_by_slot, &mut stack);
            }
            PlanInstr::And { lhs, rhs }
            | PlanInstr::Or { lhs, rhs }
            | PlanInstr::Xor { lhs, rhs } => {
                enqueue_slot(*lhs, &delta, &mut demanded_by_slot, &mut stack);
                enqueue_slot(*rhs, &delta, &mut demanded_by_slot, &mut stack);
            }
            PlanInstr::Ite {
                cond,
                then_slot,
                else_slot,
            } => {
                let mut cond_bits = BitSet::new(slot_bits[*cond]);
                cond_bits.insert(0);
                enqueue_slot(*cond, &cond_bits, &mut demanded_by_slot, &mut stack);
                enqueue_slot(*then_slot, &delta, &mut demanded_by_slot, &mut stack);
                enqueue_slot(*else_slot, &delta, &mut demanded_by_slot, &mut stack);
            }
            PlanInstr::Fop0Dyn { fid } => {
                let _ = get_deffun_dep_bits(*fid, 0, &delta, cache)?;
            }
            PlanInstr::Fop1Dyn { fid, arg } => {
                let outer = get_deffun_dep_bits(*fid, 1, &delta, cache)?;
                enqueue_slot(*arg, &outer.per_arg[0], &mut demanded_by_slot, &mut stack);
            }
            PlanInstr::Fop2Dyn { fid, lhs, rhs } => {
                let outer = get_deffun_dep_bits(*fid, 2, &delta, cache)?;
                enqueue_slot(*lhs, &outer.per_arg[0], &mut demanded_by_slot, &mut stack);
                enqueue_slot(*rhs, &outer.per_arg[1], &mut demanded_by_slot, &mut stack);
            }
            PlanInstr::FopDyn { fid, args } => {
                let outer = get_deffun_dep_bits(*fid, args.len(), &delta, cache)?;
                for (arg_idx, bits) in outer.per_arg.iter().enumerate() {
                    enqueue_slot(args[arg_idx], bits, &mut demanded_by_slot, &mut stack);
                }
            }
            PlanInstr::Neg { src } => {
                enqueue_slot(
                    *src,
                    &BitSet::full(slot_bits[*src]),
                    &mut demanded_by_slot,
                    &mut stack,
                );
            }
            PlanInstr::Add { lhs, rhs }
            | PlanInstr::Mul { lhs, rhs }
            | PlanInstr::Sub { lhs, rhs }
            | PlanInstr::LShr { lhs, rhs }
            | PlanInstr::AShr { lhs, rhs }
            | PlanInstr::Shl { lhs, rhs }
            | PlanInstr::UDiv { lhs, rhs }
            | PlanInstr::URem { lhs, rhs }
            | PlanInstr::SDiv { lhs, rhs }
            | PlanInstr::SRem { lhs, rhs } => {
                enqueue_slot(
                    *lhs,
                    &BitSet::full(slot_bits[*lhs]),
                    &mut demanded_by_slot,
                    &mut stack,
                );
                enqueue_slot(
                    *rhs,
                    &BitSet::full(slot_bits[*rhs]),
                    &mut demanded_by_slot,
                    &mut stack,
                );
            }
        }
    }

    Some(out)
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
        OwnedExpr::Var(idx, _) => {
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
    if dep.per_arg.len() < slot_idx + 1 {
        return None;
    }
    let mut combined = BitDep::empty(scope_bits);
    for (arg_idx, bits) in dep.per_arg.iter().enumerate() {
        if arg_idx < slot_idx {
            combined.per_arg[arg_idx].union_inplace(bits);
        } else if arg_idx == slot_idx {
            for bit in bits.iter_ones() {
                combined.union_inplace(&compute_expr_dep_bit(value, scope_bits, bit, cache)?);
            }
        } else {
            // Extra slots beyond the one being collapsed — pass through
            // This can happen when Var indices don't perfectly align with let-binding order
            if arg_idx < scope_bits.len() {
                combined.per_arg[arg_idx].union_inplace(bits);
            }
        }
    }
    Some(combined)
}
