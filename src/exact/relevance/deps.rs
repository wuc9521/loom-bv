//! Per-operator bit-dependency analysis.
//!
//! Given a `BitCircuitPlan` or `Generic` `DefineFunPlan`, compute which
//! input bits each output bit depends on (single-bit form) or, for a
//! demanded subset of output bits, which input bits collectively feed
//! them (set form). Used by the lazy relevance worklist in
//! `relevance::mod` to backward-propagate demand from constraint bits to
//! the leaves.

use rustc_hash::FxHashMap;

use crate::{
    enumerate::{expr::OwnedExpr, grammar::TemplateExpr},
    parse::deffun::{self, BitCircuitPlan, BoolAtom, BoolNode, DefineFunPlan, PlanInstr},
};

use super::bits::{BitDep, BitSet};

pub type DepCache = FxHashMap<(usize, usize, usize), Option<BitDep>>;
pub type TemplateDepCache = FxHashMap<(usize, usize), Option<BitDep>>;

pub fn get_deffun_dep_bit(
    fid: usize,
    nargs: usize,
    bit: usize,
    cache: &mut DepCache,
) -> Option<BitDep> {
    if let Some(dep) = cache.get(&(fid, nargs, bit)) {
        return dep.clone();
    }
    // See `get_deffun_dep_bits` — same extended-arg_bits reason.
    let mut arg_bits = deffun::ENV.arg_bits(fid, nargs).to_vec();
    arg_bits.extend_from_slice(deffun::ENV.closure_arg_bits(fid, nargs));
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

pub fn get_deffun_dep_bits(
    fid: usize,
    nargs: usize,
    demanded: &BitSet,
    cache: &mut DepCache,
) -> Option<BitDep> {
    // Use EXTENDED arg_bits = user args + closure-synth-fun args. Define-fun
    // bodies may reference closure synth-funs (SyGuS 2.1 §3.7); their
    // identifiers were resolved to Var slots beyond the real arity at parse
    // time. Without this extension, dependency walks treat synth-arg slots
    // as instructions and quietly mis-attribute demand.
    let mut arg_bits = deffun::ENV.arg_bits(fid, nargs).to_vec();
    arg_bits.extend_from_slice(deffun::ENV.closure_arg_bits(fid, nargs));
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

pub fn compute_template_dep_bit(
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
            // Extra slots beyond the one being collapsed — pass through.
            // This can happen when Var indices don't perfectly align with let-binding order.
            if arg_idx < scope_bits.len() {
                combined.per_arg[arg_idx].union_inplace(bits);
            }
        }
    }
    Some(combined)
}
