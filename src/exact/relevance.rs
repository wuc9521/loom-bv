use rustc_hash::FxHashMap;

use crate::{
    enumerate::{expr::OwnedExpr, grammar::TemplateExpr},
    parse::deffun,
};

use super::{owned_expr_width, ExactGrammar, ExactRule, NullarySpec};

#[derive(Clone)]
struct BitDep {
    per_arg: Vec<Vec<usize>>,
}

impl BitDep {
    fn empty(nargs: usize) -> Self {
        Self {
            per_arg: (0..nargs).map(|_| Vec::new()).collect(),
        }
    }

    fn single_slot(nargs: usize, arg_idx: usize, bit: usize) -> Self {
        let mut dep = Self::empty(nargs);
        dep.per_arg[arg_idx].push(bit);
        dep
    }

    fn union(&self, other: &Self) -> Self {
        let mut per_arg = Vec::with_capacity(self.per_arg.len());
        for (lhs, rhs) in self.per_arg.iter().zip(other.per_arg.iter()) {
            let mut merged = lhs.clone();
            for bit in rhs {
                if !merged.contains(bit) {
                    merged.push(*bit);
                }
            }
            merged.sort_unstable();
            per_arg.push(merged);
        }
        Self { per_arg }
    }
}

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
    if !structural.is_empty() {
        return None;
    }
    if known_bits.is_empty() {
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
    let mut dep_cache = FxHashMap::<(usize, usize), Option<Vec<BitDep>>>::default();
    let mut relevant = nt_bits
        .iter()
        .map(|bits| vec![false; *bits])
        .collect::<Vec<_>>();
    for bit in known_bits.keys() {
        if *bit < relevant[grammar.start].len() {
            relevant[grammar.start][*bit] = true;
        }
    }
    let mut changed = true;
    while changed {
        changed = false;
        for (nt_idx, (_, rules)) in grammar.nts.iter().enumerate() {
            let parent_relevant = relevant[nt_idx]
                .iter()
                .enumerate()
                .filter_map(|(bit, is_rel)| is_rel.then_some(bit))
                .collect::<Vec<_>>();
            if parent_relevant.is_empty() {
                continue;
            }
            for rule in rules {
                match rule {
                    ExactRule::Alias(child_nt) => {
                        for bit in &parent_relevant {
                            if *bit < relevant[*child_nt].len() && !relevant[*child_nt][*bit] {
                                relevant[*child_nt][*bit] = true;
                                changed = true;
                            }
                        }
                    }
                    ExactRule::Leaf(_) => {}
                    ExactRule::Unary { fid, child_nt } => {
                        let Some(summary) = get_deffun_dep_summary(*fid, 1, &mut dep_cache) else {
                            return None;
                        };
                        propagate_relevant_bits(
                            &parent_relevant,
                            &summary,
                            0,
                            &mut relevant[*child_nt],
                            &mut changed,
                        );
                    }
                    ExactRule::Binary {
                        fid,
                        lhs_nt,
                        rhs_nt,
                    } => {
                        let Some(summary) = get_deffun_dep_summary(*fid, 2, &mut dep_cache) else {
                            return None;
                        };
                        propagate_relevant_bits(
                            &parent_relevant,
                            &summary,
                            0,
                            &mut relevant[*lhs_nt],
                            &mut changed,
                        );
                        propagate_relevant_bits(
                            &parent_relevant,
                            &summary,
                            1,
                            &mut relevant[*rhs_nt],
                            &mut changed,
                        );
                    }
                    ExactRule::Nary { fid, child_nts } => {
                        let Some(summary) =
                            get_deffun_dep_summary(*fid, child_nts.len(), &mut dep_cache)
                        else {
                            return None;
                        };
                        for (arg_idx, child_nt) in child_nts.iter().enumerate() {
                            propagate_relevant_bits(
                                &parent_relevant,
                                &summary,
                                arg_idx,
                                &mut relevant[*child_nt],
                                &mut changed,
                            );
                        }
                    }
                    ExactRule::GenericTemplate {
                        template,
                        child_nts,
                        ..
                    } => {
                        let Some(summary) = get_template_dep_summary(
                            template,
                            &child_nts
                                .iter()
                                .map(|child_nt| nt_bits[*child_nt])
                                .collect::<Vec<_>>(),
                            &mut dep_cache,
                        ) else {
                            return None;
                        };
                        for (arg_idx, child_nt) in child_nts.iter().enumerate() {
                            propagate_relevant_bits(
                                &parent_relevant,
                                &summary,
                                arg_idx,
                                &mut relevant[*child_nt],
                                &mut changed,
                            );
                        }
                    }
                }
            }
        }
    }
    let relevant_bits = relevant
        .into_iter()
        .map(|bits| {
            bits.into_iter()
                .enumerate()
                .filter_map(|(idx, relevant)| relevant.then_some(idx))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let reduced_any = relevant_bits
        .iter()
        .zip(nt_bits.iter())
        .any(|(rel, bits)| rel.len() < *bits);
    reduced_any.then_some(relevant_bits)
}

fn propagate_relevant_bits(
    parent_relevant: &[usize],
    summary: &[BitDep],
    arg_idx: usize,
    child_relevant: &mut [bool],
    changed: &mut bool,
) {
    for bit in parent_relevant {
        let Some(dep) = summary.get(*bit) else {
            continue;
        };
        let Some(arg_deps) = dep.per_arg.get(arg_idx) else {
            continue;
        };
        for child_bit in arg_deps {
            if *child_bit < child_relevant.len() && !child_relevant[*child_bit] {
                child_relevant[*child_bit] = true;
                *changed = true;
            }
        }
    }
}

pub fn nt_output_bits(rules: &[ExactRule]) -> usize {
    for rule in rules {
        match rule {
            ExactRule::Alias(_) => {}
            ExactRule::Leaf(expr) => return owned_expr_width(expr),
            ExactRule::Unary { fid, .. } => return deffun::ENV.ret_bits(*fid, 1),
            ExactRule::Binary { fid, .. } => return deffun::ENV.ret_bits(*fid, 2),
            ExactRule::Nary { fid, child_nts } => {
                return deffun::ENV.ret_bits(*fid, child_nts.len())
            }
            ExactRule::GenericTemplate { template, .. } => return template_output_bits(template),
        }
    }
    1
}

fn template_output_bits(template: &TemplateExpr) -> usize {
    match template {
        TemplateExpr::Slot(_) => 1,
        TemplateExpr::Leaf(expr) => owned_expr_width(expr),
        TemplateExpr::App(id, parts) => deffun::ENV
            .lookup(id.get_name(), parts.len())
            .map(|fid| deffun::ENV.ret_bits(fid, parts.len()))
            .unwrap_or(1),
    }
}

fn get_deffun_dep_summary(
    fid: usize,
    nargs: usize,
    cache: &mut FxHashMap<(usize, usize), Option<Vec<BitDep>>>,
) -> Option<Vec<BitDep>> {
    if let Some(summary) = cache.get(&(fid, nargs)) {
        return summary.clone();
    }
    let arg_bits = deffun::ENV.arg_bits(fid, nargs).to_vec();
    let summary = compute_expr_dep_summary(deffun::ENV.apply(fid, nargs), &arg_bits, cache);
    cache.insert((fid, nargs), summary.clone());
    summary
}

fn get_template_dep_summary(
    template: &TemplateExpr,
    slot_bits: &[usize],
    cache: &mut FxHashMap<(usize, usize), Option<Vec<BitDep>>>,
) -> Option<Vec<BitDep>> {
    compute_template_dep_summary(template, slot_bits, cache)
}

fn compute_template_dep_summary(
    template: &TemplateExpr,
    slot_bits: &[usize],
    cache: &mut FxHashMap<(usize, usize), Option<Vec<BitDep>>>,
) -> Option<Vec<BitDep>> {
    match template {
        TemplateExpr::Slot(slot) => {
            let bits = *slot_bits.get(*slot)?;
            Some(
                (0..bits)
                    .map(|bit| BitDep::single_slot(slot_bits.len(), *slot, bit))
                    .collect(),
            )
        }
        TemplateExpr::Leaf(expr) => compute_expr_dep_summary(expr, slot_bits, cache),
        TemplateExpr::App(id, parts) => {
            let fid = deffun::ENV.lookup(id.get_name(), parts.len())?;
            let f_summary = get_deffun_dep_summary(fid, parts.len(), cache)?;
            let part_summaries = parts
                .iter()
                .map(|part| compute_template_dep_summary(part, slot_bits, cache))
                .collect::<Option<Vec<_>>>()?;
            compose_dep_summaries(&f_summary, &part_summaries, slot_bits.len())
        }
    }
}

fn compute_expr_dep_summary(
    expr: &OwnedExpr,
    arg_bits: &[usize],
    cache: &mut FxHashMap<(usize, usize), Option<Vec<BitDep>>>,
) -> Option<Vec<BitDep>> {
    match expr {
        OwnedExpr::Const(value) => Some(
            (0..value.bits())
                .map(|_| BitDep::empty(arg_bits.len()))
                .collect(),
        ),
        OwnedExpr::Var(idx) => {
            let bits = *arg_bits.get(*idx)?;
            Some(
                (0..bits)
                    .map(|bit| BitDep::single_slot(arg_bits.len(), *idx, bit))
                    .collect(),
            )
        }
        OwnedExpr::Extract(inner, hi, lo) => {
            let deps = compute_expr_dep_summary(inner, arg_bits, cache)?;
            Some(deps.get(*lo as usize..=*hi as usize)?.to_vec())
        }
        OwnedExpr::Concat(high, low) => {
            let mut res = compute_expr_dep_summary(low, arg_bits, cache)?;
            res.extend(compute_expr_dep_summary(high, arg_bits, cache)?);
            Some(res)
        }
        OwnedExpr::Not(inner) | OwnedExpr::Neg(inner) => {
            compute_expr_dep_summary(inner, arg_bits, cache)
        }
        OwnedExpr::And(lhs, rhs) | OwnedExpr::Or(lhs, rhs) | OwnedExpr::Xor(lhs, rhs) => {
            let lhs_deps = compute_expr_dep_summary(lhs, arg_bits, cache)?;
            let rhs_deps = compute_expr_dep_summary(rhs, arg_bits, cache)?;
            union_pointwise_deps(&lhs_deps, &rhs_deps)
        }
        OwnedExpr::Ite(cond, then_expr, else_expr) => {
            let cond_deps = compute_expr_dep_summary(cond, arg_bits, cache)?;
            if cond_deps.len() != 1 {
                return None;
            }
            let then_deps = compute_expr_dep_summary(then_expr, arg_bits, cache)?;
            let else_deps = compute_expr_dep_summary(else_expr, arg_bits, cache)?;
            if then_deps.len() != else_deps.len() {
                return None;
            }
            Some(
                then_deps
                    .into_iter()
                    .zip(else_deps)
                    .map(|(a, b)| a.union(&b).union(&cond_deps[0]))
                    .collect(),
            )
        }
        OwnedExpr::Fop0Dyn(fid) => get_deffun_dep_summary(*fid, 0, cache),
        OwnedExpr::Fop1Dyn(fid, arg) => {
            let f_summary = get_deffun_dep_summary(*fid, 1, cache)?;
            let arg_summary = compute_expr_dep_summary(arg, arg_bits, cache)?;
            compose_dep_summaries(&f_summary, &[arg_summary], arg_bits.len())
        }
        OwnedExpr::Fop2Dyn(fid, lhs, rhs) => {
            let f_summary = get_deffun_dep_summary(*fid, 2, cache)?;
            let lhs_summary = compute_expr_dep_summary(lhs, arg_bits, cache)?;
            let rhs_summary = compute_expr_dep_summary(rhs, arg_bits, cache)?;
            compose_dep_summaries(&f_summary, &[lhs_summary, rhs_summary], arg_bits.len())
        }
        OwnedExpr::FopDyn(fid, args) => {
            let f_summary = get_deffun_dep_summary(*fid, args.len(), cache)?;
            let arg_summaries = args
                .iter()
                .map(|arg| compute_expr_dep_summary(arg, arg_bits, cache))
                .collect::<Option<Vec<_>>>()?;
            compose_dep_summaries(&f_summary, &arg_summaries, arg_bits.len())
        }
        other => Some(top_dep_summary(owned_expr_width(other), arg_bits)),
    }
}

fn union_pointwise_deps(lhs: &[BitDep], rhs: &[BitDep]) -> Option<Vec<BitDep>> {
    if lhs.len() != rhs.len() {
        return None;
    }
    Some(
        lhs.iter()
            .zip(rhs.iter())
            .map(|(a, b)| a.union(b))
            .collect(),
    )
}

fn compose_dep_summaries(
    outer: &[BitDep],
    inner: &[Vec<BitDep>],
    nargs: usize,
) -> Option<Vec<BitDep>> {
    let mut result = Vec::with_capacity(outer.len());
    for out_dep in outer {
        let mut combined = BitDep::empty(nargs);
        for (arg_idx, bits) in out_dep.per_arg.iter().enumerate() {
            let arg_summary = inner.get(arg_idx)?;
            for bit in bits {
                let bit_dep = arg_summary.get(*bit)?;
                combined = combined.union(bit_dep);
            }
        }
        result.push(combined);
    }
    Some(result)
}

fn top_dep_summary(width: usize, arg_bits: &[usize]) -> Vec<BitDep> {
    let full = BitDep {
        per_arg: arg_bits
            .iter()
            .map(|bits| (0..*bits).collect::<Vec<_>>())
            .collect(),
    };
    (0..width).map(|_| full.clone()).collect()
}
