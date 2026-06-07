use std::{collections::HashMap, mem::size_of};

use rustc_hash::FxHashMap;

use bumpalo::Bump;

use crate::{
    enumerate::{expr::Expr, Algo as AlgoTrait, Bv},
    parse::{self, SynthProblem},
};

use super::{
    algo::dynamic_usage_for_capacity,
    expr::OwnedExpr,
    grammar::{
        for_each_candidate_tuple, for_each_size_split, MultiConfig, MultiRule, TemplateExpr,
    },
};

#[derive(Clone)]
struct Candidate<const N: usize> {
    expr: OwnedExpr,
    value: Bv<N>,
}

#[derive(Clone, Copy)]
struct AbsSummary<const N: usize> {
    may_one: Bv<N>,
    may_zero: Bv<N>,
}

impl<const N: usize> AbsSummary<N> {
    fn top() -> Self {
        Self {
            may_one: Bv::ONES,
            may_zero: Bv::ONES,
        }
    }

    fn exact(value: Bv<N>) -> Self {
        Self {
            may_one: value,
            may_zero: !value,
        }
    }

    fn union(self, rhs: Self) -> Self {
        Self {
            may_one: self.may_one | rhs.may_one,
            may_zero: self.may_zero | rhs.may_zero,
        }
    }

    fn may_match_target(&self, target: Bv<N>) -> bool {
        (self.may_one & target) == target && (self.may_zero & !target) == !target
    }
}

pub struct Algo<'a, const N: usize> {
    config: MultiConfig<'static>,
    exprs: Vec<Vec<Vec<Candidate<N>>>>,
    start_map: HashMap<Bv<N>, Option<&'a Expr<'a>>>,
    seen_counts: Vec<usize>,
    seen_non_start: Vec<FxHashMap<Bv<N>, ()>>,
    bucket_abs: Vec<Vec<Option<AbsSummary<N>>>>,
    args: Vec<Bv<N>>,
    arg_abs: Vec<AbsSummary<N>>,
    target: Bv<N>,
    bump: &'a Bump,
    counter2: usize,
    current_size: usize,
    /// Reserved for the upcoming sub-expression-reuse port from `algo::Algo`.
    /// Currently unused; setting it has no effect.
    #[allow(dead_code)]
    dag_size: bool,
}

impl<'a, const N: usize> AlgoTrait<'a, N> for Algo<'a, N> {
    fn len(&self) -> usize {
        self.exprs
            .iter()
            .flat_map(|nt| nt.iter())
            .map(|bucket| bucket.len())
            .sum()
    }

    fn count(&self) -> usize {
        self.start_map.len() + self.seen_counts.iter().sum::<usize>()
    }

    fn count2(&self) -> usize {
        self.counter2
    }

    fn size(&self) -> usize {
        self.current_size
    }

    fn map_size(&self) -> usize {
        dynamic_usage_for_capacity::<Bv<N>, Option<&'a Expr<'a>>>(self.start_map.capacity())
            + self
                .seen_non_start
                .iter()
                .map(|map| dynamic_usage_for_capacity::<Bv<N>, ()>(map.capacity()))
                .sum::<usize>()
    }

    fn expr_size(&self) -> usize {
        self.len() * size_of::<Candidate<N>>()
    }

    fn map(&self) -> &HashMap<Bv<N>, Option<&'a Expr<'a>>> {
        &self.start_map
    }
}

impl<'a, const N: usize> Algo<'a, N> {
    pub fn new(
        problem: &SynthProblem<'static>,
        args: Vec<Bv<N>>,
        output: Bv<N>,
        dag_size: bool,
        bump: &'a Bump,
    ) -> parse::Result<Self> {
        let config = MultiConfig::from_problem(problem)?;
        let nt_count = config.nts.len();
        let mut start_map = HashMap::with_capacity_and_hasher(2000000, Default::default());
        start_map.insert(output, None);
        let arg_abs = args
            .iter()
            .copied()
            .map(AbsSummary::exact)
            .collect::<Vec<_>>();
        Ok(Self {
            config,
            exprs: vec![vec![Vec::new()]; nt_count],
            start_map,
            seen_counts: vec![0; nt_count],
            seen_non_start: (0..nt_count).map(|_| FxHashMap::default()).collect(),
            bucket_abs: vec![vec![None]; nt_count],
            args,
            arg_abs,
            target: output,
            bump,
            counter2: 0,
            current_size: 0,
            dag_size,
        })
    }

    pub fn run_until(
        &mut self,
        mut f: impl FnMut(&Self, &'a Expr<'a>, Bv<N>) -> Result<(), ()>,
    ) -> Result<(), ()> {
        loop {
            let size = self.current_size + 1;
            let mut next = vec![Vec::new(); self.config.nts.len()];
            for nt in 0..self.config.nts.len() {
                let rules = self.config.nts[nt].1.clone();
                for rule in rules {
                    match rule {
                        MultiRule::Alias(child_nt) => {
                            if size < self.exprs[child_nt].len() {
                                let staged = self.exprs[child_nt][size].clone();
                                for child in staged {
                                    self.insert_candidate(
                                        nt,
                                        child.expr,
                                        child.value,
                                        &mut next[nt],
                                        &mut f,
                                    )?;
                                }
                            }
                        }
                        MultiRule::Template {
                            template,
                            child_nts,
                            base_size,
                            class: _class,
                        } => {
                            if base_size > size {
                                continue;
                            }
                            let child_total = size - base_size;
                            if child_nts.is_empty() {
                                if child_total == 0 {
                                    let expr = match template.instantiate(&[]) {
                                        Ok(expr) => expr,
                                        Err(_) => continue,
                                    };
                                    let value = expr.eval_bv(&self.args);
                                    self.insert_candidate(nt, expr, value, &mut next[nt], &mut f)?;
                                }
                                continue;
                            }
                            if child_total < child_nts.len() {
                                continue;
                            }
                            let mut staged = Vec::new();
                            let mut splits = Vec::with_capacity(child_nts.len());
                            for_each_size_split(
                                child_total,
                                child_nts.len(),
                                &mut splits,
                                &mut |sizes| {
                                    let pools = child_nts
                                        .iter()
                                        .zip(sizes.iter())
                                        .map(|(child_nt, child_size)| {
                                            self.exprs[*child_nt]
                                                .get(*child_size)
                                                .map(Vec::as_slice)
                                                .unwrap_or(&[][..])
                                        })
                                        .collect::<Vec<_>>();
                                    if pools.iter().any(|pool| pool.is_empty()) {
                                        return;
                                    }
                                    let child_abs = child_nts
                                        .iter()
                                        .zip(sizes.iter())
                                        .map(|(child_nt, child_size)| {
                                            self.bucket_abs[*child_nt]
                                                .get(*child_size)
                                                .and_then(|v| *v)
                                        })
                                        .collect::<Option<Vec<_>>>();
                                    let Some(child_abs) = child_abs else {
                                        return;
                                    };
                                    if let Some(approx) =
                                        self.eval_template_abs(&template, &child_abs)
                                    {
                                        if !approx.may_match_target(self.target) {
                                            return;
                                        }
                                    }
                                    let mut tuple = Vec::with_capacity(child_nts.len());
                                    for_each_candidate_tuple(&pools, &mut tuple, &mut |tuple| {
                                        let child_exprs = tuple
                                            .iter()
                                            .map(|cand| cand.expr.clone())
                                            .collect::<Vec<_>>();
                                        let expr = match template.instantiate(&child_exprs) {
                                            Ok(expr) => expr,
                                            Err(_) => return,
                                        };
                                        let value = expr.eval_bv(&self.args);
                                        staged.push((expr, value));
                                    });
                                },
                            );
                            for (expr, value) in staged {
                                self.insert_candidate(nt, expr, value, &mut next[nt], &mut f)?;
                            }
                        }
                        MultiRule::ChatGPT { expr, size: target_size } => {
                            if size == target_size {
                                let value = expr.eval_bv(&self.args);
                                self.insert_candidate(
                                    nt,
                                    expr.clone(),
                                    value,
                                    &mut next[nt],
                                    &mut f,
                                )?;
                            }
                        }
                    }
                }
            }
            for (nt, bucket) in next.into_iter().enumerate() {
                let abs = bucket
                    .iter()
                    .map(|cand| AbsSummary::exact(cand.value))
                    .reduce(AbsSummary::union);
                self.exprs[nt].push(bucket);
                self.bucket_abs[nt].push(abs);
            }
            self.current_size = size;
        }
    }

    fn eval_template_abs(
        &self,
        template: &TemplateExpr,
        slot_args: &[AbsSummary<N>],
    ) -> Option<AbsSummary<N>> {
        match template {
            TemplateExpr::Slot(i) => slot_args.get(*i).copied(),
            TemplateExpr::Leaf(expr) => self.eval_owned_abs(expr, &self.arg_abs, 0),
            TemplateExpr::App(id, parts) => {
                let mut args = Vec::with_capacity(parts.len());
                for part in parts {
                    args.push(self.eval_template_abs(part, slot_args)?);
                }
                Some(self.apply_op_abs(id.get_name(), &args))
            }
        }
    }

    fn eval_owned_abs(
        &self,
        expr: &OwnedExpr,
        vars: &[AbsSummary<N>],
        depth: usize,
    ) -> Option<AbsSummary<N>> {
        if depth > 64 {
            return Some(AbsSummary::top());
        }
        Some(match expr {
            OwnedExpr::Var(i, _) => vars.get(*i).copied().unwrap_or_else(AbsSummary::top),
            OwnedExpr::Const(v) => AbsSummary::exact(Bv([v.as_u64_lossy(); N].into())),
            OwnedExpr::Let(_, _, _) => {
                let mut scoped = vars.to_vec();
                let mut current = expr;
                loop {
                    match current {
                        OwnedExpr::Let(_, value, body) => {
                            let bound = self.eval_owned_abs(value, &scoped, depth + 1)?;
                            scoped.push(bound);
                            current = body;
                        }
                        other => break self.eval_owned_abs(other, &scoped, depth + 1)?,
                    }
                }
            }
            OwnedExpr::Not(a) => {
                let a = self.eval_owned_abs(a, vars, depth + 1)?;
                AbsSummary {
                    may_one: a.may_zero,
                    may_zero: a.may_one,
                }
            }
            OwnedExpr::And(a, b) => {
                let a = self.eval_owned_abs(a, vars, depth + 1)?;
                let b = self.eval_owned_abs(b, vars, depth + 1)?;
                AbsSummary {
                    may_one: a.may_one & b.may_one,
                    may_zero: a.may_zero | b.may_zero,
                }
            }
            OwnedExpr::Or(a, b) => {
                let a = self.eval_owned_abs(a, vars, depth + 1)?;
                let b = self.eval_owned_abs(b, vars, depth + 1)?;
                AbsSummary {
                    may_one: a.may_one | b.may_one,
                    may_zero: a.may_zero & b.may_zero,
                }
            }
            OwnedExpr::Xor(a, b) => {
                let a = self.eval_owned_abs(a, vars, depth + 1)?;
                let b = self.eval_owned_abs(b, vars, depth + 1)?;
                AbsSummary {
                    may_one: (a.may_one & b.may_zero) | (a.may_zero & b.may_one),
                    may_zero: (a.may_one & b.may_one) | (a.may_zero & b.may_zero),
                }
            }
            OwnedExpr::Concat(a, b) => {
                let rhs_bits = b.bit_width();
                let a = self.eval_owned_abs(a, vars, depth + 1)?;
                let b = self.eval_owned_abs(b, vars, depth + 1)?;
                AbsSummary {
                    may_one: a.may_one.concat_low(b.may_one, rhs_bits),
                    may_zero: a.may_zero.concat_low(b.may_zero, rhs_bits),
                }
            }
            OwnedExpr::Extract(a, hi, lo) => {
                let a = self.eval_owned_abs(a, vars, depth + 1)?;
                AbsSummary {
                    may_one: a.may_one.extract(*hi, *lo),
                    may_zero: a.may_zero.extract(*hi, *lo),
                }
            }
            OwnedExpr::Ite(_, b, c) => {
                let b = self.eval_owned_abs(b, vars, depth + 1)?;
                let c = self.eval_owned_abs(c, vars, depth + 1)?;
                b.union(c)
            }
            OwnedExpr::Fop0Dyn(fid) => {
                let body = crate::parse::deffun::ENV.apply(*fid);
                self.eval_owned_abs(body, &[], depth + 1)?
            }
            OwnedExpr::Fop1Dyn(fid, a) => {
                let arg = self.eval_owned_abs(a, vars, depth + 1)?;
                let body = crate::parse::deffun::ENV.apply(*fid);
                self.eval_owned_abs(body, &[arg], depth + 1)?
            }
            OwnedExpr::Fop2Dyn(fid, a, b) => {
                let a = self.eval_owned_abs(a, vars, depth + 1)?;
                let b = self.eval_owned_abs(b, vars, depth + 1)?;
                let body = crate::parse::deffun::ENV.apply(*fid);
                self.eval_owned_abs(body, &[a, b], depth + 1)?
            }
            OwnedExpr::FopDyn(fid, args) => {
                let mut abs_args = Vec::with_capacity(args.len());
                for arg in args {
                    abs_args.push(self.eval_owned_abs(arg, vars, depth + 1)?);
                }
                let body = crate::parse::deffun::ENV.apply(*fid);
                self.eval_owned_abs(body, &abs_args, depth + 1)?
            }
            _ => AbsSummary::top(),
        })
    }

    fn apply_op_abs(&self, op: &str, args: &[AbsSummary<N>]) -> AbsSummary<N> {
        match (op, args) {
            ("not", [a]) | ("bvnot", [a]) => AbsSummary {
                may_one: a.may_zero,
                may_zero: a.may_one,
            },
            ("and", [a, b]) | ("bvand", [a, b]) => AbsSummary {
                may_one: a.may_one & b.may_one,
                may_zero: a.may_zero | b.may_zero,
            },
            ("or", [a, b]) | ("bvor", [a, b]) => AbsSummary {
                may_one: a.may_one | b.may_one,
                may_zero: a.may_zero & b.may_zero,
            },
            ("xor", [a, b]) | ("bvxor", [a, b]) | ("=", [a, b]) => AbsSummary {
                may_one: (a.may_one & b.may_zero) | (a.may_zero & b.may_one),
                may_zero: (a.may_one & b.may_one) | (a.may_zero & b.may_zero),
            },
            ("concat", [a, b]) => AbsSummary {
                may_one: a.may_one.concat_low(b.may_one, 64),
                may_zero: a.may_zero.concat_low(b.may_zero, 64),
            },
            _ => {
                if let Some(fid) = crate::parse::deffun::ENV.lookup(op, args.len()) {
                    let body = crate::parse::deffun::ENV.apply(fid);
                    self.eval_owned_abs(body, args, 0)
                        .unwrap_or_else(AbsSummary::top)
                } else {
                    AbsSummary::top()
                }
            }
        }
    }

    fn insert_candidate(
        &mut self,
        nt: usize,
        expr: OwnedExpr,
        value: Bv<N>,
        bucket: &mut Vec<Candidate<N>>,
        f: &mut impl FnMut(&Self, &'a Expr<'a>, Bv<N>) -> Result<(), ()>,
    ) -> Result<(), ()> {
        self.counter2 += 1;
        if nt == self.config.start {
            match self.start_map.entry(value) {
                std::collections::hash_map::Entry::Vacant(entry) => {
                    let expr_ref = Expr::from_owned(self.bump, &expr);
                    entry.insert(Some(expr_ref));
                    f(self, expr_ref, value)?;
                    bucket.push(Candidate { expr, value });
                }
                std::collections::hash_map::Entry::Occupied(entry) => {
                    if entry.get().is_none() {
                        let expr_ref = Expr::from_owned(self.bump, &expr);
                        f(self, expr_ref, value)?;
                    }
                }
            }
        } else if self.seen_non_start[nt].insert(value, ()).is_none() {
            self.seen_counts[nt] += 1;
            bucket.push(Candidate { expr, value });
        }
        Ok(())
    }
}

impl OwnedExpr {
    fn bit_width(&self) -> usize {
    match self {
        OwnedExpr::Concat(a, b) => a.bit_width() + b.bit_width(),
        OwnedExpr::Extract(_, hi, lo) => (*hi - *lo + 1) as usize,
        OwnedExpr::Fop0Dyn(id) => crate::parse::deffun::ENV.ret_bits(*id),
        OwnedExpr::FopDyn(id, ..) => crate::parse::deffun::ENV.ret_bits(*id),
        OwnedExpr::Const(v) => v.bits(),
        OwnedExpr::Var(_, width) => *width,
        OwnedExpr::Let(_, _, body) => body.bit_width(),
        OwnedExpr::Not(a) | OwnedExpr::Neg(a) | OwnedExpr::Fop1Dyn(_, a) => a.bit_width(),
        OwnedExpr::Add(a, _)
        | OwnedExpr::Xor(a, _)
        | OwnedExpr::And(a, _)
        | OwnedExpr::Or(a, _)
        | OwnedExpr::Mul(a, _)
        | OwnedExpr::Sub(a, _)
        | OwnedExpr::Fop2Dyn(_, a, _)
        | OwnedExpr::LShr(a, _)
        | OwnedExpr::AShr(a, _)
        | OwnedExpr::Shl(a, _)
        | OwnedExpr::UDiv(a, _)
        | OwnedExpr::URem(a, _)
        | OwnedExpr::SDiv(a, _)
        | OwnedExpr::SRem(a, _) => a.bit_width(),
        OwnedExpr::Ite(_, a, _) => a.bit_width(),
    }
    }
}
// (extract / concat helpers were duplicated here; see `Bv::extract` and
// `Bv::concat_low` in `enumerate/mod.rs`.)
