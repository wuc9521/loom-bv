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
    grammar::{for_each_candidate_tuple, for_each_size_split, MultiConfig, MultiRule},
};

#[derive(Clone)]
struct Candidate<const N: usize> {
    expr: OwnedExpr,
    value: Bv<N>,
}

pub struct Algo<'a, const N: usize> {
    config: MultiConfig<'static>,
    exprs: Vec<Vec<Vec<Candidate<N>>>>,
    start_map: HashMap<Bv<N>, Option<&'a Expr<'a>>>,
    seen_counts: Vec<usize>,
    seen_non_start: Vec<FxHashMap<Bv<N>, ()>>,
    args: Vec<Bv<N>>,
    bump: &'a Bump,
    counter2: usize,
    current_size: usize,
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
        bump: &'a Bump,
    ) -> parse::Result<Self> {
        let config = MultiConfig::from_problem(problem)?;
        let nt_count = config.nts.len();
        let mut start_map = HashMap::with_capacity_and_hasher(2000000, Default::default());
        start_map.insert(output, None);
        Ok(Self {
            config,
            exprs: vec![vec![Vec::new()]; nt_count],
            start_map,
            seen_counts: vec![0; nt_count],
            seen_non_start: (0..nt_count).map(|_| FxHashMap::default()).collect(),
            args,
            bump,
            counter2: 0,
            current_size: 0,
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
                    }
                }
            }
            for (nt, bucket) in next.into_iter().enumerate() {
                self.exprs[nt].push(bucket);
            }
            self.current_size = size;
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
