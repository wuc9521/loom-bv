use std::{collections::HashMap, mem::size_of};

use rustc_hash::FxHashMap;

use bumpalo::Bump;
use pest::Span;
use sygus_parser::ast::{Identifier, SyGuSGTerm, SyGuSTerm};

use crate::{
    all_ops,
    enumerate::{expr::Expr, Algo as AlgoTrait, Bv},
    parse::{self, deffun, new_custom_error_span, SynthProblem},
    smt_name_of,
};

use super::{algo::dynamic_usage_for_capacity, expr::OwnedExpr};

#[derive(Clone)]
enum TemplateExpr {
    Slot(usize),
    Leaf(OwnedExpr),
    App(Identifier, Vec<TemplateExpr>),
}

impl TemplateExpr {
    fn instantiate(&self, args: &[OwnedExpr]) -> parse::Result<OwnedExpr> {
        match self {
            Self::Slot(i) => Ok(args[*i].clone()),
            Self::Leaf(expr) => Ok(expr.clone()),
            Self::App(id, parts) => {
                let args = parts
                    .iter()
                    .map(|part| part.instantiate(args))
                    .collect::<parse::Result<Vec<_>>>()?;
                build_owned_application(id, &args)
            }
        }
    }
}

#[derive(Clone)]
enum MultiRule {
    Alias(usize),
    Template {
        template: TemplateExpr,
        child_nts: Vec<usize>,
        base_size: usize,
    },
}

struct MultiConfig<'a> {
    nts: Vec<(&'a str, Vec<MultiRule>)>,
    start: usize,
}

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

impl<'a> MultiConfig<'a> {
    fn from_problem(problem: &SynthProblem<'static>) -> parse::Result<MultiConfig<'static>> {
        let nt_lookup = problem
            .cfg
            .iter()
            .enumerate()
            .map(|(idx, nt)| (nt.0, idx))
            .collect::<HashMap<_, _>>();
        let env = problem
            .args
            .iter()
            .map(|name| (*name, 64_u64))
            .collect::<Vec<_>>();
        let mut nts = Vec::with_capacity(problem.cfg.len());
        for nt in problem.cfg.iter() {
            let mut rules = Vec::new();
            for gterm in &nt.1 {
                let term = match gterm {
                    SyGuSGTerm::SyGuSTerm(term) => term,
                    SyGuSGTerm::Constant(_) | SyGuSGTerm::Variable(_) => continue,
                };
                match term_to_rule(term, &nt_lookup, &env)? {
                    Some(rule) => rules.push(rule),
                    None => {}
                }
            }
            nts.push((nt.0, rules));
        }
        Ok(MultiConfig { nts, start: 0 })
    }
}

fn term_to_rule(
    term: &SyGuSTerm,
    nt_lookup: &HashMap<&str, usize>,
    env: &[(&str, u64)],
) -> parse::Result<Option<MultiRule>> {
    fn parse_identifier_atom(
        id: &Identifier,
        env: &[(&str, u64)],
    ) -> parse::Result<Option<OwnedExpr>> {
        let name = id.get_name();
        if env.iter().any(|(arg, _)| *arg == name) {
            Ok(Some(OwnedExpr::from_term(
                &SyGuSTerm::Identifier(id.clone()),
                env,
            )?))
        } else if name.eq_ignore_ascii_case("true")
            || name.eq_ignore_ascii_case("false")
            || name.starts_with('#')
        {
            Ok(Some(OwnedExpr::from_term(
                &SyGuSTerm::Identifier(id.clone()),
                env,
            )?))
        } else if crate::parse::deffun::ENV.lookup(name, 0).is_some() {
            Ok(Some(OwnedExpr::from_term(
                &SyGuSTerm::Identifier(id.clone()),
                env,
            )?))
        } else {
            Ok(None)
        }
    }

    match term {
        SyGuSTerm::Identifier(id) => {
            if let Some(child_nt) = nt_lookup.get(id.get_name()).copied() {
                Ok(Some(MultiRule::Alias(child_nt)))
            } else if let Some(atom) = parse_identifier_atom(id, env)? {
                Ok(Some(MultiRule::Template {
                    template: TemplateExpr::Leaf(atom),
                    child_nts: Vec::new(),
                    base_size: 1,
                }))
            } else {
                Err(new_custom_error_span(
                    format!("Enumeration: unsupported grammar symbol {}", id),
                    Span::new("", 0, 0).unwrap(),
                ))
            }
        }
        SyGuSTerm::Literal(lit) => {
            let atom = OwnedExpr::from_term(&SyGuSTerm::Literal(lit.clone()), env)?;
            Ok(Some(MultiRule::Template {
                template: TemplateExpr::Leaf(atom),
                child_nts: Vec::new(),
                base_size: 1,
            }))
        }
        SyGuSTerm::Application(_, _) | SyGuSTerm::Annotated(_, _) => {
            let (template, child_nts, base_size) = template_from_term(term, nt_lookup, env)?;
            Ok(Some(MultiRule::Template {
                template,
                child_nts,
                base_size,
            }))
        }
        _ => Err(new_custom_error_span(
            format!("Enumeration: unsupported grammar term {}", term),
            Span::new("", 0, 0).unwrap(),
        )),
    }
}

fn template_from_term(
    term: &SyGuSTerm,
    nt_lookup: &HashMap<&str, usize>,
    env: &[(&str, u64)],
) -> parse::Result<(TemplateExpr, Vec<usize>, usize)> {
    match term {
        SyGuSTerm::Identifier(id) => {
            if let Some(child_nt) = nt_lookup.get(id.get_name()).copied() {
                Ok((TemplateExpr::Slot(0), vec![child_nt], 0))
            } else {
                Ok((
                    TemplateExpr::Leaf(OwnedExpr::from_term(term, env)?),
                    Vec::new(),
                    1,
                ))
            }
        }
        SyGuSTerm::Literal(_) => Ok((
            TemplateExpr::Leaf(OwnedExpr::from_term(term, env)?),
            Vec::new(),
            1,
        )),
        SyGuSTerm::Annotated(inner, _) => template_from_term(inner, nt_lookup, env),
        SyGuSTerm::Application(id, args) => {
            let mut child_nts = Vec::new();
            let mut base_size = 1;
            let mut rendered_args = Vec::with_capacity(args.len());
            for arg in args {
                let (template, mut nts, size) = template_from_term(arg, nt_lookup, env)?;
                let offset = child_nts.len();
                rendered_args.push(shift_slots(template, offset));
                child_nts.append(&mut nts);
                base_size += size;
            }
            Ok((
                TemplateExpr::App(id.clone(), rendered_args),
                child_nts,
                base_size,
            ))
        }
        _ => Err(new_custom_error_span(
            format!("Enumeration: unsupported grammar term {}", term),
            Span::new("", 0, 0).unwrap(),
        )),
    }
}

fn shift_slots(expr: TemplateExpr, offset: usize) -> TemplateExpr {
    match expr {
        TemplateExpr::Slot(i) => TemplateExpr::Slot(i + offset),
        TemplateExpr::Leaf(expr) => TemplateExpr::Leaf(expr),
        TemplateExpr::App(id, args) => TemplateExpr::App(
            id,
            args.into_iter()
                .map(|arg| shift_slots(arg, offset))
                .collect(),
        ),
    }
}

fn build_owned_application(id: &Identifier, args: &[OwnedExpr]) -> parse::Result<OwnedExpr> {
    fn empty_span() -> Span<'static> {
        Span::new("", 0, 0).expect("empty span should be valid")
    }

    fn index_numeral(idx: &sygus_parser::ast::Index) -> Option<u64> {
        match idx {
            sygus_parser::ast::Index::Numeral(v) => Some(*v as u64),
            sygus_parser::ast::Index::Symbol(_) => None,
        }
    }

    fn extract_indices(id: &Identifier) -> Option<(u64, u64)> {
        match id {
            Identifier::Indexed(sym, idxs) if sym == "_" && idxs.len() >= 3 => {
                match (&idxs[0], index_numeral(&idxs[1]), index_numeral(&idxs[2])) {
                    (sygus_parser::ast::Index::Symbol(op), Some(hi), Some(lo))
                        if op == "extract" && hi >= lo =>
                    {
                        Some((hi, lo))
                    }
                    _ => None,
                }
            }
            Identifier::Indexed(sym, idxs) if sym == "extract" && idxs.len() >= 2 => {
                match (index_numeral(&idxs[0]), index_numeral(&idxs[1])) {
                    (Some(hi), Some(lo)) if hi >= lo => Some((hi, lo)),
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
                ["_", "extract", hi, lo] => match (hi.parse::<u64>(), lo.parse::<u64>()) {
                    (Ok(hi), Ok(lo)) if hi >= lo => Some((hi, lo)),
                    _ => None,
                },
                _ => None,
            }
        })
    }

    let opname = id.get_name();
    if args.len() == 1 {
        if let Some((hi, lo)) = extract_indices(id) {
            return Ok(OwnedExpr::Extract(Box::new(args[0].clone()), hi, lo));
        }
    }
    if opname == "concat" && args.len() >= 2 {
        let mut acc = args.last().unwrap().clone();
        for arg in args[..args.len() - 1].iter().rev() {
            acc = OwnedExpr::Concat(Box::new(arg.clone()), Box::new(acc));
        }
        return Ok(acc);
    }
    macro_rules! operator1 {
        ($opn:expr, $n:ident) => {
            if opname == $opn && args.len() == 1 {
                return Ok(OwnedExpr::$n(Box::new(args[0].clone())));
            }
        };
    }
    macro_rules! operator2 {
        ($opn:expr, $n:ident) => {
            if opname == $opn && args.len() == 2 {
                return Ok(OwnedExpr::$n(
                    Box::new(args[0].clone()),
                    Box::new(args[1].clone()),
                ));
            }
        };
    }
    macro_rules! foreach_op {
        (1, $op:ident) => {
            operator1!(smt_name_of![$op], $op);
        };
        (2, $op:ident) => {
            operator2!(smt_name_of![$op], $op);
        };
    }
    all_ops!(arity);
    operator1!("not", Not);
    if opname == "and" && args.len() >= 2 {
        let mut it = args.iter();
        let mut acc = it.next().unwrap().clone();
        for a in it {
            acc = OwnedExpr::Or(Box::new(acc), Box::new(a.clone()));
        }
        return Ok(acc);
    }
    if opname == "or" && args.len() >= 2 {
        let mut it = args.iter();
        let mut acc = it.next().unwrap().clone();
        for a in it {
            acc = OwnedExpr::And(Box::new(acc), Box::new(a.clone()));
        }
        return Ok(acc);
    }
    if opname == "xor" && args.len() >= 2 {
        let mut it = args.iter();
        let mut acc = it.next().unwrap().clone();
        for a in it {
            acc = OwnedExpr::Xor(Box::new(acc), Box::new(a.clone()));
        }
        return Ok(acc);
    }
    operator2!("=", Xor);
    if opname == "ite" && args.len() == 3 {
        return Ok(OwnedExpr::Ite(
            Box::new(args[0].clone()),
            Box::new(args[1].clone()),
            Box::new(args[2].clone()),
        ));
    }
    if args.len() == 1 {
        if let Some(fid) = deffun::ENV.lookup(opname, 1) {
            return Ok(OwnedExpr::Fop1Dyn(fid, Box::new(args[0].clone())));
        }
    }
    if args.len() == 2 {
        if let Some(fid) = deffun::ENV.lookup(opname, 2) {
            return Ok(OwnedExpr::Fop2Dyn(
                fid,
                Box::new(args[0].clone()),
                Box::new(args[1].clone()),
            ));
        }
    }
    if let Some(fid) = deffun::ENV.lookup(opname, args.len()) {
        return Ok(OwnedExpr::FopDyn(fid, args.to_vec()));
    }
    Err(new_custom_error_span(
        format!("Unrecongnized Expression: ({} ...)", opname),
        empty_span(),
    ))
}

fn for_each_size_split(
    total: usize,
    arity: usize,
    sizes: &mut Vec<usize>,
    f: &mut impl FnMut(&[usize]),
) {
    if arity == 0 {
        if total == 0 {
            f(sizes);
        }
        return;
    }
    if arity == 1 {
        sizes.push(total);
        f(sizes);
        sizes.pop();
        return;
    }
    let min_rest = arity - 1;
    for first in 1..=(total - min_rest) {
        sizes.push(first);
        for_each_size_split(total - first, arity - 1, sizes, f);
        sizes.pop();
    }
}

fn for_each_candidate_tuple<'a, const N: usize>(
    candidate_pools: &[&'a [Candidate<N>]],
    tuple: &mut Vec<&'a Candidate<N>>,
    f: &mut impl FnMut(&[&'a Candidate<N>]),
) {
    if tuple.len() == candidate_pools.len() {
        f(tuple);
        return;
    }
    let idx = tuple.len();
    for candidate in candidate_pools[idx] {
        tuple.push(candidate);
        for_each_candidate_tuple(candidate_pools, tuple, f);
        tuple.pop();
    }
}
