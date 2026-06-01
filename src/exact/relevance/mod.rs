//! Backward relevance analysis for the exact-nullary search.
//!
//! Given the bit-constraints in a `NullarySpec`, walk the search grammar
//! backward to determine which output bits at each non-terminal are
//! *demanded* by the constraints. Bits no can prove irrelevant get
//! projected out of the seen-map keys, increasing dedup hit rate.
//!
//! Two driving modes:
//! * eager: run to completion up front via [`compute_relevant_bits_for_spec`].
//! * lazy: drive incrementally via [`LazyRelevance::advance`] interleaved
//!   with search; used by `--mitm`.

mod bits;
mod deps;

use std::collections::VecDeque;

use crate::{enumerate::expr::OwnedExpr, info, parse::deffun};

use super::{ExactGrammar, ExactRule, NullarySpec};

use bits::{BitDep, BitSet, WorkItem};
use deps::{
    compute_template_dep_bit, get_deffun_dep_bits, DepCache, TemplateDepCache,
};

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
                rules
                    .iter()
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
                self.propagate_closure_deps(*fid, 1, &dep);
                true
            }
            ExactRule::Binary { fid, lhs_nt, rhs_nt } => {
                let Some(dep) = get_deffun_dep_bits(*fid, 2, demanded, &mut self.dep_cache)
                else {
                    return false;
                };
                self.propagate_dep(&dep, 0, *lhs_nt);
                self.propagate_dep(&dep, 1, *rhs_nt);
                self.propagate_closure_deps(*fid, 2, &dep);
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
                self.propagate_closure_deps(*fid, child_nts.len(), &dep);
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

    /// `dep.per_arg` was computed with extended arg_bits (user args followed
    /// by closure-synth-fun arg slots). The user-arg slots are already
    /// consumed by `propagate_dep`; the trailing closure-arg slots feed the
    /// `closure_relevant` set and, by the closure constraint `g = aux`,
    /// re-trigger demand on the start NT.
    fn propagate_closure_deps(&mut self, fid: usize, nargs: usize, dep: &BitDep) {
        if self.closure_param.is_none() {
            return;
        }
        let closure_arg_bits = deffun::ENV.closure_arg_bits(fid, nargs);
        if closure_arg_bits.is_empty() {
            return;
        }
        let start = self.grammar.start;
        for offset in 0..closure_arg_bits.len() {
            let Some(bits) = dep.per_arg.get(nargs + offset) else {
                continue;
            };
            if bits.is_empty() {
                continue;
            }
            // Clone the BitSet so we can mutate self.closure_relevant and
            // self.relevant independently.
            let bits = bits.clone();
            if let Some(cr) = self.closure_relevant.as_mut() {
                cr.union_inplace(&bits);
            }
            self.propagate_bits(start, &bits);
        }
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
