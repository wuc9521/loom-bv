//! Backward relevance analysis for the exact-nullary search.
//!
//! Given the bit-constraints in a `NullarySpec`, walk the search grammar
//! backward to determine which output bits at each non-terminal are
//! *demanded* by the constraints. Bits we can prove irrelevant get
//! projected out of the seen-map keys, increasing dedup hit rate.
//!
//! Driven to completion eagerly via [`compute_relevant_bits_for_spec`];
//! [`Relevance`] is the underlying worklist engine.

pub mod bits;
pub mod deps;

use std::collections::{BTreeMap, VecDeque};

use crate::{info, parse::deffun};

use super::{Grammar, ExactRule};

use bits::{BitDep, BitSet, WorkItem};
use deps::{
    compute_template_dep_bit, get_deffun_dep_bits, DepCache, TemplateDepCache,
};

pub struct Relevance<'a> {
    grammar: &'a Grammar<'a>,
    nt_bits: Vec<usize>,
    dep_cache: DepCache,
    template_dep_cache: TemplateDepCache,
    relevant: Vec<BitSet>,
    pending: Vec<Vec<BitSet>>,
    queued: Vec<Vec<bool>>,
    worklist: VecDeque<WorkItem>,
    complete: bool,
}

impl<'a> Relevance<'a> {
    pub fn new(
        grammar: &'a Grammar<'a>,
        bits: usize,
        known_bits: &BTreeMap<usize, bool>,
    ) -> Option<Self> {
        if known_bits.is_empty() {
            return None;
        }

        let mut nt_bits: Vec<usize> = grammar
            .nts
            .iter()
            .map(|(_, rules)| nt_output_bits(rules))
            .collect();
        nt_bits[grammar.start] = bits;

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
        let mut start_demand = BitSet::new(bits);
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
        })
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
        reduced_any.then_some(relevant_bits)
    }

    fn process_rule_item(&mut self, _item: WorkItem, demanded: &BitSet, rule: &ExactRule) -> bool {
        match rule {
            ExactRule::Alias(child_nt) => {
                self.propagate_bits(*child_nt, demanded);
                true
            }
            ExactRule::Leaf(_) => true,
            ExactRule::Op { fid, child_nts, .. } => {
                let Some(dep) = get_deffun_dep_bits(*fid, demanded, &mut self.dep_cache) else {
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

pub fn nt_output_bits(rules: &[ExactRule]) -> usize {
    for rule in rules {
        match rule {
            ExactRule::Alias(_) => {}
            ExactRule::Leaf(expr) => return expr.width(),
            ExactRule::Op { fid, .. } => return deffun::ENV.ret_bits(*fid),
            ExactRule::GenericTemplate { template, .. } => return template.output_bits(),
        }
    }
    1
}
