//! Term enumeration + LFP + projection dedup. Mirrors the single-strategy
//! design of the original multisynth solver: walk the operator's grammar
//! smallest-first, compute each candidate's LFP, skip equivalents whose LFP
//! projects to a previously-seen pattern on the start-NT relevant bits, and
//! return the first whose LFP satisfies the label constraints.

use rustc_hash::FxHashSet;
use sygus_parser::ast::{GrammarDef, SyGuSTerm};

use crate::enumerate::expr::OwnedExpr;
use crate::enumerate::value::Value;
use crate::info;
use crate::parse::{self, deffun, new_custom_error_span};

use super::eval::closure_arg_values;
use super::spec::{empty_span, LfpSpec};

pub fn search(
    spec: &LfpSpec,
    env: &deffun::Environ,
    start_relevant: &[usize],
) -> parse::Result<Option<String>> {
    let grammar = spec.grammar_def().ok_or_else(|| {
        new_custom_error_span(
            format!("{}: operator has no grammar", spec.variant_tag()),
            empty_span(),
        )
    })?;
    let max_iters = spec.bits() + 1;
    let enumerator = TermEnumerator::new(grammar);
    // Dedup candidates by their LFP projected to the start-NT relevant bits.
    // Two candidates whose LFPs agree on those bits are indistinguishable
    // for label-satisfaction purposes, so the second (larger) one is skipped.
    let mut seen_lfp: FxHashSet<Vec<u64>> = FxHashSet::default();
    let dedup_enabled = !start_relevant.is_empty();
    let mut candidates_total = 0usize;
    let mut candidates_converged = 0usize;
    let mut candidates_unique = 0usize;
    for size in 1.. {
        for term in enumerator.terms_of_size(size) {
            candidates_total += 1;
            let mut value = Value::from_u64(0, spec.bits());
            let mut converged = false;
            for _ in 0..max_iters {
                let next = term.eval(env, &value, spec.closure_name(), spec.variant_tag())?;
                if next == value {
                    converged = true;
                    break;
                }
                value = next;
            }
            if !converged {
                continue;
            }
            candidates_converged += 1;
            if dedup_enabled {
                let key = value.project_bits(start_relevant);
                if !seen_lfp.insert(key) {
                    continue;
                }
            }
            candidates_unique += 1;
            if spec
                .labels()
                .iter()
                .all(|(bit, expected)| value.bit(*bit) == *expected)
            {
                info!(
                    "{}: found solution at size={}, candidates_total={}, candidates_converged={}, candidates_unique={}",
                    spec.variant_tag(),
                    size,
                    candidates_total,
                    candidates_converged,
                    candidates_unique
                );
                let expr = term.to_owned_expr(spec.variant_tag())?;
                return Ok(Some(spec.finalize(env, expr)?));
            }
        }
    }
    Ok(None)
}

// ---------------------------------------------------------------------------
//  Term enumeration over the operator's grammar
// ---------------------------------------------------------------------------

/// A concrete grammar term: leaf reference or application of a constructor.
#[derive(Clone, Debug)]
enum Term {
    Leaf(String),
    App(String, Vec<Term>),
}

impl Term {
    /// Evaluate this term under `env`, substituting `closure_value` at every
    /// reference of `closure_name`.
    fn eval(
        &self,
        env: &deffun::Environ,
        closure_value: &Value,
        closure_name: &str,
        log_tag: &str,
    ) -> parse::Result<Value> {
        match self {
            Term::Leaf(name) => {
                if name == closure_name {
                    return Ok(closure_value.clone());
                }
                let Some(id) = env.lookup(name, 0) else {
                    return Err(new_custom_error_span(
                        format!("{log_tag}: unknown 0-arity symbol {name}"),
                        empty_span(),
                    ));
                };
                let arg_vals = closure_arg_values(env, id, 0, closure_value, closure_name);
                env.eval_defined(id, 0, &arg_vals).map_err(|_| {
                    new_custom_error_span(format!("{log_tag}: divide-by-zero in {name}"), empty_span())
                })
            }
            Term::App(name, args) => {
                let mut arg_vals = Vec::with_capacity(args.len());
                for a in args {
                    arg_vals.push(a.eval(env, closure_value, closure_name, log_tag)?);
                }
                let Some(id) = env.lookup(name, args.len()) else {
                    return Err(new_custom_error_span(
                        format!("{log_tag}: unknown {}-arity symbol {name}", args.len()),
                        empty_span(),
                    ));
                };
                arg_vals.extend(closure_arg_values(env, id, args.len(), closure_value, closure_name));
                env.eval_defined(id, args.len(), &arg_vals).map_err(|_| {
                    new_custom_error_span(
                        format!("{log_tag}: divide-by-zero in {name}"),
                        empty_span(),
                    )
                })
            }
        }
    }

    /// Convert this term into the OwnedExpr representation used downstream
    /// for formatting and verification.
    fn to_owned_expr(&self, log_tag: &str) -> parse::Result<OwnedExpr> {
        match self {
            Term::Leaf(name) => {
                let fid = deffun::ENV.lookup(name, 0).ok_or_else(|| {
                    new_custom_error_span(format!("{log_tag}: unknown 0-arity symbol {name}"), empty_span())
                })?;
                Ok(OwnedExpr::Fop0Dyn(fid))
            }
            Term::App(name, args) => {
                let child_exprs = args
                    .iter()
                    .map(|a| a.to_owned_expr(log_tag))
                    .collect::<parse::Result<Vec<_>>>()?;
                let fid = deffun::ENV.lookup(name, child_exprs.len()).ok_or_else(|| {
                    new_custom_error_span(
                        format!("{log_tag}: unknown {}-arity symbol {name}", child_exprs.len()),
                        empty_span(),
                    )
                })?;
                Ok(match child_exprs.len() {
                    1 => OwnedExpr::Fop1Dyn(fid, Box::new(child_exprs[0].clone())),
                    2 => OwnedExpr::Fop2Dyn(
                        fid,
                        Box::new(child_exprs[0].clone()),
                        Box::new(child_exprs[1].clone()),
                    ),
                    _ => OwnedExpr::FopDyn(fid, child_exprs),
                })
            }
        }
    }
}

struct TermEnumerator<'a> {
    grammar: &'a GrammarDef,
}

impl<'a> TermEnumerator<'a> {
    fn new(grammar: &'a GrammarDef) -> Self {
        Self { grammar }
    }

    fn start_nt(&self) -> &str {
        &self.grammar.grouped_rule_lists[0].symbol
    }

    fn nt_rules(&self, nt: &str) -> &[sygus_parser::ast::SyGuSGTerm] {
        self.grammar
            .grouped_rule_lists
            .iter()
            .find(|grl| grl.symbol == nt)
            .map(|grl| grl.terms.as_slice())
            .unwrap_or(&[])
    }

    fn terms_of_size(&self, size: usize) -> Vec<Term> {
        let mut cache: std::collections::HashMap<(String, usize), Vec<Term>> =
            std::collections::HashMap::new();
        self.terms_of_nt_size(self.start_nt(), size, &mut cache)
    }

    fn terms_of_nt_size(
        &self,
        nt: &str,
        size: usize,
        cache: &mut std::collections::HashMap<(String, usize), Vec<Term>>,
    ) -> Vec<Term> {
        if size == 0 {
            return Vec::new();
        }
        if let Some(c) = cache.get(&(nt.to_string(), size)) {
            return c.clone();
        }
        let mut out = Vec::new();
        for rule in self.nt_rules(nt) {
            self.extend_from_rule(rule, size, &mut out, cache);
        }
        cache.insert((nt.to_string(), size), out.clone());
        out
    }

    fn extend_from_rule(
        &self,
        rule: &sygus_parser::ast::SyGuSGTerm,
        size: usize,
        out: &mut Vec<Term>,
        cache: &mut std::collections::HashMap<(String, usize), Vec<Term>>,
    ) {
        let term = match rule {
            sygus_parser::ast::SyGuSGTerm::SyGuSTerm(t) => t,
            _ => return,
        };
        match term {
            SyGuSTerm::Identifier(id) => {
                if size != 1 {
                    return;
                }
                let name = id.get_name();
                if self.nt_rules(name.as_ref()).is_empty() {
                    out.push(Term::Leaf(name.to_string()));
                } else {
                    let nested = self.terms_of_nt_size(name.as_ref(), size, cache);
                    out.extend(nested);
                }
            }
            SyGuSTerm::Application(id, args) => {
                if size < 1 + args.len() {
                    return;
                }
                let remaining = size - 1;
                let nts: Vec<String> = args
                    .iter()
                    .filter_map(|a| match a {
                        SyGuSTerm::Identifier(child_id) => Some(child_id.get_name().to_string()),
                        _ => None,
                    })
                    .collect();
                if nts.len() != args.len() {
                    return;
                }
                each_split(remaining, nts.len(), &mut |sizes| {
                    let per_child: Vec<Vec<Term>> = sizes
                        .iter()
                        .zip(nts.iter())
                        .map(|(s, nt)| self.terms_of_nt_size(nt, *s, cache))
                        .collect();
                    if per_child.iter().any(|v| v.is_empty()) {
                        return;
                    }
                    cartesian_product(&per_child, &mut |children| {
                        out.push(Term::App(id.get_name().to_string(), children.to_vec()));
                    });
                });
            }
            _ => {}
        }
    }
}

fn each_split(total: usize, parts: usize, f: &mut impl FnMut(&[usize])) {
    if parts == 0 {
        if total == 0 {
            f(&[]);
        }
        return;
    }
    if parts == 1 {
        if total >= 1 {
            f(&[total]);
        }
        return;
    }
    for first in 1..=total.saturating_sub(parts - 1) {
        each_split_inner(total - first, parts - 1, first, &mut Vec::new(), f);
    }
}

fn each_split_inner(
    remaining: usize,
    parts: usize,
    head: usize,
    acc: &mut Vec<usize>,
    f: &mut impl FnMut(&[usize]),
) {
    acc.push(head);
    if parts == 0 {
        if remaining == 0 {
            f(acc);
        }
    } else if parts == 1 {
        if remaining >= 1 {
            acc.push(remaining);
            f(acc);
            acc.pop();
        }
    } else {
        for next in 1..=remaining.saturating_sub(parts - 1) {
            each_split_inner(remaining - next, parts - 1, next, acc, f);
        }
    }
    acc.pop();
}

fn cartesian_product(slots: &[Vec<Term>], f: &mut impl FnMut(&[Term])) {
    let mut buf: Vec<Term> = Vec::with_capacity(slots.len());
    cartesian_inner(slots, 0, &mut buf, f);
}

fn cartesian_inner(
    slots: &[Vec<Term>],
    idx: usize,
    buf: &mut Vec<Term>,
    f: &mut impl FnMut(&[Term]),
) {
    if idx == slots.len() {
        f(buf);
        return;
    }
    for item in &slots[idx] {
        buf.push(item.clone());
        cartesian_inner(slots, idx + 1, buf, f);
        buf.pop();
    }
}
