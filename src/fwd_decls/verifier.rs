//! Verifier impl for [`FwdDeclsProblem`].

use std::collections::BTreeMap;

use crate::enumerate::expr::OwnedExpr;
use crate::enumerate::value::BitVec;
use crate::exact::bitspec::Example;
use crate::exact::relevance::{deps::get_deffun_dep_bit, Relevance};
use crate::exact::types::{ExactRule, Grammar};
use crate::exact::verifier::Verifier;
use crate::fwd_decls::problem::{FwdDeclsProblem, LfpRecipe};
use crate::parse::deffun;

impl Verifier for FwdDeclsProblem {
    fn num_examples(&self) -> usize {
        // Structural-only: no PBE examples.
        0
    }

    fn output_bits(&self) -> usize {
        self.entry_bits
    }

    fn example_args(&self, _i: usize) -> &[BitVec] {
        // Never called when num_examples() == 0.
        &[]
    }

    fn compute_relevant_bits(&self, grammar: &Grammar<'_>) -> Option<Vec<Vec<usize>>> {
        // Demand closure: alternates between grammar-side propagation
        // (`Relevance`) and synth-fun-side propagation (aux feedback
        // through the propagation define-fun). Iterates until the
        // demand on the entry-point synth-fun stabilises — bounded by
        // `entry_bits` since each round can only add bits.
        let mut demand_on_entry: BTreeMap<usize, bool> =
            extract_initial_demand(&self.bit_asserts, self.entry_synth_idx);
        if demand_on_entry.is_empty() {
            return None;
        }
        // Map each aux to the NT in this grammar that has it as a Leaf
        // (looked up by sort matching the aux's output sort width).
        let aux_nt: Vec<(usize, &LfpRecipe)> = self
            .recipes
            .iter()
            .filter_map(|r| find_leaf_nt(grammar, r.aux_synth_idx).map(|nt| (nt, r)))
            .collect();
        // Cap iterations at entry_bits + 1 (each round must add at
        // least one bit to demand_on_entry, else we've converged).
        for _ in 0..=self.entry_bits {
            let Some(mut rel) = Relevance::new(grammar, self.entry_bits, &demand_on_entry)
            else {
                return None;
            };
            while !rel.advance(1024) {}
            let relevant = rel.finish().unwrap_or_else(|| {
                (0..grammar.nts.len())
                    .map(|i| (0..nt_output_bits(grammar, i)).collect())
                    .collect()
            });
            // Add aux feedback to demand_on_entry.
            let before = demand_on_entry.len();
            for (nt, recipe) in &aux_nt {
                for &s in &relevant[*nt] {
                    let mut cache = Default::default();
                    let Some(bit_dep) = get_deffun_dep_bit(
                        recipe.propagation_fid,
                        s,
                        &mut cache,
                    ) else {
                        continue;
                    };
                    if let Some(entry_bits) = bit_dep.per_arg.first() {
                        for b in entry_bits.iter_ones() {
                            demand_on_entry.entry(b).or_insert(true);
                        }
                    }
                }
            }
            if demand_on_entry.len() == before {
                // Stable — return the relevant bits computed in this round.
                return Some(relevant);
            }
        }
        // Shouldn't reach here given the iteration bound, but be safe:
        // re-run one last time with the final demand.
        let mut rel = Relevance::new(grammar, self.entry_bits, &demand_on_entry)?;
        while !rel.advance(1024) {}
        rel.finish()
    }

    fn pbe_examples(&self) -> Option<&[Example]> {
        // try_compose requires PBE shape we don't have.
        None
    }

    fn verify(
        &self,
        _values: &[BitVec],
        materialize: &mut dyn FnMut() -> Option<OwnedExpr>,
    ) -> bool {
        let Some(candidate) = materialize() else {
            return false;
        };
        // Install the entry-point candidate so `SynthApp(entry_idx, _)`
        // references inside `bit_asserts` resolve via `CURRENT_CANDIDATES`.
        deffun::set_candidate(self.entry_synth_idx, Some(candidate.clone()));
        // 1. Seed each auxiliary with its baseline.
        for r in &self.recipes {
            deffun::set_candidate(
                r.aux_synth_idx,
                Some(OwnedExpr::Const(r.baseline.clone())),
            );
        }

        // 2. Iterate to fixpoint. The lattice is finite (per-bit BV at
        //    the auxiliary's sort width), so convergence happens in at
        //    most `sum of aux widths` rounds. We cap conservatively at
        //    `entry_bits * recipes.len() + 1` which is a generous safe
        //    bound for any monotone operator on this lattice.
        let cap = self.entry_bits * self.recipes.len().max(1) + 1;
        for _round in 0..cap {
            // Evaluate the candidate; this propagates the current
            // auxiliary values through the constructor define-funs.
            let g_value = match candidate.eval(&[]) {
                Ok(v) => v,
                Err(_) => return false,
            };
            let mut changed = false;
            for r in &self.recipes {
                let prop = match deffun::ENV.eval_defined(
                    r.propagation_fid,
                    &[g_value.clone()],
                    &[],
                ) {
                    Ok(v) => v,
                    Err(_) => return false,
                };
                let next = bvor(&r.baseline, &prop);
                let current = current_aux_value(r);
                if next != current {
                    deffun::set_candidate(
                        r.aux_synth_idx,
                        Some(OwnedExpr::Const(next)),
                    );
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }

        // 3. Evaluate the remaining bit asserts against the now-LFP'd
        //    auxiliaries (their `SynthApp` lookups in the structural
        //    exprs will hit the values just written via `set_candidate`).
        self.bit_asserts.iter().all(|expr| {
            expr.eval(&[])
                .map(|v| v.as_bool().holds())
                .unwrap_or(false)
        })
    }
}

fn bvor(a: &BitVec, b: &BitVec) -> BitVec {
    crate::enumerate::op::or(a.clone(), b.clone())
}

/// Walk each bit-assert expression collecting `(extract i i (SynthApp entry [])) = #b?`
/// patterns. Returns the demanded entry-output bit positions with
/// dummy `true` polarity (Relevance only uses the keys).
fn extract_initial_demand(
    bit_asserts: &[OwnedExpr],
    entry_idx: usize,
) -> BTreeMap<usize, bool> {
    fn walk(expr: &OwnedExpr, entry_idx: usize, out: &mut BTreeMap<usize, bool>) {
        if let OwnedExpr::Extract(inner, hi, lo) = expr {
            if hi == lo {
                if let OwnedExpr::SynthApp(idx, args) = inner.as_ref() {
                    if *idx == entry_idx && args.is_empty() {
                        out.insert(*hi as usize, true);
                    }
                }
            }
        }
        match expr {
            OwnedExpr::Concat(a, b)
            | OwnedExpr::Add(a, b)
            | OwnedExpr::Xor(a, b)
            | OwnedExpr::And(a, b)
            | OwnedExpr::Or(a, b)
            | OwnedExpr::Mul(a, b)
            | OwnedExpr::Sub(a, b)
            | OwnedExpr::LShr(a, b)
            | OwnedExpr::AShr(a, b)
            | OwnedExpr::Shl(a, b)
            | OwnedExpr::UDiv(a, b)
            | OwnedExpr::URem(a, b)
            | OwnedExpr::SDiv(a, b)
            | OwnedExpr::SRem(a, b)
            | OwnedExpr::BVule(a, b)
            | OwnedExpr::BVult(a, b)
            | OwnedExpr::BVsle(a, b)
            | OwnedExpr::BVslt(a, b) => {
                walk(a, entry_idx, out);
                walk(b, entry_idx, out);
            }
            OwnedExpr::Not(a) | OwnedExpr::Neg(a) => walk(a, entry_idx, out),
            OwnedExpr::Ite(c, t, e) => {
                walk(c, entry_idx, out);
                walk(t, entry_idx, out);
                walk(e, entry_idx, out);
            }
            OwnedExpr::Func(_, args) | OwnedExpr::SynthApp(_, args) => {
                for a in args {
                    walk(a, entry_idx, out);
                }
            }
            OwnedExpr::Extract(inner, _, _) => walk(inner, entry_idx, out),
            OwnedExpr::Let(_, v, b) => {
                walk(v, entry_idx, out);
                walk(b, entry_idx, out);
            }
            OwnedExpr::Var(_, _) | OwnedExpr::Const(_) => {}
        }
    }
    let mut out = BTreeMap::new();
    for expr in bit_asserts {
        walk(expr, entry_idx, &mut out);
    }
    out
}

/// Find the NT index in `grammar` that has the aux synth-fun as a
/// `Leaf(SynthApp(aux_idx, []))` production.
fn find_leaf_nt(grammar: &Grammar<'_>, aux_idx: usize) -> Option<usize> {
    for (nt_idx, (_, rules)) in grammar.nts.iter().enumerate() {
        for rule in rules {
            if let ExactRule::Leaf(expr) = rule {
                if let OwnedExpr::SynthApp(idx, args) = expr {
                    if *idx == aux_idx && args.is_empty() {
                        return Some(nt_idx);
                    }
                }
            }
        }
    }
    None
}

fn nt_output_bits(grammar: &Grammar<'_>, nt_idx: usize) -> usize {
    use crate::exact::relevance::nt_output_bits as f;
    f(&grammar.nts[nt_idx].1)
}

fn current_aux_value(r: &LfpRecipe) -> BitVec {
    match deffun::get_candidate(r.aux_synth_idx) {
        Some(OwnedExpr::Const(c)) => c,
        _ => {
            // We seeded with Const(baseline), so this shouldn't happen.
            panic!(
                "fwd_decls: aux synth-fun {} not set to a Const value",
                r.aux_synth_idx
            );
        }
    }
}
