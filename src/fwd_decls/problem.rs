//! Structural representation and detection of a fwd-decls problem.

use crate::enumerate::expr::OwnedExpr;
use crate::enumerate::value::BitVec;
use crate::parse::{self, constraint::empty_span, deffun, new_custom_error_span, ProgramEnv};
use sygus_parser::ast::SyGuSTerm;

/// One auxiliary forward-declared synth-fun, with the LFP recipe that
/// determines its value as a function of the entry-point synth-fun's
/// value.
#[derive(Clone, Debug)]
pub struct LfpRecipe {
    /// Index into the synth-fun registry of the auxiliary synth-fun
    /// being defined.
    pub aux_synth_idx: usize,
    /// Baseline value (the constant initial value of the LFP iteration).
    pub baseline: BitVec,
    /// Defined-function id for the propagation `<aux>_propagation`.
    /// Takes the entry-point synth-fun's value and returns the
    /// per-bit contribution to be ORed into `aux`.
    pub propagation_fid: usize,
}

#[derive(Clone, Debug)]
pub struct FwdDeclsProblem {
    /// Index of the entry-point synth-fun (the one with the grammar
    /// the search enumerates).
    pub entry_synth_idx: usize,
    /// Bit-width of the entry-point synth-fun's return sort.
    pub entry_bits: usize,
    /// Name of the entry-point synth-fun (used for shape matching).
    pub entry_name: String,
    /// One recipe per fwd-declared synth-fun whose value is determined
    /// by a fixpoint constraint.
    pub recipes: Vec<LfpRecipe>,
    /// Remaining constraints (not fixpoint equations). Each is a Bool-
    /// returning `OwnedExpr` over the entry-point synth-fun and the
    /// auxiliary synth-funs (referenced via `SynthApp`). Evaluated with
    /// an empty args slice.
    pub bit_asserts: Vec<OwnedExpr>,
}

impl FwdDeclsProblem {
    /// Detect and build a fwd-decls problem from `view`. Requires
    /// `:fwd-decls true` and the global `deffun::ENV` already populated
    /// with the define-funs from this view.
    pub fn from_view(view: &ProgramEnv<'_>) -> parse::Result<Self> {
        if !view.features.fwd_decls {
            return Err(new_custom_error_span(
                "FwdDeclsProblem::from_view called without :fwd-decls feature".to_string(),
                empty_span(),
            ));
        }
        // Entry-point = the synth-fun with a grammar. Auxiliaries have
        // no grammar (emitted as `(synth-fun c () Sort)`).
        let entry_idx = view
            .synth_funs
            .iter()
            .position(|sf| sf.grammar.is_some())
            .ok_or_else(|| {
                new_custom_error_span(
                    "fwd-decls: no synth-fun has a grammar; nothing to enumerate over"
                        .to_string(),
                    empty_span(),
                )
            })?;
        let entry_sf = view.synth_funs[entry_idx];
        let entry_bits = view
            .sort_aliases
            .parse_sort_width(entry_sf.ret)
            .ok_or_else(|| {
                new_custom_error_span(
                    format!(
                        "fwd-decls: entry-point synth-fun `{}` return sort not BV",
                        entry_sf.name
                    ),
                    empty_span(),
                )
            })? as usize;
        let entry_name = entry_sf.name.to_string();

        let mut recipes: Vec<LfpRecipe> = Vec::new();
        let mut bit_asserts: Vec<OwnedExpr> = Vec::new();

        for term in &view.constraints {
            match match_fixpoint_shape(term, &entry_name) {
                Some(parts) => {
                    let recipe = build_recipe(parts)?;
                    recipes.push(recipe);
                }
                None => {
                    let expr = OwnedExpr::from_term(term, &[])?;
                    bit_asserts.push(expr);
                }
            }
        }

        Ok(Self {
            entry_synth_idx: entry_idx,
            entry_bits,
            entry_name,
            recipes,
            bit_asserts,
        })
    }
}

/// Parts extracted from a successful fixpoint-shape match.
struct FixpointParts<'a> {
    aux_name: &'a str,
    baseline_name: &'a str,
    prop_name: &'a str,
}

/// Match `(= AUX (bvor BASELINE (PROP ENTRY)))` and return the names.
fn match_fixpoint_shape<'a>(
    term: &'a SyGuSTerm,
    entry_name: &str,
) -> Option<FixpointParts<'a>> {
    let term = strip_annotation(term);
    let SyGuSTerm::Application(op, args) = term else {
        return None;
    };
    if op.get_name() != "=" || args.len() != 2 {
        return None;
    }
    // Try both arg orders for `=`.
    for (lhs, rhs) in [(0, 1), (1, 0)] {
        if let Some(parts) = try_one_orientation(&args[lhs], &args[rhs], entry_name) {
            return Some(parts);
        }
    }
    None
}

fn try_one_orientation<'a>(
    lhs: &'a SyGuSTerm,
    rhs: &'a SyGuSTerm,
    entry_name: &str,
) -> Option<FixpointParts<'a>> {
    let lhs = strip_annotation(lhs);
    let SyGuSTerm::Identifier(id) = lhs else {
        return None;
    };
    let aux_name = id.get_name();

    let rhs = strip_annotation(rhs);
    let SyGuSTerm::Application(bvor_id, bvor_args) = rhs else {
        return None;
    };
    if bvor_id.get_name() != "bvor" || bvor_args.len() != 2 {
        return None;
    }
    // baseline + prop_call in either order.
    for (b, p) in [(0, 1), (1, 0)] {
        let baseline = strip_annotation(&bvor_args[b]);
        let prop_call = strip_annotation(&bvor_args[p]);
        let SyGuSTerm::Identifier(baseline_id) = baseline else {
            continue;
        };
        let SyGuSTerm::Application(prop_id, prop_args) = prop_call else {
            continue;
        };
        if prop_args.len() != 1 {
            continue;
        }
        let entry_arg = strip_annotation(&prop_args[0]);
        let SyGuSTerm::Identifier(entry_id) = entry_arg else {
            continue;
        };
        if entry_id.get_name() != entry_name {
            continue;
        }
        return Some(FixpointParts {
            aux_name,
            baseline_name: baseline_id.get_name(),
            prop_name: prop_id.get_name(),
        });
    }
    None
}

fn strip_annotation(term: &SyGuSTerm) -> &SyGuSTerm {
    match term {
        SyGuSTerm::Annotated(inner, _) => strip_annotation(inner),
        other => other,
    }
}

fn build_recipe(parts: FixpointParts<'_>) -> parse::Result<LfpRecipe> {
    let aux_synth_idx = deffun::lookup_synth(parts.aux_name, 0).ok_or_else(|| {
        new_custom_error_span(
            format!(
                "fwd-decls: fixpoint LHS `{}` is not a registered nullary synth-fun",
                parts.aux_name
            ),
            empty_span(),
        )
    })?;
    let baseline_fid = deffun::ENV.lookup(parts.baseline_name, 0).ok_or_else(|| {
        new_custom_error_span(
            format!(
                "fwd-decls: baseline `{}` is not a nullary define-fun",
                parts.baseline_name
            ),
            empty_span(),
        )
    })?;
    let propagation_fid = deffun::ENV.lookup(parts.prop_name, 1).ok_or_else(|| {
        new_custom_error_span(
            format!(
                "fwd-decls: propagation `{}` is not a unary define-fun",
                parts.prop_name
            ),
            empty_span(),
        )
    })?;
    // Baseline is a constant define-fun; evaluate once.
    let baseline = deffun::ENV.eval_defined(baseline_fid, &[], &[]).map_err(|e| {
        new_custom_error_span(
            format!(
                "fwd-decls: failed to evaluate baseline `{}`: {:?}",
                parts.baseline_name, e
            ),
            empty_span(),
        )
    })?;
    Ok(LfpRecipe {
        aux_synth_idx,
        baseline,
        propagation_fid,
    })
}
