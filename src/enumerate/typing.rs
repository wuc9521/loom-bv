//! Parse-time sort checking for SyGuS terms.
//!
//! `OwnedExpr` is untyped: every term is carried as a `BitVec`, with Bool
//! encoded as a 1-bit value under the internal negative-logic convention
//! (`0` = true). Lowering is lossy — `bvand` and the boolean `or` both become
//! `OwnedExpr::And`, `bvxor`/`=`/bool-`xor` all become `OwnedExpr::Xor` — so a
//! term's sort cannot be recovered once it is an `OwnedExpr`.
//!
//! [`check_sort`] therefore runs on the `SyGuSTerm`, before lowering, and
//! rejects genuine `Bool` ↔ `(_ BitVec n)` mismatches (e.g. a bit-vector used
//! as an `ite` condition, or a Bool fed to `bvand`). It only enforces the
//! Bool/bit-vector distinction; width mismatches between same-family sorts are
//! left to the downstream solver.
//!
//! The branch structure mirrors `OwnedExpr::from_term_lower` exactly, so every
//! term the lowering accepts is also accepted here (plus the sort checks).

use sygus_parser::ast::SyGuSTerm;

use crate::parse::{self, deffun, empty_span, new_custom_error_span};

/// SMT sort of a term, tracked only during parse-time validation.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Sort {
    Bool,
    BitVec(usize),
}

impl Sort {
    /// Require a bit-vector, returning its width; error if this is a Bool.
    fn as_bitvec(self, ctx: &str) -> parse::Result<usize> {
        match self {
            Sort::BitVec(w) => Ok(w),
            Sort::Bool => Err(new_custom_error_span(
                format!("sort error: expected a bit-vector but found Bool in `{ctx}`"),
                empty_span(),
            )),
        }
    }

    /// Require a Bool; error if this is a bit-vector.
    fn expect_bool(self, ctx: &str) -> parse::Result<()> {
        match self {
            Sort::Bool => Ok(()),
            Sort::BitVec(w) => Err(new_custom_error_span(
                format!("sort error: expected Bool but found (_ BitVec {w}) in `{ctx}`"),
                empty_span(),
            )),
        }
    }

    /// True if both sorts are Bool, or both are bit-vectors (any widths).
    fn same_family(self, other: Sort) -> bool {
        matches!(
            (self, other),
            (Sort::Bool, Sort::Bool) | (Sort::BitVec(_), Sort::BitVec(_))
        )
    }
}

/// Compute the SMT sort of `term`, rejecting ill-sorted terms — in particular
/// genuine `Bool` ↔ bit-vector confusions. `env` maps in-scope names to their
/// sorts (formal parameters are always bit-vectors here).
pub fn check_sort<'s>(term: &'s SyGuSTerm, env: &[(&'s str, Sort)]) -> parse::Result<Sort> {
    match term {
        SyGuSTerm::Identifier(id) => {
            let name = id.get_name();
            if let Some((_, sort)) = env.iter().find(|(n, _)| *n == name) {
                Ok(*sort)
            } else if name.eq_ignore_ascii_case("true") || name.eq_ignore_ascii_case("false") {
                Ok(Sort::Bool)
            } else if let Some(digits) = name.strip_prefix("#x") {
                Ok(Sort::BitVec((digits.len() * 4).max(1)))
            } else if let Some(digits) = name.strip_prefix("#b") {
                Ok(Sort::BitVec(digits.len().max(1)))
            } else if name.strip_prefix("#d").is_some() {
                Ok(Sort::BitVec(64))
            } else if let Some((_, width)) = crate::parse::constraint::indexed_bv_literal(id) {
                // SMT-LIB indexed bit-vector literal `(_ bvDECIMAL WIDTH)`.
                Ok(Sort::BitVec(width))
            } else if let Some(fid) = deffun::ENV.lookup(name, 0) {
                Ok(Sort::BitVec(deffun::ENV.ret_bits(fid)))
            } else if let Some(idx) = deffun::lookup_synth(name, 0) {
                Ok(Sort::BitVec(deffun::synth_ret_bits(idx)))
            } else {
                Err(new_custom_error_span(
                    format!("Unrecognized identifier `{name}`"),
                    empty_span(),
                ))
            }
        }
        SyGuSTerm::Literal(lit) => Ok(Sort::BitVec(crate::parse::literal_to_value(lit)?.bits())),
        SyGuSTerm::Annotated(inner, _) => check_sort(inner, env),
        SyGuSTerm::Application(id, args) => {
            let opname = id.get_name();
            if args.len() == 1 {
                if let Some((hi, lo)) = crate::parse::extract_indices_from_identifier(id) {
                    if hi >= lo {
                        let w = check_sort(&args[0], env)?.as_bitvec("extract operand")?;
                        if hi >= w {
                            return Err(new_custom_error_span(
                                format!(
                                    "sort error: extract [{hi}:{lo}] out of range for (_ BitVec {w})"
                                ),
                                empty_span(),
                            ));
                        }
                        return Ok(Sort::BitVec(hi - lo + 1));
                    }
                }
            }
            if opname == "concat" && args.len() >= 2 {
                let mut width = 0usize;
                for arg in args {
                    width += check_sort(arg, env)?.as_bitvec("concat operand")?;
                }
                return Ok(Sort::BitVec(width));
            }
            if matches!(opname, "bvnot" | "bvneg") && args.len() == 1 {
                let w = check_sort(&args[0], env)?.as_bitvec(opname)?;
                return Ok(Sort::BitVec(w));
            }
            const BV_BINARY: &[&str] = &[
                "bvadd", "bvxor", "bvand", "bvor", "bvmul", "bvsub", "bvlshr", "bvashr", "bvshl",
                "bvudiv", "bvurem", "bvsdiv", "bvsrem",
            ];
            if BV_BINARY.contains(&opname) && args.len() == 2 {
                let w = check_sort(&args[0], env)?.as_bitvec(opname)?;
                check_sort(&args[1], env)?.as_bitvec(opname)?;
                return Ok(Sort::BitVec(w));
            }
            const BV_COMPARE: &[&str] = &[
                "bvule", "bvult", "bvsle", "bvslt", "bvugt", "bvuge", "bvsgt", "bvsge",
            ];
            if BV_COMPARE.contains(&opname) && args.len() == 2 {
                check_sort(&args[0], env)?.as_bitvec(opname)?;
                check_sort(&args[1], env)?.as_bitvec(opname)?;
                return Ok(Sort::Bool);
            }
            if opname == "not" && args.len() == 1 {
                check_sort(&args[0], env)?.expect_bool("not")?;
                return Ok(Sort::Bool);
            }
            if matches!(opname, "and" | "or" | "xor") && args.len() >= 2 {
                for arg in args {
                    check_sort(arg, env)?.expect_bool(opname)?;
                }
                return Ok(Sort::Bool);
            }
            if opname == "=" && args.len() == 2 {
                let lhs = check_sort(&args[0], env)?;
                let rhs = check_sort(&args[1], env)?;
                if !lhs.same_family(rhs) {
                    return Err(new_custom_error_span(
                        format!(
                            "sort error: `=` operands have mismatched sorts {lhs:?} and {rhs:?}"
                        ),
                        empty_span(),
                    ));
                }
                return Ok(Sort::Bool);
            }
            if opname == "ite" && args.len() == 3 {
                check_sort(&args[0], env)?.expect_bool("ite condition")?;
                let then_sort = check_sort(&args[1], env)?;
                let else_sort = check_sort(&args[2], env)?;
                if !then_sort.same_family(else_sort) {
                    return Err(new_custom_error_span(
                        format!(
                            "sort error: ite branches have mismatched sorts {then_sort:?} and {else_sort:?}"
                        ),
                        empty_span(),
                    ));
                }
                return Ok(then_sort);
            }
            if let Some(fid) = deffun::ENV.lookup(opname, args.len()) {
                for arg in args {
                    check_sort(arg, env)?.as_bitvec(opname)?;
                }
                return Ok(Sort::BitVec(deffun::ENV.ret_bits(fid)));
            }
            if let Some(idx) = deffun::lookup_synth(opname, args.len()) {
                for arg in args {
                    check_sort(arg, env)?;
                }
                return Ok(Sort::BitVec(deffun::synth_ret_bits(idx)));
            }
            Err(new_custom_error_span(
                format!("Unrecongnized Expression: {term}"),
                empty_span(),
            ))
        }
        SyGuSTerm::Let(bindings, body) => {
            let mut extended = env.to_vec();
            for binding in bindings {
                let sort = check_sort(&binding.term, &extended)?;
                extended.push((binding.name.as_str(), sort));
            }
            check_sort(body, &extended)
        }
        SyGuSTerm::Exists(_, _) | SyGuSTerm::Forall(_, _) => Err(new_custom_error_span(
            format!("Unrecongnized Expression: {term}"),
            empty_span(),
        )),
    }
}
