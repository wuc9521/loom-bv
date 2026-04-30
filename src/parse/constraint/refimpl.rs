use derive_more::DebugCustom;
use sygus_parser::ast::{SortedVar, SyGuSCmd, SyGuSFile, SyGuSTerm};

use crate::{
    enumerate::expr::OwnedExpr,
    parse,
};

#[cfg(feature = "chatgpt")]
use rand::{rngs::StdRng, seq::SliceRandom};
#[cfg(feature = "chatgpt")]
use super::PbeConstraint;
use super::{constraints, term_app, term_eq, term_var_name};

#[derive(DebugCustom, Clone)]
#[debug(fmt = "{:?}", ref_impl)]
pub struct RefImplConstraint {
    pub args: usize,
    pub ref_impl: OwnedExpr,
}

impl RefImplConstraint {
    pub fn parse_from_file(
        file: &SyGuSFile,
        target_name: &str,
        target_arity: usize,
    ) -> Result<Option<Self>, parse::Error> {
        fn target_var_indices(
            args: &[SyGuSTerm],
            target_args: &[SortedVar],
        ) -> Option<Vec<usize>> {
            let mut indices = Vec::with_capacity(args.len());
            for arg in args {
                let name = term_var_name(arg)?;
                let idx = target_args.iter().position(|v| v.name == name)?;
                indices.push(idx);
            }
            Some(indices)
        }

        fn helper_env_from_call(
            helper_formals: &[SortedVar],
            helper_call_args: &[SyGuSTerm],
            target_args: &[SortedVar],
        ) -> Option<Vec<(&'static str, u64)>> {
            if helper_formals.len() != helper_call_args.len() {
                return None;
            }
            let mapping = target_var_indices(helper_call_args, target_args)?;
            let mut env = target_args
                .iter()
                .map(|arg| {
                    let name =
                        Box::leak(format!("__unused_target_arg_{}", arg.name).into_boxed_str());
                    (name as &'static str, 64_u64)
                })
                .collect::<Vec<_>>();
            for (formal, target_idx) in helper_formals.iter().zip(mapping) {
                let name = Box::leak(formal.name.clone().into_boxed_str()) as &'static str;
                env[target_idx] = (name, 64);
            }
            Some(env)
        }

        let sort_aliases = parse::SortAliases::from_file(file);

        for cmd in &file.cmds {
            if let SyGuSCmd::DefineFun(name, args, _, body) = cmd {
                if name != target_name || args.len() != target_arity {
                    continue;
                }
                let vargs: Vec<(&'static str, u64)> = args
                    .iter()
                    .map(|v| {
                        let name = Box::leak(v.name.clone().into_boxed_str()) as &'static str;
                        let bits = sort_aliases.parse_sort_width(&v.sort).unwrap_or(1) as u64;
                        (name, bits)
                    })
                    .collect();
                let e = OwnedExpr::from_term(body, &*vargs)?;
                return Ok(Some(Self {
                    ref_impl: e,
                    args: vargs.len(),
                }));
            }
        }

        let Some(target_decl) = file.cmds.iter().find_map(|cmd| match cmd {
            SyGuSCmd::SynthFun(name, args, _, _) if name == target_name => Some(args.as_slice()),
            _ => None,
        }) else {
            return Ok(None);
        };

        for term in constraints(file) {
            let Some((lhs_eq, rhs_eq)) = term_eq(term) else {
                continue;
            };

            let mut candidate = None;
            for (lhs, rhs) in [(lhs_eq, rhs_eq), (rhs_eq, lhs_eq)] {
                let Some((rhs_name, rhs_args)) = term_app(rhs) else {
                    continue;
                };
                if rhs_name != target_name || rhs_args.len() != target_arity {
                    continue;
                }
                let expected = (0..target_decl.len()).collect::<Vec<_>>();
                if target_var_indices(rhs_args, target_decl).as_deref() != Some(expected.as_slice()) {
                    continue;
                }
                let Some((helper_name, helper_call_args)) = term_app(lhs) else {
                    continue;
                };
                candidate = Some((helper_name, helper_call_args));
                break;
            }

            let Some((helper_name, helper_call_args)) = candidate else {
                continue;
            };

            for helper_cmd in &file.cmds {
                let SyGuSCmd::DefineFun(name, helper_formals, _ret, body) = helper_cmd else {
                    continue;
                };
                if name != helper_name {
                    continue;
                }
                let Some(env) = helper_env_from_call(helper_formals, helper_call_args, target_decl)
                else {
                    continue;
                };
                let e = OwnedExpr::from_term(body, &env)?;
                return Ok(Some(Self {
                    ref_impl: e,
                    args: target_arity,
                }));
            }
        }

        Ok(None)
    }
    #[cfg(feature = "chatgpt")]
    pub fn generate_pbe(&self, count: usize, arity: usize, rng: &mut StdRng) -> PbeConstraint {
        let mut res = PbeConstraint::new(arity);
        for _ in 0..count {
            let mask = [
                u64::MAX,
                u64::MAX,
                u64::MAX,
                u64::MAX,
                0xFF,
                0xFFFFFFFFFFFF,
                0xFFFFFF0000FFFFFF,
            ]
            .choose(rng)
            .unwrap();
            res.random_example(rng, *mask, &self.ref_impl, arity)
        }
        res
    }
}
