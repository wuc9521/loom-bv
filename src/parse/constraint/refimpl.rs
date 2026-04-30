use derive_more::DebugCustom;
use sygus_parser::ast::{SyGuSCmd, SyGuSFile};

use crate::{
    enumerate::expr::OwnedExpr,
    parse,
};

#[cfg(feature = "chatgpt")]
use rand::{rngs::StdRng, seq::SliceRandom};
#[cfg(feature = "chatgpt")]
use super::PbeConstraint;

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
