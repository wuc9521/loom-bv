use derive_more::DebugCustom;
use rand::{rngs::StdRng, seq::SliceRandom};
use sygus_parser::ast::{
    Identifier, Index, Sort, SyGuSCmd, SyGuSFile,
};

use crate::{
    enumerate::expr::OwnedExpr,
    parse,
};

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
        fn parse_width_from_identifier(id: &Identifier) -> Option<usize> {
            match id {
                Identifier::Symbol(sym) => sym.parse::<usize>().ok(),
                Identifier::Indexed(sym, idxs) => {
                    if sym == "_" && idxs.len() >= 2 {
                        if let (Index::Symbol(head), Index::Numeral(width)) = (&idxs[0], &idxs[1]) {
                            if head == "BitVec" {
                                return Some(*width);
                            }
                        }
                    }
                    if sym == "BitVec" {
                        if let Some(Index::Numeral(width)) = idxs.first() {
                            return Some(*width);
                        }
                    }
                    idxs.iter().find_map(|i| match i {
                        Index::Numeral(v) => Some(*v),
                        Index::Symbol(_) => None,
                    })
                }
            }
        }

        fn parse_sort_width(sort: &Sort) -> Option<usize> {
            match sort {
                Sort::Simple(id) => parse_width_from_identifier(id),
                Sort::Parameterized(id, ss) => {
                    parse_width_from_identifier(id).or_else(|| ss.iter().find_map(parse_sort_width))
                }
            }
        }

        for cmd in &file.cmds {
            if let SyGuSCmd::DefineFun(name, args, _, body) = cmd {
                if name != target_name || args.len() != target_arity {
                    continue;
                }
                let vargs: Vec<(&'static str, u64)> = args
                    .iter()
                    .map(|v| {
                        let name = Box::leak(v.name.clone().into_boxed_str()) as &'static str;
                        let bits = parse_sort_width(&v.sort).unwrap_or(1) as u64;
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
