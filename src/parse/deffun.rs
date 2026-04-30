use std::cell::UnsafeCell;

use derive_more::DebugCustom;
use sygus_parser::ast::{SyGuSCmd, SyGuSFile};

use crate::{enumerate::expr::OwnedExpr, info};

use super::{new_custom_error_span, Error, SortAliases};

#[derive(Clone, DebugCustom)]
#[debug(fmt = "define-fun {} {:?}", name, args)]
pub struct DefineFun {
    pub name: &'static str,
    pub args: Vec<&'static str>,
    pub ret_bits: usize,
    pub expr: OwnedExpr,
}

pub struct Environ(UnsafeCell<Vec<Vec<DefineFun>>>);

impl Environ {
    pub fn new() -> Self {
        Environ(vec![Vec::new(), Vec::new(), Vec::new()].into())
    }

    pub fn inner(&self) -> &mut Vec<Vec<DefineFun>> {
        unsafe { self.0.get().as_mut().unwrap() }
    }

    pub fn clear(&self) {
        for defs in self.inner().iter_mut() {
            defs.clear();
        }
    }

    pub fn parse_from_file(&self, file: &SyGuSFile) -> Result<(), Error> {
        let sort_aliases = SortAliases::from_file(file);
        for cmd in &file.cmds {
            if let SyGuSCmd::DefineFun(name, args, ret, body) = cmd {
                if name == "if0" || name == "im" {
                    continue;
                }
                let args: Vec<(&'static str, u64)> = args
                    .iter()
                    .map(|x| {
                        let name = Box::leak(x.name.clone().into_boxed_str()) as &'static str;
                        let bits = sort_aliases.parse_sort_width(&x.sort).unwrap_or(1) as u64;
                        (name, bits)
                    })
                    .collect();
                let name = Box::leak(name.clone().into_boxed_str());
                let ret_bits = sort_aliases.parse_sort_width(ret).ok_or_else(|| {
                    new_custom_error_span(
                        format!("DefineFun: unsupported return sort for {}: {}", name, ret),
                        pest::Span::new("", 0, 0).unwrap(),
                    )
                })?;
                let expr = OwnedExpr::from_term(body, args.as_slice())?;
                info!(
                    "DefineFun: {} {:?} -> {:?}",
                    name,
                    args.iter().map(|(name, _)| *name).collect::<Vec<_>>(),
                    expr
                );
                if self.inner().len() <= args.len() {
                    self.inner().resize_with(args.len() + 1, Vec::new);
                }
                self.inner()[args.len()].push(DefineFun {
                    name,
                    args: args.iter().map(|(name, _)| *name).collect(),
                    ret_bits,
                    expr,
                });
            }
        }
        Ok(())
    }

    pub fn lookup(&self, name: &str, nargs: usize) -> Option<usize> {
        self.inner()
            .get(nargs)?
            .iter()
            .enumerate()
            .find(|(_, p)| p.name == name)
            .map(|(a, _)| a)
    }
    pub fn apply(&self, id: usize, nargs: usize) -> &OwnedExpr {
        &self.inner()[nargs][id].expr
    }
    pub fn ret_bits(&self, id: usize, nargs: usize) -> usize {
        self.inner()[nargs][id].ret_bits
    }
    pub fn name(&self, id: usize, nargs: usize) -> &'static str {
        &self.inner()[nargs][id].name
    }
}

unsafe impl Sync for Environ {}

lazy_static::lazy_static!(
    pub static ref ENV: Environ = Environ::new();
);
