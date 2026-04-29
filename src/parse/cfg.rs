use derive_more::{Deref, From};
use sygus_parser::ast::{GrammarDef, SyGuSGTerm};

use super::sexpr::Error;
use derive_more::DebugCustom;
use join_lazy_fmt::Join;
#[derive(DebugCustom, Clone)]
#[debug(fmt = "{} -> {}", _0, "\" | \".join(_1)")]
pub struct NonTerminal<'i>(pub &'i str, pub Vec<SyGuSGTerm>);

#[derive(From, DebugCustom, Clone, Deref)]
#[debug(fmt = "{:?}", _0)]
pub struct Cfg<'i>(Vec<NonTerminal<'i>>);

impl<'i> Cfg<'i> {
    pub fn nt(&self, name: &str) -> Option<usize> {
        self.iter()
            .enumerate()
            .find(|x| x.1 .0 == name)
            .map(|x| x.0)
    }

    pub fn from_grammar(grammar: &GrammarDef) -> Result<Cfg<'static>, Error> {
        let nts = grammar
            .grouped_rule_lists
            .iter()
            .map(|rule_list| {
                let name: &'static str = Box::leak(rule_list.symbol.clone().into_boxed_str());
                let terms = rule_list.terms.clone();
                NonTerminal(name, terms)
            })
            .collect::<Vec<_>>();
        Ok(Cfg(nts))
    }
}
