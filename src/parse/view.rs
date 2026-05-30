use sygus_parser::ast::{Sort, SortedVar, SyGuSCmd, SyGuSFile, SyGuSTerm};

use super::SortAliases;

#[derive(Clone, Copy)]
pub struct DefineFunView<'a> {
    pub name: &'a str,
    pub args: &'a [SortedVar],
    pub ret: &'a Sort,
    pub body: &'a SyGuSTerm,
}

#[derive(Clone, Copy)]
pub struct SynthFunView<'a> {
    pub name: &'a str,
    pub args: &'a [SortedVar],
    pub ret: &'a Sort,
    pub grammar: Option<&'a sygus_parser::ast::GrammarDef>,
}

pub struct ProblemView<'a> {
    pub file: &'a SyGuSFile,
    pub sort_aliases: SortAliases,
    pub synth_funs: Vec<SynthFunView<'a>>,
    pub define_funs: Vec<DefineFunView<'a>>,
    pub constraints: Vec<&'a SyGuSTerm>,
    pub axioms: Vec<&'a SyGuSTerm>,
}

impl<'a> ProblemView<'a> {
    pub fn from_file(file: &'a SyGuSFile) -> Self {
        let sort_aliases = SortAliases::from_file(file);
        let mut synth_funs = Vec::new();
        let mut define_funs = Vec::new();
        let mut constraints = Vec::new();
        let mut axioms = Vec::new();

        for cmd in &file.cmds {
            match cmd {
                SyGuSCmd::SynthFun(name, args, ret, grammar) => {
                    synth_funs.push(SynthFunView {
                        name,
                        args,
                        ret,
                        grammar: grammar.as_ref(),
                    });
                }
                SyGuSCmd::DefineFun(name, args, ret, body) => {
                    define_funs.push(DefineFunView {
                        name,
                        args,
                        ret,
                        body,
                    });
                }
                SyGuSCmd::Constraint(term) => constraints.push(term),
                SyGuSCmd::Assume(term) => axioms.push(term),
                _ => {}
            }
        }

        Self {
            file,
            sort_aliases,
            synth_funs,
            define_funs,
            constraints,
            axioms,
        }
    }

    /// First synth-fun, for legacy single-synth-fun callers.
    pub fn synth_fun(&self) -> Option<SynthFunView<'a>> {
        self.synth_funs.first().copied()
    }

    pub fn define_fun(&self, name: &str, arity: usize) -> Option<DefineFunView<'a>> {
        self.define_funs
            .iter()
            .copied()
            .find(|f| f.name == name && f.args.len() == arity)
    }
}
