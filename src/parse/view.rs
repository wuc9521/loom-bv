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
}

impl<'a> ProblemView<'a> {
    pub fn from_file(file: &'a SyGuSFile) -> Self {
        let sort_aliases = SortAliases::from_file(file);
        let mut synth_funs = Vec::new();
        let mut define_funs = Vec::new();
        let mut constraints = Vec::new();

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
                _ => {}
            }
        }

        Self {
            file,
            sort_aliases,
            synth_funs,
            define_funs,
            constraints,
        }
    }

    /// The primary synth-fun: the one with a non-trivial grammar.
    /// In multi-synth-fun problems (closure pattern), this picks the operator
    /// synth-fun over the constant-grammar fixpoint placeholder.
    pub fn synth_fun(&self) -> Option<SynthFunView<'a>> {
        if self.synth_funs.len() == 1 {
            return self.synth_funs.first().copied();
        }
        self.synth_funs.iter().copied().find(|sf| {
            sf.grammar.is_some_and(|g| !Self::is_constant_grammar(g))
        }).or_else(|| self.synth_funs.first().copied())
    }

    /// The fixpoint synth-fun name, if any define-fun references a synth-fun.
    /// Returns the name of the synth-fun that define-funs substitute into.
    pub fn fixpoint_name(&self) -> Option<&'a str> {
        for sf in &self.synth_funs {
            if sf.grammar.is_some_and(|g| Self::is_constant_grammar(g)) {
                return Some(sf.name);
            }
        }
        // Single synth-fun referenced by its own define-funs
        if self.synth_funs.len() == 1 {
            let name = self.synth_funs[0].name;
            let referenced = self.define_funs.iter().any(|df| {
                Self::term_mentions(df.body, name)
            });
            if referenced {
                return Some(name);
            }
        }
        None
    }

    fn is_constant_grammar(g: &sygus_parser::ast::GrammarDef) -> bool {
        g.grouped_rule_lists.len() == 1
            && g.grouped_rule_lists[0].terms.len() == 1
            && matches!(
                &g.grouped_rule_lists[0].terms[0],
                sygus_parser::ast::SyGuSGTerm::Constant(_)
            )
    }

    fn term_mentions(term: &SyGuSTerm, target: &str) -> bool {
        match term {
            SyGuSTerm::Identifier(id) => id.get_name() == target,
            SyGuSTerm::Application(id, args) => {
                id.get_name() == target || args.iter().any(|a| Self::term_mentions(a, target))
            }
            SyGuSTerm::Annotated(inner, _) => Self::term_mentions(inner, target),
            SyGuSTerm::Let(bindings, body) => {
                bindings.iter().any(|b| Self::term_mentions(&b.term, target))
                    || Self::term_mentions(body, target)
            }
            SyGuSTerm::Forall(_, body) | SyGuSTerm::Exists(_, body) => {
                Self::term_mentions(body, target)
            }
            SyGuSTerm::Literal(_) => false,
        }
    }

    pub fn define_fun(&self, name: &str, arity: usize) -> Option<DefineFunView<'a>> {
        self.define_funs
            .iter()
            .copied()
            .find(|f| f.name == name && f.args.len() == arity)
    }
}
