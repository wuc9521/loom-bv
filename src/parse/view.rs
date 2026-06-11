use std::collections::HashSet;

use sygus_parser::ast::{
    GrammarDef, Sort, SortedVar, SyGuSCmd, SyGuSFeature, SyGuSFile, SyGuSGTerm, SyGuSTerm,
};

use super::SortAliases;

#[derive(Clone, Debug)]
pub struct FeatureSet {
    pub grammars: bool,
    pub fwd_decls: bool,
    pub recursion: bool,
    pub oracles: bool,
    pub weights: bool,
}

impl Default for FeatureSet {
    fn default() -> Self {
        Self {
            grammars: true,
            fwd_decls: false,
            recursion: false,
            oracles: false,
            weights: false,
        }
    }
}

impl FeatureSet {
    fn set(&mut self, feature: &SyGuSFeature, value: bool) {
        match feature {
            SyGuSFeature::Grammars => self.grammars = value,
            SyGuSFeature::FwdDecls => self.fwd_decls = value,
            SyGuSFeature::Recursion => self.recursion = value,
            SyGuSFeature::Oracles => self.oracles = value,
            SyGuSFeature::Weights => self.weights = value,
        }
    }
}

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

#[derive(Clone, Debug, Default)]
pub struct GrammarDeps {
    pub define_calls: Vec<usize>,
    pub forward_synth_calls: Vec<usize>,
    pub future_synth_calls: Vec<usize>,
    pub uses_self: bool,
}

impl GrammarDeps {
    pub fn requires_fwd_decls(&self) -> bool {
        !self.forward_synth_calls.is_empty()
    }

    pub fn requires_recursion(&self) -> bool {
        self.uses_self
    }
}

pub struct ProgramEnv<'a> {
    pub file: &'a SyGuSFile,
    pub features: FeatureSet,
    pub sort_aliases: SortAliases,
    pub synth_funs: Vec<SynthFunView<'a>>,
    pub define_funs: Vec<DefineFunView<'a>>,
    pub constraints: Vec<&'a SyGuSTerm>,
    pub grammar_deps: Vec<GrammarDeps>,
}

pub type ProblemView<'a> = ProgramEnv<'a>;

impl<'a> ProgramEnv<'a> {
    pub fn from_file(file: &'a SyGuSFile) -> Self {
        let sort_aliases = SortAliases::from_file(file);
        let mut features = FeatureSet::default();
        let mut synth_funs = Vec::new();
        let mut define_funs = Vec::new();
        let mut constraints = Vec::new();

        for cmd in &file.cmds {
            match cmd {
                SyGuSCmd::SetFeature(feature, value) => features.set(feature, *value),
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
        let grammar_deps = analyze_grammar_deps(&synth_funs, &define_funs);

        Self {
            file,
            features,
            sort_aliases,
            synth_funs,
            define_funs,
            constraints,
            grammar_deps,
        }
    }

    /// The primary synth-fun: the one with a non-trivial grammar.
    /// In multi-synth-fun problems (closure pattern), this picks the operator
    /// synth-fun over the constant-grammar fixpoint placeholder.
    pub fn synth_fun(&self) -> Option<SynthFunView<'a>> {
        if self.synth_funs.len() == 1 {
            return self.synth_funs.first().copied();
        }
        self.synth_funs
            .iter()
            .copied()
            .find(|sf| sf.grammar.is_some_and(|g| !is_constant_grammar(g)))
            .or_else(|| self.synth_funs.first().copied())
    }

    /// The fixpoint synth-fun name, if any define-fun references a synth-fun.
    /// Returns the name of the synth-fun that define-funs substitute into.
    pub fn fixpoint_name(&self) -> Option<&'a str> {
        for sf in &self.synth_funs {
            if sf.grammar.is_some_and(|g| is_constant_grammar(g)) {
                return Some(sf.name);
            }
        }
        // Single synth-fun referenced by its own define-funs
        if self.synth_funs.len() == 1 {
            let name = self.synth_funs[0].name;
            let referenced = self
                .define_funs
                .iter()
                .any(|df| term_mentions_symbol(df.body, name));
            if referenced {
                return Some(name);
            }
        }
        None
    }

    pub fn define_fun(&self, name: &str, arity: usize) -> Option<DefineFunView<'a>> {
        self.define_funs
            .iter()
            .copied()
            .find(|f| f.name == name && f.args.len() == arity)
    }

    pub fn grammar_deps_for(&self, synth_idx: usize) -> Option<&GrammarDeps> {
        self.grammar_deps.get(synth_idx)
    }
}

pub fn is_constant_grammar(g: &GrammarDef) -> bool {
    g.grouped_rule_lists.len() == 1
        && g.grouped_rule_lists[0].terms.len() == 1
        && matches!(&g.grouped_rule_lists[0].terms[0], SyGuSGTerm::Constant(_))
}

pub fn term_mentions_symbol(term: &SyGuSTerm, target: &str) -> bool {
    match term {
        SyGuSTerm::Identifier(id) => id.get_name() == target,
        SyGuSTerm::Application(id, args) => {
            id.get_name() == target || args.iter().any(|arg| term_mentions_symbol(arg, target))
        }
        SyGuSTerm::Annotated(inner, _) => term_mentions_symbol(inner, target),
        SyGuSTerm::Let(bindings, body) => {
            bindings
                .iter()
                .any(|binding| term_mentions_symbol(&binding.term, target))
                || term_mentions_symbol(body, target)
        }
        SyGuSTerm::Forall(_, body) | SyGuSTerm::Exists(_, body) => {
            term_mentions_symbol(body, target)
        }
        SyGuSTerm::Literal(_) => false,
    }
}

fn analyze_grammar_deps(
    synths: &[SynthFunView<'_>],
    defines: &[DefineFunView<'_>],
) -> Vec<GrammarDeps> {
    synths
        .iter()
        .enumerate()
        .map(|(idx, synth)| {
            let mut deps = GrammarDeps::default();
            let Some(grammar) = synth.grammar else {
                return deps;
            };
            let nt_names = grammar
                .grouped_rule_lists
                .iter()
                .map(|rule| rule.symbol.as_str())
                .collect::<HashSet<_>>();
            let mut define_stack = Vec::new();
            for rule_list in &grammar.grouped_rule_lists {
                for gterm in &rule_list.terms {
                    if let SyGuSGTerm::SyGuSTerm(term) = gterm {
                        collect_grammar_term_deps(
                            term,
                            idx,
                            &nt_names,
                            synths,
                            defines,
                            &mut deps,
                            &mut define_stack,
                        );
                    }
                }
            }
            deps
        })
        .collect()
}

fn collect_grammar_term_deps(
    term: &SyGuSTerm,
    current_synth: usize,
    nt_names: &HashSet<&str>,
    synths: &[SynthFunView<'_>],
    defines: &[DefineFunView<'_>],
    deps: &mut GrammarDeps,
    define_stack: &mut Vec<usize>,
) {
    match term {
        SyGuSTerm::Identifier(id) => {
            collect_symbol_deps(
                id.get_name(),
                0,
                current_synth,
                nt_names,
                synths,
                defines,
                deps,
                define_stack,
            );
        }
        SyGuSTerm::Application(id, args) => {
            collect_symbol_deps(
                id.get_name(),
                args.len(),
                current_synth,
                nt_names,
                synths,
                defines,
                deps,
                define_stack,
            );
            for arg in args {
                collect_grammar_term_deps(
                    arg,
                    current_synth,
                    nt_names,
                    synths,
                    defines,
                    deps,
                    define_stack,
                );
            }
        }
        SyGuSTerm::Annotated(inner, _) => collect_grammar_term_deps(
            inner,
            current_synth,
            nt_names,
            synths,
            defines,
            deps,
            define_stack,
        ),
        SyGuSTerm::Let(bindings, body) => {
            for binding in bindings {
                collect_grammar_term_deps(
                    &binding.term,
                    current_synth,
                    nt_names,
                    synths,
                    defines,
                    deps,
                    define_stack,
                );
            }
            collect_grammar_term_deps(
                body,
                current_synth,
                nt_names,
                synths,
                defines,
                deps,
                define_stack,
            );
        }
        SyGuSTerm::Forall(_, body) | SyGuSTerm::Exists(_, body) => collect_grammar_term_deps(
            body,
            current_synth,
            nt_names,
            synths,
            defines,
            deps,
            define_stack,
        ),
        SyGuSTerm::Literal(_) => {}
    }
}

fn collect_symbol_deps(
    name: &str,
    arity: usize,
    current_synth: usize,
    nt_names: &HashSet<&str>,
    synths: &[SynthFunView<'_>],
    defines: &[DefineFunView<'_>],
    deps: &mut GrammarDeps,
    define_stack: &mut Vec<usize>,
) {
    if nt_names.contains(name) {
        return;
    }

    if let Some(synth_idx) = synths
        .iter()
        .position(|synth| synth.name == name && synth.args.len() == arity)
    {
        if synth_idx == current_synth {
            deps.uses_self = true;
        } else if synth_idx < current_synth {
            push_unique(&mut deps.forward_synth_calls, synth_idx);
        } else {
            push_unique(&mut deps.future_synth_calls, synth_idx);
        }
    }

    if let Some(define_idx) = defines
        .iter()
        .position(|define| define.name == name && define.args.len() == arity)
    {
        push_unique(&mut deps.define_calls, define_idx);
        if define_stack.contains(&define_idx) {
            return;
        }
        define_stack.push(define_idx);
        collect_grammar_term_deps(
            defines[define_idx].body,
            current_synth,
            nt_names,
            synths,
            defines,
            deps,
            define_stack,
        );
        define_stack.pop();
    }
}

fn push_unique(values: &mut Vec<usize>, value: usize) {
    if !values.contains(&value) {
        values.push(value);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn program_env_tracks_forward_deps_through_macros() {
        let file = SyGuSFile::from_str(
            r#"
            (set-feature :fwd-decls true)
            (synth-fun f () (_ BitVec 1)
              ((B (_ BitVec 1))
               ((B (_ BitVec 1) (#b0)))))
            (define-fun wrap ((x (_ BitVec 1))) (_ BitVec 1) f)
            (synth-fun g () (_ BitVec 1)
              ((B (_ BitVec 1))
               ((B (_ BitVec 1) ((wrap B))))))
            (check-synth)
            "#,
        )
        .unwrap();
        let env = ProgramEnv::from_file(&file);

        assert!(env.features.fwd_decls);
        assert_eq!(env.synth_funs.len(), 2);
        assert_eq!(env.grammar_deps[1].define_calls, vec![0]);
        assert_eq!(env.grammar_deps[1].forward_synth_calls, vec![0]);
        assert!(env.grammar_deps[1].requires_fwd_decls());
    }

    #[test]
    fn program_env_tracks_recursive_synth_grammar_use() {
        let file = SyGuSFile::from_str(
            r#"
            (set-feature :recursion true)
            (synth-fun h () (_ BitVec 1)
              ((B (_ BitVec 1))
               ((B (_ BitVec 1) (#b0 h)))))
            (check-synth)
            "#,
        )
        .unwrap();
        let env = ProgramEnv::from_file(&file);

        assert!(env.features.recursion);
        assert!(env.grammar_deps[0].uses_self);
        assert!(env.grammar_deps[0].requires_recursion());
    }
}
