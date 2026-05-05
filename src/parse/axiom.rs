use std::collections::{BTreeMap, BTreeSet};

use sygus_parser::ast::{Identifier, SyGuSTerm};

#[derive(Clone, Debug)]
enum Pattern {
    Var(String),
    Id(String),
    App(String, Vec<Pattern>),
}

#[derive(Clone, Debug)]
struct EquationRule {
    lhs: Pattern,
    rhs: Pattern,
}

#[derive(Clone, Debug, Default)]
pub struct AxiomRewriter {
    by_root: BTreeMap<(String, usize), Vec<(Pattern, Pattern)>>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CanonTerm {
    Atom(String),
    App(String, Vec<CanonTerm>),
}

impl std::fmt::Display for CanonTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Atom(atom) => f.write_str(atom),
            Self::App(name, args) => {
                write!(f, "({name}")?;
                for arg in args {
                    write!(f, " {arg}")?;
                }
                f.write_str(")")
            }
        }
    }
}

impl Default for CanonTerm {
    fn default() -> Self {
        Self::Atom(String::new())
    }
}

impl CanonTerm {
    pub fn from_sygus_term(term: &SyGuSTerm) -> Self {
        match term {
            SyGuSTerm::Identifier(id) => Self::Atom(id.to_string()),
            SyGuSTerm::Application(id, args) => Self::App(
                id.to_string(),
                args.iter().map(Self::from_sygus_term).collect(),
            ),
            SyGuSTerm::Annotated(inner, _) => Self::from_sygus_term(inner),
            _ => Self::Atom(term.to_string()),
        }
    }

    fn size(&self) -> usize {
        match self {
            Self::Atom(_) => 1,
            Self::App(_, args) => 1 + args.iter().map(Self::size).sum::<usize>(),
        }
    }
}

impl AxiomRewriter {
    pub fn from_axioms(axioms: &[SyGuSTerm]) -> Option<Self> {
        let equations = axioms
            .iter()
            .filter_map(equation_rule_from_axiom)
            .collect::<Vec<_>>();
        if equations.is_empty() {
            None
        } else {
            let mut by_root = BTreeMap::<(String, usize), Vec<(Pattern, Pattern)>>::new();
            for eq in equations {
                if let Some(key) = pattern_root(&eq.lhs) {
                    by_root
                        .entry(key)
                        .or_default()
                        .push((eq.lhs.clone(), eq.rhs.clone()));
                }
                if let Some(key) = pattern_root(&eq.rhs) {
                    by_root
                        .entry(key)
                        .or_default()
                        .push((eq.rhs.clone(), eq.lhs.clone()));
                }
            }
            Some(Self { by_root })
        }
    }

    pub fn root_redundant(&self, term: &CanonTerm) -> bool {
        let CanonTerm::App(name, args) = term else {
            return false;
        };
        let Some(candidates) = self.by_root.get(&(name.clone(), args.len())) else {
            return false;
        };
        candidates
            .iter()
            .any(|(from, to)| rewrites_to_smaller(term, from, to))
    }
}

fn rewrites_to_smaller(term: &CanonTerm, from: &Pattern, to: &Pattern) -> bool {
    let mut subst = std::collections::HashMap::<String, CanonTerm>::new();
    if !match_pattern_canon(from, term, &mut subst) {
        return false;
    }
    let other = instantiate_canon(to, &subst);
    term_is_better(&other, term)
}

fn term_is_better(lhs: &CanonTerm, rhs: &CanonTerm) -> bool {
    let lhs_size = lhs.size();
    let rhs_size = rhs.size();
    lhs_size < rhs_size || (lhs_size == rhs_size && lhs < rhs)
}

fn match_pattern_canon(
    pattern: &Pattern,
    term: &CanonTerm,
    subst: &mut std::collections::HashMap<String, CanonTerm>,
) -> bool {
    match pattern {
        Pattern::Var(name) => match subst.get(name) {
            Some(existing) => existing == term,
            None => {
                subst.insert(name.clone(), term.clone());
                true
            }
        },
        Pattern::Id(name) => matches!(term, CanonTerm::Atom(atom) if atom == name),
        Pattern::App(name, parts) => {
            let CanonTerm::App(id, args) = term else {
                return false;
            };
            if id != name || args.len() != parts.len() {
                return false;
            }
            parts
                .iter()
                .zip(args.iter())
                .all(|(pat, arg)| match_pattern_canon(pat, arg, subst))
        }
    }
}

fn instantiate_canon(
    pattern: &Pattern,
    subst: &std::collections::HashMap<String, CanonTerm>,
) -> CanonTerm {
    match pattern {
        Pattern::Var(name) => subst
            .get(name)
            .cloned()
            .unwrap_or_else(|| CanonTerm::Atom(name.clone())),
        Pattern::Id(name) => CanonTerm::Atom(name.clone()),
        Pattern::App(name, parts) => CanonTerm::App(
            name.clone(),
            parts
                .iter()
                .map(|part| instantiate_canon(part, subst))
                .collect(),
        ),
    }
}

fn equation_rule_from_axiom(axiom: &SyGuSTerm) -> Option<EquationRule> {
    let (bound_vars, core) = peel_forall(axiom);
    let SyGuSTerm::Application(eq, args) = core else {
        return None;
    };
    if eq.get_name() != "=" || args.len() != 2 {
        return None;
    }
    let lhs = compile_pattern(&args[0], &collect_rule_vars(&args[0], &args[1], &bound_vars))?;
    let rhs = compile_pattern(&args[1], &collect_rule_vars(&args[0], &args[1], &bound_vars))?;
    Some(EquationRule { lhs, rhs })
}

fn pattern_root(pattern: &Pattern) -> Option<(String, usize)> {
    match pattern {
        Pattern::App(name, args) => Some((name.clone(), args.len())),
        _ => None,
    }
}

fn peel_forall<'a>(term: &'a SyGuSTerm) -> (Vec<String>, &'a SyGuSTerm) {
    let mut bound = Vec::new();
    let mut cur = term;
    while let SyGuSTerm::Forall(vars, body) = cur {
        bound.extend(vars.iter().map(|v| v.name.clone()));
        cur = body;
    }
    (bound, cur)
}

fn collect_rule_vars(from: &SyGuSTerm, to: &SyGuSTerm, bound_vars: &[String]) -> BTreeSet<String> {
    let mut vars = BTreeSet::new();
    collect_term_vars(from, bound_vars, &mut vars);
    collect_term_vars(to, bound_vars, &mut vars);
    vars
}

fn collect_term_vars(term: &SyGuSTerm, bound_vars: &[String], vars: &mut BTreeSet<String>) {
    match term {
        SyGuSTerm::Identifier(Identifier::Symbol(sym)) => {
            if is_var_symbol(sym, bound_vars) {
                vars.insert(sym.clone());
            }
        }
        SyGuSTerm::Application(_, args) => {
            for arg in args {
                collect_term_vars(arg, bound_vars, vars);
            }
        }
        SyGuSTerm::Annotated(inner, _) => collect_term_vars(inner, bound_vars, vars),
        SyGuSTerm::Let(bindings, body) => {
            for binding in bindings {
                collect_term_vars(&binding.term, bound_vars, vars);
            }
            collect_term_vars(body, bound_vars, vars);
        }
        SyGuSTerm::Forall(bindings, body) | SyGuSTerm::Exists(bindings, body) => {
            let mut nested = bound_vars.to_vec();
            nested.extend(bindings.iter().map(|b| b.name.clone()));
            collect_term_vars(body, nested.as_slice(), vars);
        }
        _ => {}
    }
}

fn is_var_symbol(sym: &str, bound_vars: &[String]) -> bool {
    if !bound_vars.is_empty() {
        return bound_vars.iter().any(|v| v == sym);
    }
    if sym.eq_ignore_ascii_case("true") || sym.eq_ignore_ascii_case("false") {
        return false;
    }
    if sym.contains('.') {
        return false;
    }
    sym.chars().next().is_some_and(|c| c.is_ascii_lowercase())
}

fn compile_pattern(term: &SyGuSTerm, vars: &BTreeSet<String>) -> Option<Pattern> {
    match term {
        SyGuSTerm::Identifier(Identifier::Symbol(sym)) => {
            if vars.contains(sym) {
                Some(Pattern::Var(sym.clone()))
            } else {
                Some(Pattern::Id(sym.clone()))
            }
        }
        SyGuSTerm::Identifier(id) => Some(Pattern::Id(id.to_string())),
        SyGuSTerm::Application(id, args) => Some(Pattern::App(
            id.to_string(),
            args.iter()
                .map(|arg| compile_pattern(arg, vars))
                .collect::<Option<Vec<_>>>()?,
        )),
        SyGuSTerm::Annotated(inner, _) => compile_pattern(inner, vars),
        _ => None,
    }
}
