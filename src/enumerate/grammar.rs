use std::collections::HashMap;

use pest::Span;
use sygus_parser::ast::{Identifier, SyGuSGTerm, SyGuSTerm};

use crate::{
    all_ops,
    parse::{self, deffun, new_custom_error_span, SynthProblem},
    smt_name_of,
};

use super::expr::OwnedExpr;

#[derive(Clone)]
pub enum TemplateExpr {
    Slot(usize),
    Leaf(OwnedExpr),
    App(Identifier, Vec<TemplateExpr>),
}

impl TemplateExpr {
    pub fn instantiate(&self, args: &[OwnedExpr]) -> parse::Result<OwnedExpr> {
        match self {
            Self::Slot(i) => Ok(args[*i].clone()),
            Self::Leaf(expr) => Ok(expr.clone()),
            Self::App(id, parts) => {
                let args = parts
                    .iter()
                    .map(|part| part.instantiate(args))
                    .collect::<parse::Result<Vec<_>>>()?;
                build_owned_application(id, &args)
            }
        }
    }

    pub fn output_bits(&self) -> usize {
        match self {
            TemplateExpr::Slot(_) => 1,
            TemplateExpr::Leaf(expr) => expr.width(),
            TemplateExpr::App(id, parts) => deffun::ENV
                .lookup(id.get_name(), parts.len())
                .map(|fid| deffun::ENV.ret_bits(fid))
                .unwrap_or(1),
        }
    }
}

/// Operator-specific search-time metadata. Detected once at grammar
/// compile time by looking at the outermost `App` of the rule template.
/// Algorithm consumers (currently the enumeration engine,
/// soon `algo::Algo`) use this to prune the bottom-up enumeration:
///
/// - `commutative`: with two same-NT children, only iterate `i ≤ size/2`.
/// - `idempotent`: additionally skip `e == e` pairs (e.g. `a & a = a`).
/// - `nonzero_rhs`: skip candidate tuples whose rhs evaluates to 0 (UDiv,
///   URem, SDiv, SRem).
/// - `shift_rhs_literal`: when present, only consider size-1 leaves on the
///   rhs (matches the shift-by-symbol restriction).
#[derive(Clone, Copy, Default, Debug)]
pub struct RuleClass {
    pub commutative: bool,
    pub idempotent: bool,
    pub nonzero_rhs: bool,
    pub shift_rhs_literal: bool,
}

#[derive(Clone)]
pub enum Rule {
    Alias(usize),
    Template {
        template: TemplateExpr,
        child_nts: Vec<usize>,
        base_size: usize,
        class: RuleClass,
    },
    /// ChatGPT-suggested subexpression injected at a fixed size (currently
    /// always size 1). Only emitted when `problem.chatgpt_exprs` is
    /// non-empty.
    ChatGPT {
        expr: OwnedExpr,
        size: usize,
    },
}

pub struct Config<'a> {
    pub nts: Vec<(&'a str, Vec<Rule>)>,
    pub start: usize,
}

impl<'a> Config<'a> {
    pub fn from_problem(problem: &SynthProblem<'static>) -> parse::Result<Config<'static>> {
        let nt_lookup = problem
            .cfg
            .iter()
            .enumerate()
            .map(|(idx, nt)| (nt.0, idx))
            .collect::<HashMap<_, _>>();
        let env = problem
            .arg_decls
            .iter()
            .map(|sv| {
                let name: &str = Box::leak(sv.name.clone().into_boxed_str());
                let bits = crate::parse::SortAliases::default()
                    .parse_sort_width(&sv.sort)
                    .unwrap_or(1) as u64;
                (name, bits)
            })
            .collect::<Vec<_>>();
        let mut nts = Vec::with_capacity(problem.cfg.len());
        for (idx, nt) in problem.cfg.iter().enumerate() {
            let mut rules = Vec::new();
            // Inject ChatGPT suggestions only into the start non-terminal.
            // the legacy single-NT engine injected ChatGPT rules at the
            // single (start) NT; preserve that semantics here.
            if idx == 0 {
                for expr in problem.chatgpt_exprs.iter() {
                    rules.push(Rule::ChatGPT {
                        expr: expr.clone(),
                        size: 1,
                    });
                }
            }
            for gterm in &nt.1 {
                let term = match gterm {
                    SyGuSGTerm::SyGuSTerm(term) => term,
                    SyGuSGTerm::Constant(_) | SyGuSGTerm::Variable(_) => continue,
                };
                match term_to_rule(term, &nt_lookup, &env, problem.axioms.as_ref())? {
                    Some(rule) => rules.push(rule),
                    None => {}
                }
            }
            nts.push((nt.0, rules));
        }
        Ok(Config { nts, start: 0 })
    }
}

/// Operator-class metadata for the standard BV ops. Maps SMT-LIB names to
/// their commutativity / idempotency / non-zero-rhs / shift-rhs-literal
/// flags. Anything not matched here defaults to no specialisation.
fn classify_op(op: &str, child_nts: &[usize]) -> RuleClass {
    // Symmetry shortcuts only kick in when both binary children come from
    // the same non-terminal — otherwise the child pools are disjoint and
    // the i ≤ size/2 trick would *miss* candidates.
    let same_nt_pair = child_nts.len() == 2 && child_nts[0] == child_nts[1];
    match op {
        "bvadd" | "bvmul" | "bvxor" => RuleClass {
            commutative: same_nt_pair,
            ..Default::default()
        },
        "bvand" | "bvor" => RuleClass {
            commutative: same_nt_pair,
            idempotent: same_nt_pair,
            ..Default::default()
        },
        "bvudiv" | "bvurem" | "bvsdiv" | "bvsrem" => RuleClass {
            nonzero_rhs: child_nts.len() == 2,
            ..Default::default()
        },
        "bvlshr" | "bvashr" | "bvshl" => RuleClass {
            shift_rhs_literal: child_nts.len() == 2,
            ..Default::default()
        },
        _ => RuleClass::default(),
    }
}

fn term_to_rule(
    term: &SyGuSTerm,
    nt_lookup: &HashMap<&str, usize>,
    env: &[(&str, u64)],
    _axioms: Option<&crate::parse::axiom::AxiomRewriter>,
) -> parse::Result<Option<Rule>> {
    fn parse_identifier_atom(
        id: &Identifier,
        env: &[(&str, u64)],
    ) -> parse::Result<Option<OwnedExpr>> {
        let name = id.get_name();
        if env.iter().any(|(arg, _)| *arg == name) {
            Ok(Some(OwnedExpr::from_term(
                &SyGuSTerm::Identifier(id.clone()),
                env,
            )?))
        } else if name.eq_ignore_ascii_case("true")
            || name.eq_ignore_ascii_case("false")
            || name.starts_with('#')
        {
            Ok(Some(OwnedExpr::from_term(
                &SyGuSTerm::Identifier(id.clone()),
                env,
            )?))
        } else if deffun::ENV.lookup(name, 0).is_some() {
            Ok(Some(OwnedExpr::from_term(
                &SyGuSTerm::Identifier(id.clone()),
                env,
            )?))
        } else {
            Ok(None)
        }
    }

    match term {
        SyGuSTerm::Identifier(id) => {
            if let Some(child_nt) = nt_lookup.get(id.get_name()).copied() {
                Ok(Some(Rule::Alias(child_nt)))
            } else if let Some(atom) = parse_identifier_atom(id, env)? {
                Ok(Some(Rule::Template {
                    template: TemplateExpr::Leaf(atom),
                    child_nts: Vec::new(),
                    base_size: 1,
                    class: RuleClass::default(),
                }))
            } else {
                Err(new_custom_error_span(
                    format!("Enumeration: unsupported grammar symbol {}", id),
                    empty_span(),
                ))
            }
        }
        SyGuSTerm::Literal(lit) => {
            let atom = OwnedExpr::from_term(&SyGuSTerm::Literal(lit.clone()), env)?;
            Ok(Some(Rule::Template {
                template: TemplateExpr::Leaf(atom),
                child_nts: Vec::new(),
                base_size: 1,
                class: RuleClass::default(),
            }))
        }
        SyGuSTerm::Application(_, _) | SyGuSTerm::Annotated(_, _) => {
            let (template, child_nts, base_size) = template_from_term(term, nt_lookup, env)?;
            let class = head_op_name(term)
                .map(|op| classify_op(op, &child_nts))
                .unwrap_or_default();
            Ok(Some(Rule::Template {
                template,
                child_nts,
                base_size,
                class,
            }))
        }
        _ => Err(new_custom_error_span(
            format!("Enumeration: unsupported grammar term {}", term),
            empty_span(),
        )),
    }
}

/// Walk through `Annotated` wrappers to find the head operator name.
fn head_op_name(term: &SyGuSTerm) -> Option<&str> {
    match term {
        SyGuSTerm::Application(id, _) => Some(id.get_name()),
        SyGuSTerm::Annotated(inner, _) => head_op_name(inner),
        _ => None,
    }
}

fn template_from_term(
    term: &SyGuSTerm,
    nt_lookup: &HashMap<&str, usize>,
    env: &[(&str, u64)],
) -> parse::Result<(TemplateExpr, Vec<usize>, usize)> {
    match term {
        SyGuSTerm::Identifier(id) => {
            if let Some(child_nt) = nt_lookup.get(id.get_name()).copied() {
                Ok((TemplateExpr::Slot(0), vec![child_nt], 0))
            } else {
                Ok((
                    TemplateExpr::Leaf(OwnedExpr::from_term(term, env)?),
                    Vec::new(),
                    1,
                ))
            }
        }
        SyGuSTerm::Literal(_) => Ok((
            TemplateExpr::Leaf(OwnedExpr::from_term(term, env)?),
            Vec::new(),
            1,
        )),
        SyGuSTerm::Annotated(inner, _) => template_from_term(inner, nt_lookup, env),
        SyGuSTerm::Application(id, args) => {
            let mut child_nts = Vec::new();
            let mut base_size = 1;
            let mut rendered_args = Vec::with_capacity(args.len());
            for arg in args {
                let (template, mut nts, size) = template_from_term(arg, nt_lookup, env)?;
                let offset = child_nts.len();
                rendered_args.push(template.shift_slots(offset));
                child_nts.append(&mut nts);
                base_size += size;
            }
            Ok((
                TemplateExpr::App(id.clone(), rendered_args),
                child_nts,
                base_size,
            ))
        }
        _ => Err(new_custom_error_span(
            format!("Enumeration: unsupported grammar term {}", term),
            empty_span(),
        )),
    }
}

impl TemplateExpr {
    /// Renumber every `Slot(i)` reference in this template to `Slot(i + offset)`.
    /// Used when stitching a child template into a parent that already
    /// consumed `offset` slot indices.
    pub fn shift_slots(self, offset: usize) -> TemplateExpr {
        match self {
            TemplateExpr::Slot(i) => TemplateExpr::Slot(i + offset),
            TemplateExpr::Leaf(expr) => TemplateExpr::Leaf(expr),
            TemplateExpr::App(id, args) => TemplateExpr::App(
                id,
                args.into_iter().map(|arg| arg.shift_slots(offset)).collect(),
            ),
        }
    }
}

pub fn build_owned_application(id: &Identifier, args: &[OwnedExpr]) -> parse::Result<OwnedExpr> {
    fn index_numeral(idx: &sygus_parser::ast::Index) -> Option<u64> {
        match idx {
            sygus_parser::ast::Index::Numeral(v) => Some(*v as u64),
            sygus_parser::ast::Index::Symbol(_) => None,
        }
    }

    fn extract_indices(id: &Identifier) -> Option<(u64, u64)> {
        match id {
            Identifier::Indexed(sym, idxs) if sym == "_" && idxs.len() >= 3 => {
                match (&idxs[0], index_numeral(&idxs[1]), index_numeral(&idxs[2])) {
                    (sygus_parser::ast::Index::Symbol(op), Some(hi), Some(lo))
                        if op == "extract" && hi >= lo =>
                    {
                        Some((hi, lo))
                    }
                    _ => None,
                }
            }
            Identifier::Indexed(sym, idxs) if sym == "extract" && idxs.len() >= 2 => {
                match (index_numeral(&idxs[0]), index_numeral(&idxs[1])) {
                    (Some(hi), Some(lo)) if hi >= lo => Some((hi, lo)),
                    _ => None,
                }
            }
            _ => None,
        }
        .or_else(|| {
            let text = id.to_string();
            let parts = text
                .trim_matches(|c| c == '(' || c == ')')
                .split_whitespace()
                .collect::<Vec<_>>();
            match parts.as_slice() {
                ["_", "extract", hi, lo] => match (hi.parse::<u64>(), lo.parse::<u64>()) {
                    (Ok(hi), Ok(lo)) if hi >= lo => Some((hi, lo)),
                    _ => None,
                },
                _ => None,
            }
        })
    }

    let opname = id.get_name();
    if args.len() == 1 {
        if let Some((hi, lo)) = extract_indices(id) {
            return Ok(OwnedExpr::Extract(Box::new(args[0].clone()), hi, lo));
        }
    }
    if opname == "concat" && args.len() >= 2 {
        let mut acc = args.last().unwrap().clone();
        for arg in args[..args.len() - 1].iter().rev() {
            acc = OwnedExpr::Concat(Box::new(arg.clone()), Box::new(acc));
        }
        return Ok(acc);
    }
    macro_rules! operator1 {
        ($opn:expr, $n:ident) => {
            if opname == $opn && args.len() == 1 {
                return Ok(OwnedExpr::$n(Box::new(args[0].clone())));
            }
        };
    }
    macro_rules! operator2 {
        ($opn:expr, $n:ident) => {
            if opname == $opn && args.len() == 2 {
                return Ok(OwnedExpr::$n(
                    Box::new(args[0].clone()),
                    Box::new(args[1].clone()),
                ));
            }
        };
    }
    macro_rules! foreach_op {
        (1, $op:ident) => {
            operator1!(smt_name_of![$op], $op);
        };
        (2, $op:ident) => {
            operator2!(smt_name_of![$op], $op);
        };
    }
    all_ops!(arity);
    operator2!("bvule", BVule);
    operator2!("bvult", BVult);
    operator2!("bvsle", BVsle);
    operator2!("bvslt", BVslt);
    if opname == "bvugt" && args.len() == 2 {
        return Ok(OwnedExpr::BVult(Box::new(args[1].clone()), Box::new(args[0].clone())));
    }
    if opname == "bvuge" && args.len() == 2 {
        return Ok(OwnedExpr::BVule(Box::new(args[1].clone()), Box::new(args[0].clone())));
    }
    if opname == "bvsgt" && args.len() == 2 {
        return Ok(OwnedExpr::BVslt(Box::new(args[1].clone()), Box::new(args[0].clone())));
    }
    if opname == "bvsge" && args.len() == 2 {
        return Ok(OwnedExpr::BVsle(Box::new(args[1].clone()), Box::new(args[0].clone())));
    }
    operator1!("not", Not);
    if opname == "and" && args.len() >= 2 {
        let mut it = args.iter();
        let mut acc = it.next().unwrap().clone();
        for a in it {
            acc = OwnedExpr::Or(Box::new(acc), Box::new(a.clone()));
        }
        return Ok(acc);
    }
    if opname == "or" && args.len() >= 2 {
        let mut it = args.iter();
        let mut acc = it.next().unwrap().clone();
        for a in it {
            acc = OwnedExpr::And(Box::new(acc), Box::new(a.clone()));
        }
        return Ok(acc);
    }
    if opname == "xor" && args.len() >= 2 {
        let mut it = args.iter();
        let mut acc = it.next().unwrap().clone();
        for a in it {
            acc = OwnedExpr::Xor(Box::new(acc), Box::new(a.clone()));
        }
        return Ok(acc);
    }
    operator2!("=", Xor);
    if opname == "ite" && args.len() == 3 {
        return Ok(OwnedExpr::Ite(
            Box::new(args[0].clone()),
            Box::new(args[1].clone()),
            Box::new(args[2].clone()),
        ));
    }
    if args.len() == 1 {
        if let Some(fid) = deffun::ENV.lookup(opname, 1) {
            return Ok(OwnedExpr::Fop1Dyn(fid, Box::new(args[0].clone())));
        }
    }
    if args.len() == 2 {
        if let Some(fid) = deffun::ENV.lookup(opname, 2) {
            return Ok(OwnedExpr::Fop2Dyn(
                fid,
                Box::new(args[0].clone()),
                Box::new(args[1].clone()),
            ));
        }
    }
    if let Some(fid) = deffun::ENV.lookup(opname, args.len()) {
        return Ok(OwnedExpr::FopDyn(fid, args.to_vec()));
    }
    Err(new_custom_error_span(
        format!("Unrecongnized Expression: ({} ...)", opname),
        empty_span(),
    ))
}

pub fn for_each_size_split(
    total: usize,
    arity: usize,
    sizes: &mut Vec<usize>,
    f: &mut impl FnMut(&[usize]),
) {
    if arity == 0 {
        if total == 0 {
            f(sizes);
        }
        return;
    }
    if arity == 1 {
        sizes.push(total);
        f(sizes);
        sizes.pop();
        return;
    }
    let min_rest = arity - 1;
    for first in 1..=(total - min_rest) {
        sizes.push(first);
        for_each_size_split(total - first, arity - 1, sizes, f);
        sizes.pop();
    }
}

pub fn for_each_candidate_tuple<'a, T>(
    candidate_pools: &[&'a [T]],
    tuple: &mut Vec<&'a T>,
    f: &mut impl FnMut(&[&'a T]),
) {
    if tuple.len() == candidate_pools.len() {
        f(tuple);
        return;
    }
    let idx = tuple.len();
    for candidate in candidate_pools[idx] {
        tuple.push(candidate);
        for_each_candidate_tuple(candidate_pools, tuple, f);
        tuple.pop();
    }
}

fn empty_span() -> Span<'static> {
    Span::new("", 0, 0).expect("empty span should be valid")
}
