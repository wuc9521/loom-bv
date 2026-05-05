use std::collections::hash_map::Entry;
use std::collections::BTreeMap;

use pest::Span;
use rustc_hash::FxHashMap;
use sygus_parser::ast::{Identifier, Literal as SyGuSLiteral, SyGuSCmd, SyGuSFile, SyGuSTerm};

use crate::{
    enumerate::{
        expr::OwnedExpr,
        grammar::{
            build_owned_application, for_each_candidate_tuple, for_each_size_split, MultiConfig,
            MultiRule, TemplateExpr,
        },
        value::Value,
    },
    parse::{self, deffun, new_custom_error_span, SynthProblem},
};

pub enum NullarySpec {
    Exact(Value),
    BitConstraints {
        bits: usize,
        known_bits: BTreeMap<usize, bool>,
        /// Boolean / BV constraints over the synth function, compiled with
        /// [`OwnedExpr::from_term`] (same path as PBE / ref-impl) and checked via
        /// [`OwnedExpr::eval`]. A constraint holds when evaluation yields zero
        /// (see boolean encoding in `enumerate/expr.rs` `from_term`).
        structural: Vec<OwnedExpr>,
    },
}

impl NullarySpec {
    pub fn from_file(
        file: &SyGuSFile,
        problem: &SynthProblem<'static>,
    ) -> parse::Result<Option<Self>> {
        if !problem.args.is_empty() {
            return Ok(None);
        }
        if let Some(value) = parse_target_define_fun(file, problem.name)? {
            return Ok(Some(Self::Exact(value)));
        }
        if let Some((known_bits, structural)) =
            parse_bit_constraints(file, problem.name, problem.bits)?
        {
            return Ok(Some(Self::BitConstraints {
                bits: problem.bits,
                known_bits,
                structural,
            }));
        }
        Ok(None)
    }

    fn matches(&self, value: &Value) -> bool {
        match self {
            Self::Exact(expected) => value == expected,
            Self::BitConstraints {
                bits,
                known_bits,
                structural,
            } => {
                if value.bits() != *bits {
                    return false;
                }
                if !known_bits
                    .iter()
                    .all(|(bit, expected)| value.bit(*bit) == *expected)
                {
                    return false;
                }
                structural.iter().all(|expr| {
                    expr.eval(std::slice::from_ref(value))
                        .map(|v| v.is_zero())
                        .unwrap_or(false)
                })
            }
        }
    }
}

pub fn search_nullary(
    problem: &SynthProblem<'static>,
    spec: &NullarySpec,
) -> parse::Result<OwnedExpr> {
    search_nullary_multi_nt(problem, spec)
}

#[derive(Clone)]
struct Candidate {
    node: NodeId,
    value: Value,
}

type NodeId = usize;

struct Node {
    nt_idx: usize,
    rule_idx: usize,
    children: Vec<NodeId>,
}

struct ExactGrammar<'a> {
    nts: Vec<(&'a str, Vec<ExactRule>)>,
    start: usize,
}

#[derive(Clone)]
enum ExactRule {
    Alias(usize),
    Leaf(OwnedExpr),
    Unary {
        fid: usize,
        child_nt: usize,
    },
    Binary {
        fid: usize,
        lhs_nt: usize,
        rhs_nt: usize,
    },
    Nary {
        fid: usize,
        child_nts: Vec<usize>,
    },
    GenericTemplate {
        template: TemplateExpr,
        child_nts: Vec<usize>,
        base_size: usize,
    },
}

#[derive(Default)]
struct ExactEvalCache {
    leaves: FxHashMap<OwnedExpr, Option<Value>>,
    fop1: FxHashMap<(usize, Value), Option<Value>>,
    fop2: FxHashMap<(usize, Value, Value), Option<Value>>,
    fopn: FxHashMap<(usize, Vec<Value>), Option<Value>>,
}

fn search_nullary_multi_nt(
    problem: &SynthProblem<'static>,
    spec: &NullarySpec,
) -> parse::Result<OwnedExpr> {
    let grammar = compile_exact_grammar(&MultiConfig::from_problem(problem)?);
    let nt_count = grammar.nts.len();
    let mut by_size = vec![vec![Vec::<Candidate>::new()]; nt_count];
    let mut seen = vec![FxHashMap::<Value, usize>::default(); nt_count];
    let mut nodes = Vec::<Node>::new();
    let mut eval_cache = ExactEvalCache::default();

    for size in 1.. {
        for buckets in &mut by_size {
            buckets.push(Vec::new());
        }

        for (nt_idx, (_, rules)) in grammar.nts.iter().enumerate() {
            for (rule_idx, rule) in rules.iter().enumerate() {
                match rule {
                    ExactRule::Alias(_) => {}
                    ExactRule::Leaf(expr) => {
                        if size != 1 {
                            continue;
                        }
                        if let Some(value) = eval_cache
                            .leaves
                            .entry(expr.clone())
                            .or_insert_with(|| expr.eval(&[]).ok())
                            .clone()
                        {
                            if let Some(found) = insert_multi_nt_candidate(
                                nt_idx,
                                value,
                                size,
                                &grammar,
                                spec,
                                &mut seen,
                                &mut by_size,
                                &mut nodes,
                                || Node {
                                    nt_idx,
                                    rule_idx,
                                    children: Vec::new(),
                                },
                            ) {
                                return Ok(found);
                            }
                        }
                    }
                    ExactRule::Unary { fid, child_nt } => {
                        if size < 2 {
                            continue;
                        }
                        let child_size = size - 1;
                        let children = by_size[*child_nt]
                            .get(child_size)
                            .map(Vec::as_slice)
                            .unwrap_or(&[][..])
                            .to_vec();
                        for child in &children {
                            let value = evaluate_fop1(*fid, &child.value, &mut eval_cache);
                            let Ok(value) = value else {
                                continue;
                            };
                            if let Some(found) = insert_multi_nt_candidate(
                                nt_idx,
                                value,
                                size,
                                &grammar,
                                spec,
                                &mut seen,
                                &mut by_size,
                                &mut nodes,
                                || Node {
                                    nt_idx,
                                    rule_idx,
                                    children: vec![child.node],
                                },
                            ) {
                                return Ok(found);
                            }
                        }
                    }
                    ExactRule::Binary {
                        fid,
                        lhs_nt,
                        rhs_nt,
                    } => {
                        if size < 3 {
                            continue;
                        }
                        for lhs_size in 1..(size - 1) {
                            let rhs_size = size - 1 - lhs_size;
                            let lhs_pool = by_size[*lhs_nt]
                                .get(lhs_size)
                                .map(Vec::as_slice)
                                .unwrap_or(&[][..])
                                .to_vec();
                            let rhs_pool = by_size[*rhs_nt]
                                .get(rhs_size)
                                .map(Vec::as_slice)
                                .unwrap_or(&[][..])
                                .to_vec();
                            if lhs_pool.is_empty() || rhs_pool.is_empty() {
                                continue;
                            }
                            for lhs in &lhs_pool {
                                for rhs in &rhs_pool {
                                    let value =
                                        evaluate_fop2(*fid, &lhs.value, &rhs.value, &mut eval_cache);
                                    let Ok(value) = value else {
                                        continue;
                                    };
                                    if let Some(found) = insert_multi_nt_candidate(
                                        nt_idx,
                                        value,
                                        size,
                                        &grammar,
                                        spec,
                                        &mut seen,
                                        &mut by_size,
                                        &mut nodes,
                                        || Node {
                                            nt_idx,
                                            rule_idx,
                                            children: vec![lhs.node, rhs.node],
                                        },
                                    ) {
                                        return Ok(found);
                                    }
                                }
                            }
                        }
                    }
                    ExactRule::Nary { fid, child_nts } => {
                        if size <= child_nts.len() {
                            continue;
                        }
                        let child_total = size - 1;
                        let mut staged = Vec::new();
                        let mut splits = Vec::with_capacity(child_nts.len());
                        for_each_size_split(
                            child_total,
                            child_nts.len(),
                            &mut splits,
                            &mut |sizes| {
                                let pools = child_nts
                                    .iter()
                                    .zip(sizes.iter())
                                    .map(|(child_nt, child_size)| {
                                        by_size[*child_nt]
                                            .get(*child_size)
                                            .map(Vec::as_slice)
                                            .unwrap_or(&[][..])
                                    })
                                    .collect::<Vec<_>>();
                                if pools.iter().any(|pool| pool.is_empty()) {
                                    return;
                                }
                                let mut tuple = Vec::with_capacity(child_nts.len());
                                for_each_candidate_tuple(&pools, &mut tuple, &mut |tuple| {
                                    let child_values = tuple
                                        .iter()
                                        .map(|cand| cand.value.clone())
                                        .collect::<Vec<_>>();
                                    let Ok(value) =
                                        evaluate_fopn(*fid, &child_values, &mut eval_cache)
                                    else {
                                        return;
                                    };
                                    let children =
                                        tuple.iter().map(|cand| cand.node).collect::<Vec<_>>();
                                    staged.push((value, children));
                                });
                            },
                        );

                        for (value, children) in staged {
                            if let Some(found) = insert_multi_nt_candidate(
                                nt_idx,
                                value,
                                size,
                                &grammar,
                                spec,
                                &mut seen,
                                &mut by_size,
                                &mut nodes,
                                || Node {
                                    nt_idx,
                                    rule_idx,
                                    children,
                                },
                            ) {
                                return Ok(found);
                            }
                        }
                    }
                    ExactRule::GenericTemplate {
                        template,
                        child_nts,
                        base_size,
                    } => {
                        if *base_size > size {
                            continue;
                        }
                        let child_total = size - base_size;
                        if child_nts.is_empty() {
                            if child_total == 0 {
                                if let Ok(value) =
                                    evaluate_template_value(template, &[], &mut eval_cache)
                                {
                                    if let Some(found) = insert_multi_nt_candidate(
                                        nt_idx,
                                        value,
                                        size,
                                        &grammar,
                                        spec,
                                        &mut seen,
                                        &mut by_size,
                                        &mut nodes,
                                        || Node {
                                            nt_idx,
                                            rule_idx,
                                            children: Vec::new(),
                                        },
                                    ) {
                                        return Ok(found);
                                    }
                                }
                            }
                            continue;
                        }
                        if child_total < child_nts.len() {
                            continue;
                        }
                        let mut staged = Vec::new();
                        let mut splits = Vec::with_capacity(child_nts.len());
                        for_each_size_split(
                            child_total,
                            child_nts.len(),
                            &mut splits,
                            &mut |sizes| {
                                let pools = child_nts
                                    .iter()
                                    .zip(sizes.iter())
                                    .map(|(child_nt, child_size)| {
                                        by_size[*child_nt]
                                            .get(*child_size)
                                            .map(Vec::as_slice)
                                            .unwrap_or(&[][..])
                                    })
                                    .collect::<Vec<_>>();
                                if pools.iter().any(|pool| pool.is_empty()) {
                                    return;
                                }
                                let mut tuple = Vec::with_capacity(child_nts.len());
                                for_each_candidate_tuple(&pools, &mut tuple, &mut |tuple| {
                                    let child_values = tuple
                                        .iter()
                                        .map(|cand| cand.value.clone())
                                        .collect::<Vec<_>>();
                                    let Ok(value) = evaluate_template_value(
                                        template,
                                        &child_values,
                                        &mut eval_cache,
                                    ) else {
                                        return;
                                    };
                                    let children =
                                        tuple.iter().map(|cand| cand.node).collect::<Vec<_>>();
                                    staged.push((value, children));
                                });
                            },
                        );
                        for (value, children) in staged {
                            if let Some(found) = insert_multi_nt_candidate(
                                nt_idx,
                                value,
                                size,
                                &grammar,
                                spec,
                                &mut seen,
                                &mut by_size,
                                &mut nodes,
                                || Node {
                                    nt_idx,
                                    rule_idx,
                                    children,
                                },
                            ) {
                                return Ok(found);
                            }
                        }
                    }
                }
            }
        }

        loop {
            let mut changed = false;
            for (nt_idx, (_, rules)) in grammar.nts.iter().enumerate() {
                for rule in rules {
                    let ExactRule::Alias(child_nt) = rule else {
                        continue;
                    };
                    let before = by_size[nt_idx][size].len();
                    let staged = by_size[*child_nt][size].clone();
                    for candidate in staged {
                        if let Some(found) = insert_existing_candidate(
                            nt_idx,
                            candidate,
                            size,
                            &grammar,
                            spec,
                            &mut seen,
                            &mut by_size,
                            &nodes,
                        ) {
                            return Ok(found);
                        }
                    }
                    changed |= by_size[nt_idx][size].len() > before;
                }
            }
            if !changed {
                break;
            }
        }
    }

    unreachable!("nullary enumeration should either find a solution or diverge");
}

fn insert_existing_candidate(
    nt_idx: usize,
    candidate: Candidate,
    size: usize,
    grammar: &ExactGrammar<'_>,
    spec: &NullarySpec,
    seen: &mut [FxHashMap<Value, usize>],
    by_size: &mut [Vec<Vec<Candidate>>],
    nodes: &[Node],
) -> Option<OwnedExpr> {
    if nt_idx == grammar.start && spec.matches(&candidate.value) {
        return materialize_node(candidate.node, grammar, nodes);
    }
    match seen[nt_idx].entry(candidate.value.clone()) {
        Entry::Occupied(_) => None,
        Entry::Vacant(entry) => {
            entry.insert(size);
            by_size[nt_idx][size].push(candidate);
            None
        }
    }
}

fn insert_multi_nt_candidate(
    nt_idx: usize,
    value: Value,
    size: usize,
    grammar: &ExactGrammar<'_>,
    spec: &NullarySpec,
    seen: &mut [FxHashMap<Value, usize>],
    by_size: &mut [Vec<Vec<Candidate>>],
    nodes: &mut Vec<Node>,
    build_node: impl FnOnce() -> Node,
) -> Option<OwnedExpr> {
    if nt_idx == grammar.start && spec.matches(&value) {
        let node = intern_node(nodes, build_node());
        return materialize_node(node, grammar, nodes);
    }
    match seen[nt_idx].entry(value.clone()) {
        Entry::Occupied(_) => None,
        Entry::Vacant(entry) => {
            entry.insert(size);
            let node = intern_node(nodes, build_node());
            by_size[nt_idx][size].push(Candidate { node, value });
            None
        }
    }
}

fn intern_node(nodes: &mut Vec<Node>, node: Node) -> NodeId {
    let id = nodes.len();
    nodes.push(node);
    id
}

fn materialize_node(id: NodeId, grammar: &ExactGrammar<'_>, nodes: &[Node]) -> Option<OwnedExpr> {
    let node = &nodes[id];
    match &grammar.nts[node.nt_idx].1[node.rule_idx] {
        ExactRule::Alias(_) => materialize_node(node.children[0], grammar, nodes),
        ExactRule::Leaf(expr) => Some(expr.clone()),
        ExactRule::Unary { fid, .. } => Some(OwnedExpr::Fop1Dyn(
            *fid,
            Box::new(materialize_node(node.children[0], grammar, nodes)?),
        )),
        ExactRule::Binary { fid, .. } => Some(OwnedExpr::Fop2Dyn(
            *fid,
            Box::new(materialize_node(node.children[0], grammar, nodes)?),
            Box::new(materialize_node(node.children[1], grammar, nodes)?),
        )),
        ExactRule::Nary { fid, .. } => Some(OwnedExpr::FopDyn(
            *fid,
            node.children
                .iter()
                .map(|child| materialize_node(*child, grammar, nodes))
                .collect::<Option<Vec<_>>>()?,
        )),
        ExactRule::GenericTemplate { template, .. } => {
            let child_exprs = node
                .children
                .iter()
                .map(|child| materialize_node(*child, grammar, nodes))
                .collect::<Option<Vec<_>>>()?;
            template.instantiate(&child_exprs).ok()
        }
    }
}

fn compile_exact_grammar(grammar: &MultiConfig<'static>) -> ExactGrammar<'static> {
    let nts = grammar
        .nts
        .iter()
        .map(|(name, rules)| {
            let compiled = rules
                .iter()
                .map(|rule| match rule {
                    MultiRule::Alias(nt) => ExactRule::Alias(*nt),
                    MultiRule::Template {
                        template,
                        child_nts,
                        base_size,
                    } => compile_exact_rule(template, child_nts, *base_size),
                })
                .collect();
            (*name, compiled)
        })
        .collect();
    ExactGrammar {
        nts,
        start: grammar.start,
    }
}

fn compile_exact_rule(template: &TemplateExpr, child_nts: &[usize], base_size: usize) -> ExactRule {
    if child_nts.is_empty() {
        if let TemplateExpr::Leaf(expr) = template {
            return ExactRule::Leaf(expr.clone());
        }
    }
    let TemplateExpr::App(id, parts) = template else {
        return ExactRule::GenericTemplate {
            template: template.clone(),
            child_nts: child_nts.to_vec(),
            base_size,
        };
    };
    if parts.len() != child_nts.len() {
        return ExactRule::GenericTemplate {
            template: template.clone(),
            child_nts: child_nts.to_vec(),
            base_size,
        };
    }
    if !parts
        .iter()
        .enumerate()
        .all(|(idx, part)| matches!(part, TemplateExpr::Slot(slot) if *slot == idx))
    {
        return ExactRule::GenericTemplate {
            template: template.clone(),
            child_nts: child_nts.to_vec(),
            base_size,
        };
    }
    let Some(fid) = deffun::ENV.lookup(id.get_name(), parts.len()) else {
        return ExactRule::GenericTemplate {
            template: template.clone(),
            child_nts: child_nts.to_vec(),
            base_size,
        };
    };
    match parts.len() {
        1 => ExactRule::Unary {
            fid,
            child_nt: child_nts[0],
        },
        2 => ExactRule::Binary {
            fid,
            lhs_nt: child_nts[0],
            rhs_nt: child_nts[1],
        },
        _ => ExactRule::Nary {
            fid,
            child_nts: child_nts.to_vec(),
        },
    }
}

fn evaluate_template_value(
    template: &TemplateExpr,
    args: &[Value],
    cache: &mut ExactEvalCache,
) -> Result<Value, ()> {
    match template {
        TemplateExpr::Slot(i) => Ok(args[*i].clone()),
        TemplateExpr::Leaf(expr) => cache
            .leaves
            .entry(expr.clone())
            .or_insert_with(|| expr.eval(&[]).ok())
            .clone()
            .ok_or(()),
        TemplateExpr::App(id, parts) => {
            let values = parts
                .iter()
                .map(|part| evaluate_template_value(part, args, cache))
                .collect::<Result<Vec<_>, _>>()?;
            let const_args = values
                .iter()
                .cloned()
                .map(OwnedExpr::Const)
                .collect::<Vec<_>>();
            build_owned_application(id, &const_args)
                .ok()
                .and_then(|expr| expr.eval(&[]).ok())
                .ok_or(())
        }
    }
}

fn evaluate_fop1(fid: usize, arg: &Value, cache: &mut ExactEvalCache) -> Result<Value, ()> {
    cache
        .fop1
        .entry((fid, arg.clone()))
        .or_insert_with(|| deffun::ENV.apply(fid, 1).eval(std::slice::from_ref(arg)).ok())
        .clone()
        .ok_or(())
}

fn evaluate_fop2(
    fid: usize,
    lhs: &Value,
    rhs: &Value,
    cache: &mut ExactEvalCache,
) -> Result<Value, ()> {
    let args = [lhs.clone(), rhs.clone()];
    cache
        .fop2
        .entry((fid, lhs.clone(), rhs.clone()))
        .or_insert_with(|| deffun::ENV.apply(fid, 2).eval(&args).ok())
        .clone()
        .ok_or(())
}

fn evaluate_fopn(fid: usize, args: &[Value], cache: &mut ExactEvalCache) -> Result<Value, ()> {
    cache
        .fopn
        .entry((fid, args.to_vec()))
        .or_insert_with(|| deffun::ENV.apply(fid, args.len()).eval(args).ok())
        .clone()
        .ok_or(())
}

fn parse_target_define_fun(file: &SyGuSFile, target_name: &str) -> parse::Result<Option<Value>> {
    for cmd in &file.cmds {
        if let SyGuSCmd::DefineFun(name, args, _, body) = cmd {
            if name == target_name && args.is_empty() {
                let expr = OwnedExpr::from_term(body, &[])?;
                let value = expr.eval(&[]).map_err(|_| {
                    new_custom_error_span(
                        format!("failed to evaluate nullary define-fun {}", target_name),
                        empty_span(),
                    )
                })?;
                return Ok(Some(value));
            }
        }
    }
    Ok(None)
}

fn constraint_mentions_target(term: &SyGuSTerm, target_name: &str) -> bool {
    match term {
        SyGuSTerm::Identifier(id) => id.get_name() == target_name,
        SyGuSTerm::Annotated(inner, _) => constraint_mentions_target(inner, target_name),
        SyGuSTerm::Application(_, args) => args
            .iter()
            .any(|a| constraint_mentions_target(a, target_name)),
        SyGuSTerm::Let(bindings, body) => {
            bindings
                .iter()
                .any(|b| constraint_mentions_target(&b.term, target_name))
                || constraint_mentions_target(body, target_name)
        }
        SyGuSTerm::Forall(_, body) | SyGuSTerm::Exists(_, body) => {
            constraint_mentions_target(body, target_name)
        }
        _ => false,
    }
}

fn validate_structural_shape(term: &SyGuSTerm, target: &str) -> parse::Result<()> {
    match term {
        SyGuSTerm::Annotated(inner, _) => validate_structural_shape(inner, target),
        SyGuSTerm::Literal(SyGuSLiteral::Bool(_)) => Ok(()),
        SyGuSTerm::Literal(SyGuSLiteral::Numeral(n)) if *n == 0 || *n == 1 => Ok(()),
        SyGuSTerm::Literal(SyGuSLiteral::BinConst(s)) => {
            let bits: String = s.chars().filter(|c| *c == '0' || *c == '1').collect();
            if bits.is_empty() {
                Err(new_custom_error_span(
                    "structural constraints: expected #b... bitvector literal".into(),
                    empty_span(),
                ))
            } else {
                Ok(())
            }
        }
        SyGuSTerm::Literal(_) => Err(new_custom_error_span(
            "structural constraints: unsupported literal".into(),
            empty_span(),
        )),
        SyGuSTerm::Identifier(id) => {
            let n = id.get_name();
            if n == target || n.eq_ignore_ascii_case("true") || n.eq_ignore_ascii_case("false") {
                Ok(())
            } else {
                Err(new_custom_error_span(
                    format!("structural constraints: unsupported identifier `{n}`"),
                    empty_span(),
                ))
            }
        }
        SyGuSTerm::Application(id, args) => match id.get_name() {
            "not" if args.len() == 1 => validate_structural_shape(&args[0], target),
            "and" | "or" => args
                .iter()
                .try_for_each(|a| validate_structural_shape(a, target)),
            "=" if args.len() == 2 => {
                validate_structural_shape(&args[0], target)?;
                validate_structural_shape(&args[1], target)?;
                Ok(())
            }
            _ if extract_on_phi_range(term, target).is_some() => Ok(()),
            _ => Err(new_custom_error_span(
                format!(
                    "structural constraints: unsupported operator `{}`",
                    id.get_name()
                ),
                empty_span(),
            )),
        },
        _ => Err(new_custom_error_span(
            "structural constraints: unsupported SyGuS term shape".into(),
            empty_span(),
        )),
    }
}

/// Map SyGuS boolean constants to the 1-bit encoding used by [`OwnedExpr::from_term`]
/// (`and` / `or` / `not` / `ite`): zero means true, non-zero means false.
fn rewrite_constraint_literals_for_owned_eval(term: &SyGuSTerm) -> SyGuSTerm {
    fn xor_b0_b0() -> SyGuSTerm {
        SyGuSTerm::Application(
            Identifier::Symbol("xor".into()),
            vec![
                SyGuSTerm::Literal(SyGuSLiteral::BinConst("0".into())),
                SyGuSTerm::Literal(SyGuSLiteral::BinConst("0".into())),
            ],
        )
    }
    fn xor_b0_b1() -> SyGuSTerm {
        SyGuSTerm::Application(
            Identifier::Symbol("xor".into()),
            vec![
                SyGuSTerm::Literal(SyGuSLiteral::BinConst("0".into())),
                SyGuSTerm::Literal(SyGuSLiteral::BinConst("1".into())),
            ],
        )
    }
    match term {
        SyGuSTerm::Identifier(id) if id.get_name().eq_ignore_ascii_case("true") => xor_b0_b0(),
        SyGuSTerm::Identifier(id) if id.get_name().eq_ignore_ascii_case("false") => xor_b0_b1(),
        SyGuSTerm::Literal(SyGuSLiteral::Bool(true)) => xor_b0_b0(),
        SyGuSTerm::Literal(SyGuSLiteral::Bool(false)) => xor_b0_b1(),
        SyGuSTerm::Literal(SyGuSLiteral::Numeral(0)) => xor_b0_b1(),
        SyGuSTerm::Literal(SyGuSLiteral::Numeral(1)) => xor_b0_b0(),
        SyGuSTerm::Annotated(inner, attrs) => SyGuSTerm::Annotated(
            Box::new(rewrite_constraint_literals_for_owned_eval(inner)),
            attrs.clone(),
        ),
        SyGuSTerm::Application(id, args) => SyGuSTerm::Application(
            id.clone(),
            args.iter()
                .map(rewrite_constraint_literals_for_owned_eval)
                .collect(),
        ),
        SyGuSTerm::Exists(_, _) | SyGuSTerm::Forall(_, _) | SyGuSTerm::Let(_, _) => term.clone(),
        _ => term.clone(),
    }
}

fn index_numeral(idx: &sygus_parser::ast::Index) -> Option<usize> {
    match idx {
        sygus_parser::ast::Index::Numeral(v) => Some(*v),
        sygus_parser::ast::Index::Symbol(_) => None,
    }
}

fn extract_indices_from_identifier(id: &Identifier) -> Option<(usize, usize)> {
    match id {
        Identifier::Indexed(sym, idxs) if sym == "extract" && idxs.len() >= 2 => {
            match (index_numeral(&idxs[0]), index_numeral(&idxs[1])) {
                (Some(hi), Some(lo)) => Some((hi, lo)),
                _ => None,
            }
        }
        Identifier::Indexed(sym, idxs) if sym == "_" && idxs.len() >= 3 => {
            match (&idxs[0], index_numeral(&idxs[1]), index_numeral(&idxs[2])) {
                (sygus_parser::ast::Index::Symbol(op), Some(hi), Some(lo)) if op == "extract" => {
                    Some((hi, lo))
                }
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
            ["_", "extract", hi, lo] => match (hi.parse::<usize>(), lo.parse::<usize>()) {
                (Ok(hi), Ok(lo)) => Some((hi, lo)),
                _ => None,
            },
            ["extract", hi, lo] => match (hi.parse::<usize>(), lo.parse::<usize>()) {
                (Ok(hi), Ok(lo)) => Some((hi, lo)),
                _ => None,
            },
            _ => None,
        }
    })
}

fn extract_on_phi_range(term: &SyGuSTerm, target: &str) -> Option<(usize, usize)> {
    match term {
        SyGuSTerm::Annotated(inner, _) => extract_on_phi_range(inner, target),
        SyGuSTerm::Application(id, args) if args.len() == 1 => {
            if !matches!(&args[0], SyGuSTerm::Identifier(var) if var.get_name() == target) {
                return None;
            }
            extract_indices_from_identifier(id)
        }
        _ => None,
    }
}

fn parse_bit_constraints(
    file: &SyGuSFile,
    target_name: &str,
    target_bits: usize,
) -> parse::Result<Option<(BTreeMap<usize, bool>, Vec<OwnedExpr>)>> {
    let mut known_bits = BTreeMap::<usize, bool>::new();
    let mut structural = Vec::new();
    let synth_env = [(target_name, target_bits as u64)];
    let mut found_any = false;

    for cmd in &file.cmds {
        if let SyGuSCmd::Constraint(c) = cmd {
            if let Some((bit, value)) = parse_bit_constraint(c, target_name) {
                if bit >= target_bits {
                    continue;
                }
                found_any = true;
                if let Some(old) = known_bits.get(&bit).copied() {
                    if old != value {
                        return Err(new_custom_error_span(
                            format!("Conflicting constraints on bit {} of {}", bit, target_name),
                            empty_span(),
                        ));
                    }
                } else {
                    known_bits.insert(bit, value);
                }
            } else if constraint_mentions_target(c, target_name) {
                validate_structural_shape(c, target_name)?;
                let rewritten = rewrite_constraint_literals_for_owned_eval(c);
                structural.push(OwnedExpr::from_term(&rewritten, &synth_env)?);
                found_any = true;
            }
        }
    }

    Ok(found_any.then_some((known_bits, structural)))
}

fn parse_bit_constraint(term: &SyGuSTerm, target_name: &str) -> Option<(usize, bool)> {
    if let SyGuSTerm::Annotated(inner, _) = term {
        return parse_bit_constraint(inner, target_name);
    }
    let SyGuSTerm::Application(eq, args) = term else {
        return None;
    };
    if eq.get_name() != "=" || args.len() != 2 {
        return None;
    }
    extract_bit_of_target(&args[0], target_name)
        .zip(bit_literal(&args[1]))
        .or_else(|| extract_bit_of_target(&args[1], target_name).zip(bit_literal(&args[0])))
}

fn bit_literal(term: &SyGuSTerm) -> Option<bool> {
    match term {
        SyGuSTerm::Annotated(inner, _) => bit_literal(inner),
        SyGuSTerm::Identifier(id) => {
            let name = id.get_name();
            if name.eq_ignore_ascii_case("true") {
                Some(true)
            } else if name.eq_ignore_ascii_case("false") {
                Some(false)
            } else {
                let bits: String = name.chars().filter(|c| *c == '0' || *c == '1').collect();
                if bits.is_empty() {
                    None
                } else {
                    Some(bits.chars().last().unwrap() == '1')
                }
            }
        }
        SyGuSTerm::Literal(SyGuSLiteral::Bool(v)) => Some(*v),
        SyGuSTerm::Literal(SyGuSLiteral::Numeral(v)) => match *v {
            0 => Some(false),
            1 => Some(true),
            _ => None,
        },
        SyGuSTerm::Literal(SyGuSLiteral::BinConst(v)) => {
            let bits: String = v.chars().filter(|c| *c == '0' || *c == '1').collect();
            if bits.is_empty() {
                None
            } else {
                Some(bits.chars().last().unwrap() == '1')
            }
        }
        _ => None,
    }
}

fn extract_bit_of_target(term: &SyGuSTerm, target_name: &str) -> Option<usize> {
    let (hi, lo) = extract_on_phi_range(term, target_name)?;
    (hi == lo).then_some(hi)
}

fn empty_span() -> Span<'static> {
    Span::new("", 0, 0).expect("empty span should be valid")
}
