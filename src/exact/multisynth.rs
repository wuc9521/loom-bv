//! Multi-synth-fun closure-constraint solver.
//!
//! Pattern detected:
//!   * Two nullary synth-funs both returning the same BV sort.  One has a
//!     real grammar (call it `g`); the other has only `(Constant <sort>)`
//!     (call it `cfg.rhs.S`).
//!   * Exactly one closure constraint of shape `(= g cfg.rhs.S)`.
//!   * Zero or more bit-extract label constraints on `cfg.rhs.S` of the form
//!     `(= ((_ extract i i) cfg.rhs.S) #b0|#b1)`.
//!
//! The closure constraint forces `cfg.rhs.S` to be a fixed point of g's
//! productions, evaluated using `cfg.rhs.S`'s own value for the recursive
//! reference.  The LFP encodes "S parses (sample, i, j)" for each cell.
//!
//! Search:
//!   * Enumerate candidate `g` terms via the grammar, smallest-first.
//!   * For each candidate, compute the LFP of `cfg.rhs.S` by iteration
//!     (start at 0, repeatedly evaluate g with the previous value, stop at
//!     fixed point or word-length+1 iterations).
//!   * Check label bits; if all match, return the solution.
//!
//! No Int, no datatypes, no recursive functions — pure BV throughout.

use sygus_parser::ast::{GrammarDef, Identifier, Literal, Sort, SortedVar, SyGuSCmd, SyGuSFile, SyGuSTerm};

use crate::enumerate::grammar::MultiConfig;
use crate::enumerate::value::Value;
use crate::info;
use crate::parse::cfg::Cfg;
use crate::parse::{self, deffun, new_custom_error_span, ProblemView, SynthFunView, SynthProblem};

use super::grammar::compile_exact_grammar;
use super::{relevance, NullarySpec};

use rustc_hash::FxHashSet;
use std::collections::BTreeMap;

/// The multi-synth closure pattern, extracted from the file's view.
pub struct MultiSynthSpec<'a> {
    /// The synth-fun with the substantial grammar — the structural `g`.
    pub g: SynthFunView<'a>,
    /// The synth-fun whose grammar is `((C T ((Constant T))))` — the LFP table.
    pub rhs_s_name: &'a str,
    pub bits: usize,
    /// Bit-extract label constraints on `rhs_s_name`: `(bit_idx, expected_bit)`.
    pub labels: Vec<(usize, bool)>,
}

impl<'a> MultiSynthSpec<'a> {
    pub fn detect(view: &'a ProblemView<'_>) -> Option<Self> {
        if view.synth_funs.len() != 2 {
            return None;
        }
        // Identify which synth-fun is "Constant" (the LFP table) and which is the structural g.
        let (rhs_s, g) = pick_constant_and_structural(&view.synth_funs)?;
        if !rhs_s.args.is_empty() || !g.args.is_empty() {
            return None;
        }
        let bits = view.sort_aliases.parse_sort_width(rhs_s.ret)?;
        let g_bits = view.sort_aliases.parse_sort_width(g.ret)?;
        if bits != g_bits {
            return None;
        }

        // Constraints: exactly one closure `(= g rhs.S)` or `(= rhs.S g)`, plus
        // label bit-extracts on either `rhs.S` or `g` (they're equivalent
        // because of the closure). The cyk encoder emits labels on rhs.S;
        // Delis's native bv.rs emits them on g. We accept both.
        let mut closure_seen = false;
        let mut labels: Vec<(usize, bool)> = Vec::new();
        for c in &view.constraints {
            if is_closure_constraint(c, g.name, rhs_s.name)
                || is_closure_constraint(c, rhs_s.name, g.name)
            {
                if closure_seen {
                    return None; // only one closure allowed
                }
                closure_seen = true;
                continue;
            }
            if let Some(lbl) = parse_label_constraint(c, rhs_s.name)
                .or_else(|| parse_label_constraint(c, g.name))
            {
                labels.push(lbl);
            } else {
                return None; // unknown constraint shape — bail
            }
        }
        if !closure_seen {
            return None;
        }

        Some(Self {
            g,
            rhs_s_name: rhs_s.name,
            bits,
            labels,
        })
    }
}

/// Choose which synth-fun is the constant LFP table and which is the structural g.
/// The constant one has grammar with a single "Constant" production.
fn pick_constant_and_structural<'a>(
    synths: &[SynthFunView<'a>],
) -> Option<(SynthFunView<'a>, SynthFunView<'a>)> {
    let a = &synths[0];
    let b = &synths[1];
    match (is_constant_grammar(a.grammar?), is_constant_grammar(b.grammar?)) {
        (true, false) => Some((*a, *b)),
        (false, true) => Some((*b, *a)),
        _ => None, // both or neither — not the expected pattern
    }
}

/// Is this grammar just `((Constant <sort>))` (the LFP-table placeholder)?
fn is_constant_grammar(grammar: &GrammarDef) -> bool {
    if grammar.grouped_rule_lists.len() != 1 {
        return false;
    }
    let rules = &grammar.grouped_rule_lists[0].terms;
    if rules.len() != 1 {
        return false;
    }
    matches!(&rules[0], sygus_parser::ast::SyGuSGTerm::Constant(_))
}

fn is_closure_constraint(term: &SyGuSTerm, left: &str, right: &str) -> bool {
    let SyGuSTerm::Application(id, args) = term else { return false; };
    if id.get_name() != "=" || args.len() != 2 {
        return false;
    }
    matches!(&args[0], SyGuSTerm::Identifier(a) if a.get_name() == left)
        && matches!(&args[1], SyGuSTerm::Identifier(b) if b.get_name() == right)
}

/// Parses a label constraint into `(bit_idx, expected)`. Accepts:
///   - `(= ((_ extract i i) target) #b0|#b1)`
///   - `(not (= ((_ extract i i) target) #b0|#b1))`  → polarity flipped
///
/// The negated form is what Delis emits when a `(constraint (not ...))` in
/// the source compiles to a bit-extract under the BV encoding.
fn parse_label_constraint(term: &SyGuSTerm, target: &str) -> Option<(usize, bool)> {
    // Strip a top-level `not`, flipping the expected polarity.
    let (term, negate) = match term {
        SyGuSTerm::Application(id, args) if id.get_name() == "not" && args.len() == 1 => {
            (&args[0], true)
        }
        _ => (term, false),
    };
    let SyGuSTerm::Application(eq, args) = term else { return None; };
    if eq.get_name() != "=" || args.len() != 2 {
        return None;
    }
    let (extract_side, lit_side) = match (&args[0], &args[1]) {
        (SyGuSTerm::Application(_, _), SyGuSTerm::Literal(Literal::BinConst(_))) => (&args[0], &args[1]),
        (SyGuSTerm::Literal(Literal::BinConst(_)), SyGuSTerm::Application(_, _)) => (&args[1], &args[0]),
        _ => return None,
    };
    let SyGuSTerm::Application(id, ex_args) = extract_side else { return None; };
    let bit_idx = extract_single_bit_idx(id)?;
    if ex_args.len() != 1 {
        return None;
    }
    let SyGuSTerm::Identifier(tgt_id) = &ex_args[0] else { return None; };
    if tgt_id.get_name() != target {
        return None;
    }
    let SyGuSTerm::Literal(Literal::BinConst(bits)) = lit_side else { return None; };
    let trimmed = bits.trim_start_matches(|c| c == '0' || c == '1');
    if !trimmed.is_empty() {
        return None;
    }
    if bits.len() != 1 {
        return None; // a single-bit extract should give a 1-bit literal
    }
    let mut expected = bits.chars().next().unwrap() == '1';
    if negate {
        expected = !expected;
    }
    Some((bit_idx, expected))
}

/// `((_ extract hi lo) x)` where hi == lo gives a single bit. Return that index.
fn extract_single_bit_idx(id: &Identifier) -> Option<usize> {
    let Identifier::Indexed(name, idxs) = id else { return None; };
    if name != "extract" || idxs.len() != 2 {
        return None;
    }
    let hi = numeral_index(&idxs[0])?;
    let lo = numeral_index(&idxs[1])?;
    if hi != lo {
        return None;
    }
    Some(hi)
}

fn numeral_index(idx: &sygus_parser::ast::Index) -> Option<usize> {
    match idx {
        sygus_parser::ast::Index::Numeral(n) => Some(*n),
        sygus_parser::ast::Index::Symbol(_) => None,
    }
}

// ---------------------------------------------------------------------------
//  Search
// ---------------------------------------------------------------------------

/// Enumerate candidate `g` terms; for each, compute the LFP of `cfg.rhs.S`
/// and check label bits. Returns the rendered solution on success.
///
/// Optimization: compute the relevant bits of the closure target via backward
/// relevance with a feedback edge (the `cfg.rhs.S` leaf demand propagates back
/// to g's start NT). Use the resulting bit set to dedup LFP values across
/// candidate g's via projection. This is the first step toward unifying
/// multisynth with the exact-nullary path — it validates the closure-feedback
/// relevance computation end-to-end before the heavier Tabulated refactor.
pub fn search(
    file: &SyGuSFile,
    spec: &MultiSynthSpec,
    env: &deffun::Environ,
    max_g_size: usize,
) -> parse::Result<Option<String>> {
    let grammar = spec
        .g
        .grammar
        .ok_or_else(|| new_custom_error_span("multisynth: g has no grammar".into(), empty_span()))?;
    let max_iters = spec.bits + 1; // LFP converges in at most n_bits iterations.

    let relevant_bits = compute_closure_relevant_bits(spec).unwrap_or_else(|err| {
        info!("multisynth: relevance computation skipped: {}", err);
        None
    });
    if let Some(bits) = relevant_bits.as_ref() {
        info!(
            "multisynth: closure-relevant bits = {}/{}",
            bits.len(),
            spec.bits
        );
    }
    let mut seen_lfp: FxHashSet<Vec<u64>> = FxHashSet::default();

    let enumerator = TermEnumerator::new(grammar, spec.rhs_s_name);
    for size in 1..=max_g_size {
        for term in enumerator.terms_of_size(size) {
            // For each candidate g_term, compute LFP of cfg.rhs.S.
            let mut rhs_s = Value::from_u64(0, spec.bits);
            let mut converged = false;
            for _ in 0..max_iters {
                let next = eval_term(&term, env, &rhs_s, spec.rhs_s_name, spec.bits)?;
                if next == rhs_s {
                    converged = true;
                    break;
                }
                rhs_s = next;
            }
            if !converged {
                continue;
            }
            // Dedup by projected LFP if relevance computation succeeded.
            if let Some(bits) = relevant_bits.as_ref() {
                let key = rhs_s.project_bits(bits);
                if !seen_lfp.insert(key) {
                    continue;
                }
            }
            // Check label bits.
            let ok = spec
                .labels
                .iter()
                .all(|(bit, expected)| rhs_s.bit(*bit) == *expected);
            if ok {
                let solution = format_solution(file, spec, &term, &rhs_s);
                return Ok(Some(solution));
            }
        }
    }
    Ok(None)
}

/// Build an `ExactGrammar` from g's grammar (with the closure leaf as a
/// synthetic arg `Var(0, bits)`), then run `LazyRelevance` with the
/// closure-feedback edge enabled. Returns the relevant bit set of the start
/// NT (== the closure target), or `Ok(None)` if no reduction is possible.
fn compute_closure_relevant_bits(spec: &MultiSynthSpec) -> parse::Result<Option<Vec<usize>>> {
    let grammar_def = spec
        .g
        .grammar
        .ok_or_else(|| new_custom_error_span("multisynth: g has no grammar".into(), empty_span()))?;

    // Construct a SynthProblem for g where the closure leaf is a synthetic arg.
    // OwnedExpr::from_term will resolve the leaf as Var(0, bits) instead of
    // erroring on the unknown identifier (it's a synth-fun, not a define-fun).
    let cfg = Cfg::from_grammar(grammar_def, None)?;
    let leaf_name: &'static str = Box::leak(spec.rhs_s_name.to_string().into_boxed_str());
    let problem = SynthProblem {
        name: Box::leak(spec.g.name.to_string().into_boxed_str()),
        args: vec![leaf_name],
        arg_decls: vec![SortedVar {
            name: leaf_name.to_string(),
            sort: spec.g.ret.clone(),
        }],
        cfg,
        span: empty_span(),
        description: String::new(),
        chatgpt_exprs: Vec::new(),
        bits: spec.bits,
        ret_sort: spec.g.ret.clone(),
        axioms: None,
    };

    let multi = MultiConfig::from_problem(&problem)?;
    let exact = compile_exact_grammar(&multi);

    let known_bits: BTreeMap<usize, bool> = spec.labels.iter().copied().collect();
    let nullary_spec = NullarySpec::BitConstraints {
        bits: spec.bits,
        known_bits,
        structural: Vec::new(),
    };

    let Some(mut lazy) = relevance::LazyRelevance::new_with_closure(&exact, &nullary_spec, 0)
    else {
        return Ok(None);
    };
    while !lazy.advance(1024) {}
    Ok(lazy
        .finish()
        .and_then(|bits| bits.into_iter().next()))
}

fn format_solution(
    file: &SyGuSFile,
    spec: &MultiSynthSpec,
    g_term: &Term,
    rhs_s: &Value,
) -> String {
    let g_sort_text = display_sort(spec.g.ret);
    let rhs_sort_text = display_sort_from_name(file, spec.rhs_s_name).unwrap_or(g_sort_text.clone());
    let rhs_s_lit = format!("#b{}", value_to_binstr(rhs_s, spec.bits));
    let g_text = g_term.to_sygus();
    // Order: g first, cfg.rhs.S second (mirrors the encoder).
    format!(
        "(define-fun {} () {} {})\n(define-fun {} () {} {})",
        spec.g.name, g_sort_text, g_text, spec.rhs_s_name, rhs_sort_text, rhs_s_lit
    )
}

fn display_sort(sort: &Sort) -> String {
    format!("{}", sort)
}

fn display_sort_from_name(file: &SyGuSFile, name: &str) -> Option<String> {
    for cmd in &file.cmds {
        if let SyGuSCmd::SynthFun(n, _, ret, _) = cmd {
            if n == name {
                return Some(display_sort(ret));
            }
        }
    }
    None
}

fn value_to_binstr(v: &Value, bits: usize) -> String {
    let mut out = String::with_capacity(bits);
    for i in (0..bits).rev() {
        out.push(if v.bit(i) { '1' } else { '0' });
    }
    out
}

// ---------------------------------------------------------------------------
//  Term enumeration over the synth-fun grammar
// ---------------------------------------------------------------------------

/// A concrete g term: leaf reference or application of a constructor name.
#[derive(Clone, Debug)]
enum Term {
    /// Reference to a 0-arity define-fun or the cfg.rhs.S placeholder.
    Leaf(String),
    /// Application of a (named) constructor to children.
    App(String, Vec<Term>),
}

impl Term {
    fn to_sygus(&self) -> String {
        match self {
            Term::Leaf(name) => name.clone(),
            Term::App(name, args) => {
                let inside = args.iter().map(|a| a.to_sygus()).collect::<Vec<_>>().join(" ");
                format!("({} {})", name, inside)
            }
        }
    }
}

/// Walks the synth-fun grammar and enumerates terms.  Smallest first.
/// Terms are produced eagerly into vectors; OK for small grammars.
struct TermEnumerator<'a> {
    grammar: &'a GrammarDef,
}

impl<'a> TermEnumerator<'a> {
    fn new(grammar: &'a GrammarDef) -> Self {
        Self { grammar }
    }

    fn start_nt(&self) -> &str {
        &self.grammar.grouped_rule_lists[0].symbol
    }

    fn nt_rules(&self, nt: &str) -> &[sygus_parser::ast::SyGuSGTerm] {
        self.grammar
            .grouped_rule_lists
            .iter()
            .find(|grl| grl.symbol == nt)
            .map(|grl| grl.terms.as_slice())
            .unwrap_or(&[])
    }

    /// Returns all terms produced by the start nonterminal with exactly the given size.
    fn terms_of_size(&self, size: usize) -> Vec<Term> {
        let mut cache: std::collections::HashMap<(String, usize), Vec<Term>> =
            std::collections::HashMap::new();
        self.terms_of_nt_size(self.start_nt(), size, &mut cache)
    }

    fn terms_of_nt_size(
        &self,
        nt: &str,
        size: usize,
        cache: &mut std::collections::HashMap<(String, usize), Vec<Term>>,
    ) -> Vec<Term> {
        if size == 0 {
            return Vec::new();
        }
        if let Some(c) = cache.get(&(nt.to_string(), size)) {
            return c.clone();
        }
        let mut out = Vec::new();
        for rule in self.nt_rules(nt) {
            self.extend_from_rule(rule, size, &mut out, cache);
        }
        cache.insert((nt.to_string(), size), out.clone());
        out
    }

    fn extend_from_rule(
        &self,
        rule: &sygus_parser::ast::SyGuSGTerm,
        size: usize,
        out: &mut Vec<Term>,
        cache: &mut std::collections::HashMap<(String, usize), Vec<Term>>,
    ) {
        let term = match rule {
            sygus_parser::ast::SyGuSGTerm::SyGuSTerm(t) => t,
            _ => return, // skip (Constant T)/(Variable T) — not used in g's grammar
        };
        match term {
            SyGuSTerm::Identifier(id) => {
                if size != 1 {
                    return;
                }
                let name = id.get_name();
                // If the identifier matches another nonterminal, expand it.
                if self.nt_rules(name.as_ref()).is_empty() {
                    out.push(Term::Leaf(name.to_string()));
                } else {
                    let nested = self.terms_of_nt_size(name.as_ref(), size, cache);
                    out.extend(nested);
                }
            }
            SyGuSTerm::Application(id, args) => {
                if size < 1 + args.len() {
                    return;
                }
                let remaining = size - 1;
                let child_nts: Vec<&str> = args
                    .iter()
                    .filter_map(|a| match a {
                        SyGuSTerm::Identifier(child_id) => {
                            let n = child_id.get_name();
                            if self.nt_rules(n.as_ref()).is_empty() {
                                None
                            } else {
                                // We need a 'static str-ish or we just lookup again later via Term
                                Some(())
                            }
                        }
                        _ => None,
                    })
                    .map(|()| "")
                    .collect();
                let _ = child_nts; // placeholder
                // Distribute remaining size across children using the args' nonterminals.
                let nts: Vec<String> = args
                    .iter()
                    .filter_map(|a| match a {
                        SyGuSTerm::Identifier(child_id) => Some(child_id.get_name().to_string()),
                        _ => None,
                    })
                    .collect();
                if nts.len() != args.len() {
                    return; // unsupported non-identifier arg position
                }
                // Allocate sizes summing to `remaining`, with each part ≥ 1.
                each_split(remaining, nts.len(), &mut |sizes| {
                    let per_child: Vec<Vec<Term>> = sizes
                        .iter()
                        .zip(nts.iter())
                        .map(|(s, nt)| self.terms_of_nt_size(nt, *s, cache))
                        .collect();
                    if per_child.iter().any(|v| v.is_empty()) {
                        return;
                    }
                    cartesian_product(&per_child, &mut |children| {
                        out.push(Term::App(id.get_name().to_string(), children.to_vec()));
                    });
                });
            }
            _ => {}
        }
    }
}

/// Enumerate compositions of `total` into exactly `parts` positive integers.
fn each_split(total: usize, parts: usize, f: &mut impl FnMut(&[usize])) {
    if parts == 0 {
        if total == 0 {
            f(&[]);
        }
        return;
    }
    if parts == 1 {
        if total >= 1 {
            f(&[total]);
        }
        return;
    }
    for first in 1..=total.saturating_sub(parts - 1) {
        each_split_inner(total - first, parts - 1, first, &mut Vec::new(), f);
    }
}

fn each_split_inner(
    remaining: usize,
    parts: usize,
    head: usize,
    acc: &mut Vec<usize>,
    f: &mut impl FnMut(&[usize]),
) {
    acc.push(head);
    if parts == 0 {
        if remaining == 0 {
            f(acc);
        }
    } else if parts == 1 {
        if remaining >= 1 {
            acc.push(remaining);
            f(acc);
            acc.pop();
        }
    } else {
        for next in 1..=remaining.saturating_sub(parts - 1) {
            each_split_inner(remaining - next, parts - 1, next, acc, f);
        }
    }
    acc.pop();
}

fn cartesian_product(slots: &[Vec<Term>], f: &mut impl FnMut(&[Term])) {
    let mut buf: Vec<Term> = Vec::with_capacity(slots.len());
    cartesian_inner(slots, 0, &mut buf, f);
}

fn cartesian_inner(
    slots: &[Vec<Term>],
    idx: usize,
    buf: &mut Vec<Term>,
    f: &mut impl FnMut(&[Term]),
) {
    if idx == slots.len() {
        f(buf);
        return;
    }
    for item in &slots[idx] {
        buf.push(item.clone());
        cartesian_inner(slots, idx + 1, buf, f);
        buf.pop();
    }
}

// ---------------------------------------------------------------------------
//  Term evaluation against define-funs in the env
// ---------------------------------------------------------------------------

fn eval_term(
    term: &Term,
    env: &deffun::Environ,
    rhs_s_value: &Value,
    rhs_s_name: &str,
    bits: usize,
) -> parse::Result<Value> {
    match term {
        Term::Leaf(name) => {
            if name == rhs_s_name {
                return Ok(rhs_s_value.clone());
            }
            // 0-arity define-fun. May reference closure synth-funs in its body.
            let Some(id) = env.lookup(name, 0) else {
                return Err(new_custom_error_span(
                    format!("multisynth: unknown 0-arity symbol {name}"),
                    empty_span(),
                ));
            };
            let arg_vals = closure_arg_values(env, id, 0, rhs_s_value, rhs_s_name);
            env.apply(id, 0).eval(&arg_vals).map_err(|_| {
                new_custom_error_span(format!("multisynth: divide-by-zero in {name}"), empty_span())
            })
        }
        Term::App(name, args) => {
            let mut arg_vals = Vec::with_capacity(args.len());
            for a in args {
                arg_vals.push(eval_term(a, env, rhs_s_value, rhs_s_name, bits)?);
            }
            let Some(id) = env.lookup(name, args.len()) else {
                return Err(new_custom_error_span(
                    format!("multisynth: unknown {}-arity symbol {name}", args.len()),
                    empty_span(),
                ));
            };
            // Append closure synth-fun values (in declaration order) so the
            // define-fun's body — which may reference them via Var slots
            // beyond the real arity — has all the bindings it needs.
            arg_vals.extend(closure_arg_values(env, id, args.len(), rhs_s_value, rhs_s_name));
            env.apply(id, args.len()).eval(&arg_vals).map_err(|_| {
                new_custom_error_span(
                    format!("multisynth: divide-by-zero in {name}"),
                    empty_span(),
                )
            })
        }
    }
}

/// Resolve the value of each closure synth-fun the define-fun references.
/// The multisynth path knows only one closure synth-fun (the LFP target);
/// any others are bound to zero as a placeholder (and shouldn't appear in
/// well-formed cyk-style problems).
fn closure_arg_values(
    env: &deffun::Environ,
    id: usize,
    nargs: usize,
    rhs_s_value: &Value,
    rhs_s_name: &str,
) -> Vec<Value> {
    let names = env.closure_args(id, nargs);
    let bits = env.closure_arg_bits(id, nargs);
    names
        .iter()
        .zip(bits.iter())
        .map(|(n, b)| {
            if *n == rhs_s_name {
                rhs_s_value.clone()
            } else {
                Value::from_u64(0, *b)
            }
        })
        .collect()
}

fn empty_span() -> pest::Span<'static> {
    pest::Span::new("", 0, 0).unwrap()
}
