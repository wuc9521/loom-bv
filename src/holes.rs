//! Constant-hole synthesis: proper support for the SyGuS `(Constant T)`
//! grammar construct, which the value enumerator drops (`grammar.rs`).
//!
//! When a (nullary) synth-fun's grammar interleaves ordinary structural
//! productions with `Constant` nonterminals, a solution is a *skeleton*
//! (a syntax tree over the structural productions) together with a choice
//! of constant for each `Constant` hole. We enumerate skeletons in
//! increasing size and, for each fixed skeleton, ask an SMT solver to fill
//! the holes so the constraints hold — a bounded QF_BV query per skeleton.
//!
//! This is the literal meaning of the SyGuS `Constant` construct, so it is
//! general; the delis founded-annotation encoding is the first consumer.
//! Constraints are passed to the solver verbatim (no shape-matching), and
//! detection is purely structural ("a grammar has a `Constant` production").

use std::collections::{HashMap, HashSet};

use rsmt2::{
    print::{IdentParser, ModelParser},
    SmtConf, SmtRes, Solver,
};
use sygus_parser::ast::{SyGuSGTerm, SyGuSTerm};

use crate::parse::ProgramEnv;
use crate::{debg, info};

/// Build an `SmtConf` from environment variables so we can swap SMT solvers
/// without editing the source between trials.
///
/// * `DELIS_SMT_SOLVER` picks the solver family (`z3` [default], `bitwuzla`,
///   `cvc5`, `yices2`). The associated binary is expected on `PATH` under the
///   canonical name, overridable via `DELIS_SMT_BINARY`.
/// * `DELIS_SMT_ARGS` is a semicolon-separated list of extra command-line
///   options appended to the solver invocation, e.g. `smt.random_seed=1;sat.threads=4`.
fn smt_conf_from_env() -> SmtConf {
    let solver = std::env::var("DELIS_SMT_SOLVER").unwrap_or_else(|_| "yices2".into());
    let bin = std::env::var("DELIS_SMT_BINARY").ok();
    let mut conf = match solver.as_str() {
        "bitwuzla" => {
            let mut c = SmtConf::yices_2(bin.unwrap_or_else(|| "bitwuzla".into()));
            c.option("--lang");
            c.option("smt2");
            c.option("-m");
            c
        }
        "cvc5" => {
            // cvc5 speaks SMT-LIB2 and supports incremental push/pop. We reuse
            // the cvc4 factory (same protocol) with the `cvc5` binary name.
            let mut c = SmtConf::cvc4(bin.unwrap_or_else(|| "cvc5".into()));
            c.option("--lang=smt2");
            c.option("--incremental");
            c.option("--produce-models");
            c
        }
        "boolector" => {
            let mut c = SmtConf::yices_2(bin.unwrap_or_else(|| "boolector".into()));
            c.option("--smt2");
            c.option("--incremental");
            c.option("--model-gen");
            c
        }
        "mathsat" => {
            let mut c = SmtConf::z3(bin.unwrap_or_else(|| "mathsat".into()));
            c.option("-input=smt2");
            c
        }
        "yices2" => {
            let mut c = SmtConf::yices_2(bin.unwrap_or_else(|| "yices-smt2".into()));
            c.option("--incremental");
            c
        }
        // "z3" and anything else fall back to z3.
        _ => SmtConf::z3(bin.unwrap_or_else(|| "z3".into())),
    };
    if let Ok(extra) = std::env::var("DELIS_SMT_ARGS") {
        for opt in extra.split(';').filter(|s| !s.is_empty()) {
            conf.option(opt);
        }
    }
    conf
}

/// Send `(set-option ...)` commands from `DELIS_SMT_OPTIONS` env var.
/// Format: semicolon-separated `key=value` pairs (e.g.
/// `yices-fast-restarts=true;yices-var-elim=true`). Each becomes
/// `(set-option :key value)`.
fn apply_smt_options(solver: &mut Solver<Parser>) -> crate::SolverResult<()> {
    if let Ok(opts) = std::env::var("DELIS_SMT_OPTIONS") {
        for kv in opts.split(';').filter(|s| !s.is_empty()) {
            let (key, val) = kv.split_once('=').unwrap_or((kv, "true"));
            let key = if key.starts_with(':') {
                key.to_string()
            } else {
                format!(":{key}")
            };
            solver
                .set_option(&key, val)
                .map_err(|e| format!("set-option {key} {val}: {e}"))?;
        }
    }
    Ok(())
}

/// A production template for one grammar nonterminal.
enum Tmpl {
    /// `(Constant T)` — expands to a fresh hole of the given sort.
    Hole(String),
    /// An ordinary structural production.
    Term(Node),
}

/// A structural production with nonterminal references resolved to `Nt`.
enum Node {
    Nt(String),
    Leaf(String),
    App(String, Vec<Node>),
}

/// A concrete skeleton: a syntax tree whose `Hole`s await constant values.
#[derive(Clone)]
enum Skel {
    Hole(String),
    Leaf(String),
    App(String, Vec<Skel>),
}

/// An input define-fun, kept structured so it can be replayed to the solver
/// once via `rsmt2`'s `define_fun`.
struct DefFun {
    name: String,
    args: Vec<(String, String)>,
    ret: String,
    body: String,
}

pub struct HoleSpec {
    synth_name: String,
    ret_sort: String,
    start: String,
    prods: HashMap<String, Vec<Tmpl>>,
    /// The input's define-funs, sent to the solver once as the base scope.
    defines: Vec<DefFun>,
    /// The constraint expressions, asserted once in the solver base scope.
    constraints: Vec<String>,
    /// Operator laws for canonical dedup (from `(assume …)`).
    laws: crate::laws::OpLaws,
}

impl HoleSpec {
    /// Fires when the (single, nullary) synth-fun's grammar has at least one
    /// `Constant` production. Grammars without any `Constant` are left to the
    /// existing value path.
    pub fn detect(view: &ProgramEnv<'_>) -> Option<Self> {
        if view.synth_funs.len() != 1 {
            return None;
        }
        let sf = view.synth_funs[0];
        if !sf.args.is_empty() {
            return None;
        }
        let grammar = sf.grammar?;
        let nt_names: Vec<&str> = grammar
            .grouped_rule_lists
            .iter()
            .map(|g| g.symbol.as_str())
            .collect();
        let is_nt = |name: &str| nt_names.iter().any(|n| *n == name);

        let mut prods: HashMap<String, Vec<Tmpl>> = HashMap::new();
        let mut any_hole = false;
        for g in &grammar.grouped_rule_lists {
            let mut tmpls = Vec::new();
            for term in &g.terms {
                match term {
                    SyGuSGTerm::Constant(sort) => {
                        any_hole = true;
                        tmpls.push(Tmpl::Hole(sort.to_string()));
                    }
                    // `Variable` (a synth-fun formal) is dead for a nullary
                    // synth-fun; drop the production.
                    SyGuSGTerm::Variable(_) => {}
                    SyGuSGTerm::SyGuSTerm(t) => tmpls.push(Tmpl::Term(node_of(t, &is_nt))),
                }
            }
            prods.insert(g.symbol.to_string(), tmpls);
        }
        if !any_hole {
            return None;
        }

        let defines = view
            .define_funs
            .iter()
            .map(|d| DefFun {
                name: d.name.to_string(),
                args: d
                    .args
                    .iter()
                    .map(|a| (a.name.clone(), a.sort.to_string()))
                    .collect(),
                ret: d.ret.to_string(),
                body: d.body.to_string(),
            })
            .collect();
        let constraints = view.constraints.iter().map(|c| c.to_string()).collect();
        let laws = crate::laws::OpLaws::from_assumes(&view.assumes);

        Some(HoleSpec {
            synth_name: sf.name.to_string(),
            ret_sort: sf.ret.to_string(),
            start: grammar.grouped_rule_lists[0].symbol.to_string(),
            prods,
            defines,
            constraints,
            laws,
        })
    }

    /// Enumerate skeletons in increasing size; for each, SMT-solve the holes.
    /// Returns the inner `(define-fun …)` for the first satisfiable skeleton.
    pub fn solve(&self) -> crate::SolverResult<String> {
        let recursive = self.is_recursive();
        info!(
            "const-hole: synth={} start={} nts={} recursive={} solver={}",
            self.synth_name,
            self.start,
            self.prods.len(),
            recursive,
            std::env::var("DELIS_SMT_SOLVER").unwrap_or_else(|_| "yices2".into()),
        );
        let max_size: usize = std::env::var("DRYAD_HOLE_MAX_SIZE")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(usize::MAX);

        // A recursive grammar admits unboundedly large trees, so we never stop
        // on an empty size (completeness). A finite grammar has a maximum size;
        // once skeletons stop appearing for longer than any derivation, we're
        // done. Small sizes are legitimately empty before the minimum tree.
        let empty_cap = self.prods.len() + 2;
        let mut seen_any = false;
        let mut empty_streak = 0usize;

        // One persistent solver session: the (heavy) define-funs are sent once
        // as the base scope, then each skeleton is solved in a push/pop frame.
        // This amortizes process startup + define-fun setup across all skeletons.
        let conf = smt_conf_from_env();
        let mut solver = conf
            .spawn(Parser)
            .map_err(|e| format!("failed to spawn z3 (is it on PATH?): {e}"))?;
        solver
            .set_logic(rsmt2::Logic::QF_BV)
            .map_err(|e| format!("set-logic: {e}"))?;
        apply_smt_options(&mut solver)?;
        solver
            .declare_const(self.synth_name.as_str(), self.ret_sort.as_str())
            .map_err(|e| format!("z3 declare {}: {e}", self.synth_name))?;
        for d in &self.defines {
            solver
                .define_fun(
                    d.name.as_str(),
                    d.args.iter().map(|(n, s)| (n.as_str(), s.as_str())),
                    d.ret.as_str(),
                    d.body.as_str(),
                )
                .map_err(|e| format!("z3 define-fun {}: {e}", d.name))?;
        }
        for c in &self.constraints {
            solver
                .assert(c.as_str())
                .map_err(|e| format!("z3 assert: {e}"))?;
        }
        // Canonical-form dedup: skeletons that denote the same grammar (modulo
        // the declared operator laws) have the same SAT result, so we check one
        // representative per canonical key.
        let mut seen: HashSet<String> = HashSet::new();
        let mut deduped = 0usize;

        let mut tried = 0usize;
        for size in 0..=max_size {
            let skels = self.gen(&self.start, size, &mut Vec::new());
            if skels.is_empty() {
                if !recursive && seen_any {
                    empty_streak += 1;
                    if empty_streak > empty_cap {
                        break;
                    }
                }
                continue;
            }
            seen_any = true;
            empty_streak = 0;
            let size_start = std::time::Instant::now();
            let size_tried_start = tried;
            let size_deduped_start = deduped;
            for skel in &skels {
                if !seen.insert(canon(skel, &self.laws)) {
                    deduped += 1;
                    continue;
                }
                let mut sorts = Vec::new();
                let body = render(skel, &mut sorts, None);
                tried += 1;
                let t = std::time::Instant::now();
                let res = self.check(&mut solver, &body, &sorts)?;
                debg!(
                    "skeleton #{tried} (size {size}, {} holes): {} in {:?} — {}",
                    sorts.len(),
                    if res.is_some() { "SAT" } else { "unsat" },
                    t.elapsed(),
                    summarize(&body)
                );
                if let Some(values) = res {
                    let filled = render(skel, &mut Vec::new(), Some(&values));
                    info!(
                        "const-hole: sat size={size} checked={tried} deduped={deduped} elapsed={:?}",
                        size_start.elapsed(),
                    );
                    return Ok(format!(
                        "(define-fun {} () {} {})",
                        self.synth_name, self.ret_sort, filled
                    ));
                }
            }
            debg!(
                "const-hole: size={size} skeletons={} checked={} deduped={} total_checked={} total_deduped={} elapsed={:?}",
                skels.len(),
                tried - size_tried_start,
                deduped - size_deduped_start,
                tried,
                deduped,
                size_start.elapsed(),
            );
        }
        Err("const-hole: no solution within DRYAD_HOLE_MAX_SIZE".into())
    }

    /// Enumerate skeletons in increasing size against a refuter query. A SAT
    /// result means the skeleton has a counterexample certificate and is pruned;
    /// the first UNSAT skeleton is returned.
    pub fn solve_refuter(&self) -> crate::SolverResult<String> {
        let recursive = self.is_recursive();
        info!(
            "const-hole refuter: synth={} start={} nts={} recursive={} solver={}",
            self.synth_name,
            self.start,
            self.prods.len(),
            recursive,
            std::env::var("DELIS_SMT_SOLVER").unwrap_or_else(|_| "yices2".into()),
        );
        let max_size: usize = std::env::var("DRYAD_HOLE_MAX_SIZE")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(usize::MAX);

        let empty_cap = self.prods.len() + 2;
        let mut seen_any = false;
        let mut empty_streak = 0usize;

        let conf = smt_conf_from_env();
        let mut solver = conf
            .spawn(Parser)
            .map_err(|e| format!("failed to spawn z3 (is it on PATH?): {e}"))?;
        solver
            .set_logic(rsmt2::Logic::QF_BV)
            .map_err(|e| format!("set-logic: {e}"))?;
        apply_smt_options(&mut solver)?;
        solver
            .declare_const(self.synth_name.as_str(), self.ret_sort.as_str())
            .map_err(|e| format!("z3 declare {}: {e}", self.synth_name))?;
        for d in &self.defines {
            solver
                .define_fun(
                    d.name.as_str(),
                    d.args.iter().map(|(n, s)| (n.as_str(), s.as_str())),
                    d.ret.as_str(),
                    d.body.as_str(),
                )
                .map_err(|e| format!("z3 define-fun {}: {e}", d.name))?;
        }
        for c in &self.constraints {
            solver
                .assert(c.as_str())
                .map_err(|e| format!("z3 assert: {e}"))?;
        }
        let mut seen: HashSet<String> = HashSet::new();
        let mut deduped = 0usize;
        let mut tried = 0usize;
        let mut sampled = 0usize;
        for size in 0..=max_size {
            let skels = self.gen(&self.start, size, &mut Vec::new());
            if skels.is_empty() {
                if !recursive && seen_any {
                    empty_streak += 1;
                    if empty_streak > empty_cap {
                        break;
                    }
                }
                continue;
            }
            seen_any = true;
            empty_streak = 0;
            let size_start = std::time::Instant::now();
            let size_tried_start = tried;
            let size_deduped_start = deduped;
            for skel in &skels {
                if !seen.insert(canon(skel, &self.laws)) {
                    deduped += 1;
                    continue;
                }
                let mut sorts = Vec::new();
                let body = render(skel, &mut sorts, None);
                // Random-sampling pre-filter: try to refute cheaply before SMT.
                if !sorts.is_empty() {
                    if let Some(true) = self.try_refute_by_sampling(&body, &sorts) {
                        sampled += 1;
                        continue;
                    }
                }
                tried += 1;
                let t = std::time::Instant::now();
                let refuted = self.check_refuter(&mut solver, &body, &sorts)?;
                debg!(
                    "refuter skeleton #{tried} (size {size}, {} holes): {} in {:?} — {}",
                    sorts.len(),
                    if refuted {
                        "SAT/refuted"
                    } else {
                        "unsat/accepted"
                    },
                    t.elapsed(),
                    summarize(&body)
                );
                if !refuted {
                    let defaults = sorts
                        .iter()
                        .map(|sort| {
                            default_value(sort)
                                .ok_or_else(|| format!("no default value for hole sort {sort}"))
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    let filled = render(skel, &mut Vec::new(), Some(&defaults));
                    info!(
                        "const-hole refuter: accepted size={size} checked={tried} deduped={deduped} sampled={sampled} elapsed={:?}",
                        size_start.elapsed(),
                    );
                    return Ok(format!(
                        "(define-fun {} () {} {})",
                        self.synth_name, self.ret_sort, filled
                    ));
                }
            }
            debg!(
                "const-hole refuter: size={size} skeletons={} checked={} deduped={} total_checked={} total_deduped={} elapsed={:?}",
                skels.len(),
                tried - size_tried_start,
                deduped - size_deduped_start,
                tried,
                deduped,
                size_start.elapsed(),
            );
        }
        Err("const-hole refuter: no unrefuted candidate within DRYAD_HOLE_MAX_SIZE".into())
    }

    /// Whether some nonterminal can reach itself through structural
    /// productions — i.e. the grammar admits unboundedly large trees.
    fn is_recursive(&self) -> bool {
        fn refs<'a>(node: &'a Node, out: &mut Vec<&'a str>) {
            match node {
                Node::Nt(n) => out.push(n),
                Node::App(_, kids) => kids.iter().for_each(|k| refs(k, out)),
                Node::Leaf(_) => {}
            }
        }
        let edges: HashMap<&str, Vec<&str>> = self
            .prods
            .iter()
            .map(|(nt, tmpls)| {
                let mut succ = Vec::new();
                for t in tmpls {
                    if let Tmpl::Term(node) = t {
                        refs(node, &mut succ);
                    }
                }
                (nt.as_str(), succ)
            })
            .collect();
        // DFS from each NT looking for a path back to itself.
        for start in edges.keys() {
            let mut stack = edges[start].clone();
            let mut seen: Vec<&str> = Vec::new();
            while let Some(n) = stack.pop() {
                if n == *start {
                    return true;
                }
                if seen.contains(&n) {
                    continue;
                }
                seen.push(n);
                if let Some(succ) = edges.get(n) {
                    stack.extend(succ);
                }
            }
        }
        false
    }

    /// All skeletons rooted at `nt` using exactly `size` application nodes
    /// (holes and leaves cost 0). `visited` guards against bare-alias cycles.
    fn gen(&self, nt: &str, size: usize, visited: &mut Vec<String>) -> Vec<Skel> {
        if visited.iter().any(|v| v == nt) {
            return Vec::new();
        }
        let Some(tmpls) = self.prods.get(nt) else {
            return Vec::new();
        };
        let mut out = Vec::new();
        for tmpl in tmpls {
            match tmpl {
                Tmpl::Hole(sort) => {
                    if size == 0 {
                        out.push(Skel::Hole(sort.clone()));
                    }
                }
                Tmpl::Term(node) => {
                    visited.push(nt.to_string());
                    out.extend(self.gen_node(node, size, visited));
                    visited.pop();
                }
            }
        }
        out
    }

    fn gen_node(&self, node: &Node, size: usize, visited: &mut Vec<String>) -> Vec<Skel> {
        match node {
            Node::Nt(name) => self.gen(name, size, visited),
            Node::Leaf(s) => {
                if size == 0 {
                    vec![Skel::Leaf(s.clone())]
                } else {
                    Vec::new()
                }
            }
            Node::App(head, kids) => {
                if size == 0 {
                    return Vec::new();
                }
                let mut out = Vec::new();
                for split in splits(size - 1, kids.len()) {
                    // Children descend with a strictly smaller budget, so the
                    // alias guard can reset.
                    let pools: Vec<Vec<Skel>> = kids
                        .iter()
                        .zip(&split)
                        .map(|(kid, &s)| self.gen_node(kid, s, &mut Vec::new()))
                        .collect();
                    if pools.iter().any(|p| p.is_empty()) {
                        continue;
                    }
                    for combo in product(&pools) {
                        out.push(Skel::App(head.clone(), combo));
                    }
                }
                out
            }
        }
    }

    /// Solve one skeleton's holes in a fresh push/pop frame on the shared
    /// session. `Some(values)` on SAT (one per hole, in DFS order); `None` on
    /// UNSAT. A solver error propagates (it is NOT treated as unsat, which
    /// would silently skip a satisfiable skeleton).
    fn check(
        &self,
        solver: &mut Solver<Parser>,
        body: &str,
        hole_sorts: &[String],
    ) -> crate::SolverResult<Option<Vec<String>>> {
        solver.push(1).map_err(|e| format!("z3 push: {e}"))?;
        for (i, sort) in hole_sorts.iter().enumerate() {
            solver
                .declare_const(format!("h{i}"), sort.as_str())
                .map_err(|e| format!("z3 declare h{i}: {e}"))?;
        }
        self.assert_full_skeleton(solver, body)?;
        let sat = solver
            .check_sat()
            .map_err(|e| format!("z3 check-sat: {e}"))?;
        let result = if sat {
            let model = solver
                .get_model()
                .map_err(|e| format!("z3 get-model: {e}"))?;
            let vals: HashMap<String, String> = model
                .into_iter()
                .map(|(name, _, _, value)| (name, value))
                .collect();
            let values = (0..hole_sorts.len())
                .map(|i| {
                    vals.get(&format!("h{i}"))
                        .cloned()
                        .ok_or_else(|| format!("z3 model missing h{i}"))
                })
                .collect::<Result<Vec<_>, _>>()?;
            Some(values)
        } else {
            None
        };
        solver.pop(1).map_err(|e| format!("z3 pop: {e}"))?;
        Ok(result)
    }

    /// Try to refute a skeleton by random evaluation, avoiding the SMT solver.
    /// Returns `Some(true)` if sampling proves the skeleton is refutable (SAT),
    /// `None` if sampling cannot determine (either parse failure or all samples
    /// failed to satisfy the constraints).
    fn try_refute_by_sampling(
        &self,
        body: &str,
        hole_sorts: &[String],
    ) -> Option<bool> {
        use crate::enumerate::expr::OwnedExpr;
        use crate::enumerate::value::BitVec;

        // Parse hole sorts into widths.
        let hole_widths: Vec<usize> = hole_sorts
            .iter()
            .filter_map(|s| bitvec_width(s))
            .collect();
        if hole_widths.len() != hole_sorts.len() {
            return None;
        }

        // Build env for parsing: holes h0, h1, ... as variables.
        let env: Vec<(&str, u64)> = hole_widths
            .iter()
            .enumerate()
            .map(|(i, w)| {
                // Leak a small string for the lifetime — these are short-lived.
                let name: &'static str = Box::leak(format!("h{i}").into_boxed_str());
                (name, *w as u64)
            })
            .collect();

        // Parse the body expression. This reuses the already-registered
        // define-funs in the global Environ.
        let parsed_term = match sygus_parser::SyGuSTerm::from_str(body) {
            Ok(t) => t,
            Err(_e) => {
                eprintln!("sampling: failed to parse body: {}", &body[..body.len().min(80)]);
                return None;
            }
        };
        let expr = match OwnedExpr::from_term(&parsed_term, &env) {
            Ok(e) => e,
            Err(_e) => {
                eprintln!("sampling: failed to lower body: {}", &body[..body.len().min(80)]);
                return None;
            }
        };

        // Parse the ret_sort width for the synth-fun result.
        let ret_width = bitvec_width(&self.ret_sort)?;

        // Parse the constraints once: each constraint is a boolean condition on
        // the synth-fun value `g`. We parse each into an OwnedExpr that takes
        // `g` as its sole variable.
        let g_env: &[(&str, u64)] = &[(&self.synth_name, ret_width as u64)];
        let constraint_exprs: Vec<OwnedExpr> = self.constraints.iter()
            .filter_map(|c| {
                let term = sygus_parser::SyGuSTerm::from_str(c).ok()?;
                OwnedExpr::from_term(&term, g_env).ok()
            })
            .collect();
        if constraint_exprs.is_empty() {
            if !self.constraints.is_empty() {
                eprintln!("sampling: 0/{} constraints parsed. first: {}",
                    self.constraints.len(), &self.constraints[0][..self.constraints[0].len().min(100)]);
            }
            return None;
        }

        // Try K random hole assignments.
        const K: usize = 32;
        static ONCE: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
        let mut rng_state: u64 = 0xdeadbeef_cafebabe;
        let mut eval_ok = 0usize;
        for _ in 0..K {
            // Generate random values for each hole.
            let args: Vec<BitVec> = hole_widths
                .iter()
                .map(|w| {
                    rng_state = rng_state.wrapping_mul(6364136223846793005).wrapping_add(1);
                    BitVec::from_u64(rng_state, *w)
                })
                .collect();

            // Evaluate the skeleton body with these hole values.
            let g_val = match expr.eval(&args) {
                Ok(v) => { eval_ok += 1; v },
                Err(_) => continue,
            };

            // Check all constraints on the resulting g value.
            // Constraints use internal boolean encoding: 0 = true.
            let all_sat = constraint_exprs.iter().all(|c| {
                match c.eval(&[g_val.clone()]) {
                    Ok(v) => v.is_zero(),
                    Err(_) => false,
                }
            });

            if all_sat {
                return Some(true); // Refuted by sampling!
            }
        }

        if !ONCE.swap(true, std::sync::atomic::Ordering::Relaxed) {
            eprintln!("sampling: first skeleton: eval_ok={eval_ok}/{K} constraints={} holes={} body_len={}",
                constraint_exprs.len(), hole_widths.len(), body.len());
        }

        None // Sampling inconclusive.
    }

    /// Refuter mode only needs SAT/UNSAT. On SAT the skeleton is discarded, so
    /// do not request a model for annotation holes.
    fn check_refuter(
        &self,
        solver: &mut Solver<Parser>,
        body: &str,
        hole_sorts: &[String],
    ) -> crate::SolverResult<bool> {
        solver.push(1).map_err(|e| format!("z3 push: {e}"))?;
        for (i, sort) in hole_sorts.iter().enumerate() {
            solver
                .declare_const(format!("h{i}"), sort.as_str())
                .map_err(|e| format!("z3 declare h{i}: {e}"))?;
        }
        self.assert_full_skeleton(solver, body)?;
        let sat = solver
            .check_sat()
            .map_err(|e| format!("z3 check-sat: {e}"))?;
        solver.pop(1).map_err(|e| format!("z3 pop: {e}"))?;
        Ok(sat)
    }

    fn assert_full_skeleton(
        &self,
        solver: &mut Solver<Parser>,
        body: &str,
    ) -> crate::SolverResult<()> {
        let bind_synth = format!("(= {} {body})", self.synth_name);
        solver
            .assert(bind_synth.as_str())
            .map_err(|e| format!("z3 assert skeleton: {e}"))?;
        Ok(())
    }
}

/// Lower a grammar production term to a `Node`, resolving nonterminal
/// identifiers via `is_nt`.
fn node_of(term: &SyGuSTerm, is_nt: &impl Fn(&str) -> bool) -> Node {
    match term {
        SyGuSTerm::Identifier(id) => {
            let name = id.get_name();
            if is_nt(name) {
                Node::Nt(name.to_string())
            } else {
                Node::Leaf(name.to_string())
            }
        }
        SyGuSTerm::Application(id, args) => Node::App(
            id.get_name().to_string(),
            args.iter().map(|a| node_of(a, is_nt)).collect(),
        ),
        SyGuSTerm::Annotated(inner, _) => node_of(inner, is_nt),
        SyGuSTerm::Literal(lit) => Node::Leaf(lit.to_string()),
        // Let/quantifiers don't appear in these grammars; render verbatim so a
        // mismatch is visible rather than silently dropped.
        other => Node::Leaf(other.to_string()),
    }
}

/// Render a skeleton. Holes become `h{i}` (collecting their sorts) unless
/// `values` supplies concrete constants; the DFS order matches `check`.
fn render(skel: &Skel, sorts: &mut Vec<String>, values: Option<&[String]>) -> String {
    match skel {
        Skel::Hole(sort) => {
            let i = sorts.len();
            sorts.push(sort.clone());
            match values {
                Some(v) => v[i].clone(),
                None => format!("h{i}"),
            }
        }
        Skel::Leaf(s) => s.clone(),
        Skel::App(head, kids) => {
            let rendered = kids
                .iter()
                .map(|k| render(k, sorts, values))
                .collect::<Vec<_>>()
                .join(" ");
            format!("({head} {rendered})")
        }
    }
}

fn bitvec_width(sort: &str) -> Option<usize> {
    sort.strip_prefix("(_ BitVec ")
        .and_then(|rest| rest.strip_suffix(')'))?
        .trim()
        .parse()
        .ok()
}

fn default_value(sort: &str) -> Option<String> {
    if sort == "Bool" {
        return Some("false".to_string());
    }
    let width = bitvec_width(sort)?;
    Some(format!("(_ bv0 {width})"))
}

// ---------------------------------------------------------------------------
//  Canonical keys (apply the recognized `OpLaws` to a skeleton).
// ---------------------------------------------------------------------------

/// Structural children (the `Constant` holes — always trailing `Ann` args —
/// carry no grammar meaning, so they're dropped from the canonical key).
fn structural(kids: &[Skel]) -> Vec<&Skel> {
    kids.iter()
        .filter(|k| !matches!(k, Skel::Hole(_)))
        .collect()
}

/// Canonical key of a skeleton modulo the declared laws: associative ops are
/// flattened to a sequence; set-cons families are collected along their spine
/// and sorted/dedup'd. Equal keys ⇒ same grammar ⇒ same SAT result.
fn canon(skel: &Skel, laws: &crate::laws::OpLaws) -> String {
    match skel {
        Skel::Hole(_) => "_".to_string(),
        Skel::Leaf(s) => s.clone(),
        Skel::App(head, kids) => {
            if laws.set_ops.contains_key(head) {
                let mut elems = Vec::new();
                let mut cur = skel;
                while let Skel::App(h, k) = cur {
                    let Some(&(ei, si)) = laws.set_ops.get(h) else {
                        break;
                    };
                    let st = structural(k);
                    let elem = canon(st[ei], laws);
                    if !laws
                        .set_drop
                        .get(h)
                        .is_some_and(|drop| drop.contains(&elem))
                    {
                        elems.push(elem);
                    }
                    cur = st[si];
                }
                if laws.set_commute {
                    elems.sort();
                }
                if laws.set_idemp {
                    elems.dedup();
                }
                format!("{{set|{}|{}}}", canon(cur, laws), elems.join(","))
            } else if laws.assoc.contains(head) {
                let mut seq = Vec::new();
                flatten_assoc(skel, head, laws, &mut seq);
                format!("({head} {})", seq.join(" "))
            } else {
                let st = structural(kids);
                if st.is_empty() {
                    head.clone()
                } else {
                    let parts: Vec<String> = st.iter().map(|c| canon(c, laws)).collect();
                    format!("({head} {})", parts.join(" "))
                }
            }
        }
    }
}

fn flatten_assoc(skel: &Skel, op: &str, laws: &crate::laws::OpLaws, out: &mut Vec<String>) {
    if let Skel::App(h, kids) = skel {
        if h == op {
            for k in structural(kids) {
                flatten_assoc(k, op, laws, out);
            }
            return;
        }
    }
    out.push(canon(skel, laws));
}

/// Truncate a rendered skeleton for log lines.
fn summarize(body: &str) -> String {
    const LIMIT: usize = 120;
    if body.len() <= LIMIT {
        body.to_string()
    } else {
        format!("{}… <{} chars>", &body[..LIMIT], body.len())
    }
}

/// All compositions of `total` into `k` nonnegative parts.
fn splits(total: usize, k: usize) -> Vec<Vec<usize>> {
    if k == 0 {
        return if total == 0 { vec![vec![]] } else { vec![] };
    }
    if k == 1 {
        return vec![vec![total]];
    }
    let mut out = Vec::new();
    for first in 0..=total {
        for mut rest in splits(total - first, k - 1) {
            let mut v = Vec::with_capacity(k);
            v.push(first);
            v.append(&mut rest);
            out.push(v);
        }
    }
    out
}

/// Cartesian product of candidate pools, one pick per pool.
fn product(pools: &[Vec<Skel>]) -> Vec<Vec<Skel>> {
    let mut acc: Vec<Vec<Skel>> = vec![Vec::new()];
    for pool in pools {
        let mut next = Vec::new();
        for prefix in &acc {
            for item in pool {
                let mut row = prefix.clone();
                row.push(item.clone());
                next.push(row);
            }
        }
        acc = next;
    }
    acc
}

// ---------------------------------------------------------------------------
//  SMT backend — z3 via rsmt2 (mirrors cegis.rs). Solver values are read back
//  as raw source strings and substituted verbatim into the skeleton.
// ---------------------------------------------------------------------------

#[derive(Clone, Copy)]
struct Parser;

impl<'a> IdentParser<String, String, &'a str> for Parser {
    fn parse_ident(self, input: &'a str) -> SmtRes<String> {
        Ok(input.into())
    }
    fn parse_type(self, input: &'a str) -> SmtRes<String> {
        Ok(input.into())
    }
}

impl<'a> ModelParser<String, String, String, &'a str> for Parser {
    fn parse_value(
        self,
        input: &'a str,
        _ident: &String,
        _params: &[(String, String)],
        _typ: &String,
    ) -> SmtRes<String> {
        Ok(input.into())
    }
}
