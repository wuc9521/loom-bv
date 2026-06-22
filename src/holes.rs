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

use std::collections::HashMap;
use std::io::Write as _;
use std::process::{Command, Stdio};

use sygus_parser::ast::{SyGuSGTerm, SyGuSTerm};

use crate::parse::ProgramEnv;
use crate::{debg, info};

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

pub struct HoleSpec {
    synth_name: String,
    ret_sort: String,
    start: String,
    prods: HashMap<String, Vec<Tmpl>>,
    /// SMT-LIB preamble: the input's define-funs verbatim.
    defines: String,
    /// The constraints, rendered verbatim as `(assert …)`.
    asserts: String,
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
            .map(|d| {
                let args = d
                    .args
                    .iter()
                    .map(|a| format!("({} {})", a.name, a.sort))
                    .collect::<Vec<_>>()
                    .join(" ");
                format!("(define-fun {} ({}) {} {})", d.name, args, d.ret, d.body)
            })
            .collect::<Vec<_>>()
            .join("\n");
        let asserts = view
            .constraints
            .iter()
            .map(|c| format!("(assert {})", c))
            .collect::<Vec<_>>()
            .join("\n");

        Some(HoleSpec {
            synth_name: sf.name.to_string(),
            ret_sort: sf.ret.to_string(),
            start: grammar.grouped_rule_lists[0].symbol.to_string(),
            prods,
            defines,
            asserts,
        })
    }

    /// Enumerate skeletons in increasing size; for each, SMT-solve the holes.
    /// Returns the inner `(define-fun …)` for the first satisfiable skeleton.
    pub fn solve(&self) -> crate::SolverResult<String> {
        info!(
            "const-hole search: synth={} start={} nonterminals={} recursive={} solver=z3",
            self.synth_name,
            self.start,
            self.prods.len(),
            self.is_recursive(),
        );
        let max_size: usize = std::env::var("DRYAD_HOLE_MAX_SIZE")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(usize::MAX);

        // A recursive grammar admits unboundedly large trees, so we never stop
        // on an empty size (completeness). A finite grammar has a maximum size;
        // once skeletons stop appearing for longer than any derivation, we're
        // done. Small sizes are legitimately empty before the minimum tree.
        let recursive = self.is_recursive();
        let empty_cap = self.prods.len() + 2;
        let mut seen_any = false;
        let mut empty_streak = 0usize;

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
            info!("const-hole: size {size}: {} skeleton(s)", skels.len());
            let size_start = std::time::Instant::now();
            for skel in &skels {
                let mut sorts = Vec::new();
                let body = render(skel, &mut sorts, None);
                tried += 1;
                let t = std::time::Instant::now();
                let res = self.check(&body, &sorts)?;
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
                        "const-hole: SAT after {tried} skeletons (size {size}, {:?} at this size)",
                        size_start.elapsed()
                    );
                    return Ok(format!(
                        "(define-fun {} () {} {})",
                        self.synth_name, self.ret_sort, filled
                    ));
                }
            }
            debg!("const-hole: size {size} exhausted ({tried} skeletons total)");
        }
        Err("const-hole: no solution within DRYAD_HOLE_MAX_SIZE".into())
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

    /// Build the QF_BV query for one skeleton and run z3.
    /// `Some(values)` on SAT (one per hole, in DFS order); `None` on UNSAT.
    fn check(&self, body: &str, hole_sorts: &[String]) -> crate::SolverResult<Option<Vec<String>>> {
        let mut smt = String::new();
        smt.push_str("(set-logic QF_BV)\n(set-option :produce-models true)\n");
        smt.push_str(&self.defines);
        smt.push('\n');
        for (i, sort) in hole_sorts.iter().enumerate() {
            smt.push_str(&format!("(declare-const h{i} {sort})\n"));
        }
        smt.push_str(&format!(
            "(define-fun {} () {} {})\n",
            self.synth_name, self.ret_sort, body
        ));
        smt.push_str(&self.asserts);
        smt.push_str("\n(check-sat)\n");
        if !hole_sorts.is_empty() {
            let names = (0..hole_sorts.len())
                .map(|i| format!("h{i}"))
                .collect::<Vec<_>>()
                .join(" ");
            smt.push_str(&format!("(get-value ({names}))\n"));
        }
        let out = run_z3(&smt)?;
        // Distinguish genuine unsat from a solver that errored/couldn't decide:
        // treating an error as unsat would silently skip a satisfiable skeleton.
        match out.split_whitespace().next() {
            Some("unsat") => return Ok(None),
            Some("sat") => {}
            _ => return Err(format!("z3 gave no decision: {}", out.trim()).into()),
        }
        let model = parse_model(&out);
        let values = (0..hole_sorts.len())
            .map(|i| {
                model
                    .get(&format!("h{i}"))
                    .cloned()
                    .ok_or_else(|| format!("solver model missing h{i}"))
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Some(values))
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
//  SMT backend — z3 subprocess over stdin. z3 measured fastest on these
//  founded-annotation QF_BV queries (UNSAT-dominated, wide bit-vectors):
//  ~1.4× over cvc5 and ~2× over bitwuzla.
// ---------------------------------------------------------------------------

fn run_z3(smt: &str) -> crate::SolverResult<String> {
    let mut child = Command::new("z3")
        .args(["-smt2", "-in"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .map_err(|e| format!("failed to spawn z3 (is it on PATH?): {e}"))?;
    // Ignore a write error: z3 may reject the input and exit before consuming
    // all of stdin (BrokenPipe). We still read its output.
    {
        let mut stdin = child.stdin.take().unwrap();
        let _ = stdin.write_all(smt.as_bytes());
    }
    let out = child.wait_with_output()?;
    Ok(String::from_utf8_lossy(&out.stdout).into_owned())
}

/// Parse a `(get-value …)` reply into name → value-source, e.g.
/// `((h0 #b…) (h1 (_ bv0 8)))`.
fn parse_model(out: &str) -> HashMap<String, String> {
    let mut map = HashMap::new();
    // Parse from the first '(' after the sat line.
    let Some(start) = out.find('(') else {
        return map;
    };
    let sx = match Sx::parse(&out[start..]) {
        Some((sx, _)) => sx,
        None => return map,
    };
    if let Sx::List(pairs) = sx {
        for pair in pairs {
            if let Sx::List(kv) = pair {
                if kv.len() == 2 {
                    map.insert(kv[0].to_src(), kv[1].to_src());
                }
            }
        }
    }
    map
}

/// Minimal S-expression reader for solver replies.
enum Sx {
    Atom(String),
    List(Vec<Sx>),
}

impl Sx {
    fn parse(s: &str) -> Option<(Sx, usize)> {
        let bytes = s.as_bytes();
        let mut i = 0;
        while i < bytes.len() && bytes[i].is_ascii_whitespace() {
            i += 1;
        }
        if i >= bytes.len() {
            return None;
        }
        if bytes[i] == b'(' {
            i += 1;
            let mut items = Vec::new();
            loop {
                while i < bytes.len() && bytes[i].is_ascii_whitespace() {
                    i += 1;
                }
                if i >= bytes.len() {
                    return None;
                }
                if bytes[i] == b')' {
                    i += 1;
                    return Some((Sx::List(items), i));
                }
                let (child, used) = Sx::parse(&s[i..])?;
                items.push(child);
                i += used;
            }
        } else {
            let start = i;
            while i < bytes.len() && !bytes[i].is_ascii_whitespace() && bytes[i] != b'(' && bytes[i] != b')' {
                i += 1;
            }
            Some((Sx::Atom(s[start..i].to_string()), i))
        }
    }

    fn to_src(&self) -> String {
        match self {
            Sx::Atom(a) => a.clone(),
            Sx::List(items) => format!(
                "({})",
                items.iter().map(Sx::to_src).collect::<Vec<_>>().join(" ")
            ),
        }
    }
}
