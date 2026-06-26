#![feature(portable_simd)]
#![feature(map_try_insert)]
#![feature(int_roundings)]

use enumerate::expr::OwnedExpr;
use figment::{
    providers::{Format, Serialized, Toml},
    Figment,
};
#[cfg(feature = "chatgpt")]
use itertools::Itertools;
use parse::{constraint::parse_ref_impl, deffun, ProgramEnv};
#[cfg(feature = "chatgpt")]
use std::sync::mpsc;
use std::{env, thread};
use sygus_parser::ast::{SyGuSCmd, SyGuSFile};

use crate::{exact::Constraint, parse::SynthProblem, search::search::SearchConfig};

mod cegis;
#[cfg(feature = "chatgpt")]
pub mod chatgpt;
mod deductive;
pub mod enumerate;
mod exact;
pub mod fwd_decls;
pub mod hash;
mod holes;
mod laws;
pub mod log;
pub mod parse;
pub mod search;
mod solutions;
mod tree_learning;

type SolverResult<T> = Result<T, Box<dyn std::error::Error + Send + Sync>>;

impl SynthProblem<'_> {
    fn has_ite(&self) -> bool {
        fn term_has_ite(term: &sygus_parser::ast::SyGuSTerm) -> bool {
            match term {
                sygus_parser::ast::SyGuSTerm::Application(id, args) => {
                    id.get_name() == "ite" || args.iter().any(term_has_ite)
                }
                sygus_parser::ast::SyGuSTerm::Annotated(inner, _) => term_has_ite(inner),
                sygus_parser::ast::SyGuSTerm::Let(bindings, body) => {
                    bindings.iter().any(|binding| term_has_ite(&binding.term)) || term_has_ite(body)
                }
                sygus_parser::ast::SyGuSTerm::Forall(_, body)
                | sygus_parser::ast::SyGuSTerm::Exists(_, body) => term_has_ite(body),
                _ => false,
            }
        }

        self.cfg.iter().any(|nt| {
            nt.1.iter().any(|rule| match rule {
                sygus_parser::ast::SyGuSGTerm::SyGuSTerm(term) => term_has_ite(&term),
                _ => false,
            })
        })
    }
}

fn run_cegis_with_large_stack(
    mut config: SearchConfig,
    problem: SynthProblem<'static>,
    ref_impl: OwnedExpr,
) -> Result<OwnedExpr, String> {
    const CEGIS_STACK_SIZE: usize = 256 * 1024 * 1024;
    let handle = thread::Builder::new()
        .name("cegis-worker".to_string())
        .stack_size(CEGIS_STACK_SIZE)
        .spawn(move || {
            config
                .cegis_loop(&problem, &ref_impl)
                .map_err(|e| e.to_string())
        })
        .map_err(|e| format!("failed to spawn cegis worker: {e}"))?;
    match handle.join() {
        Ok(res) => res,
        Err(_) => Err("cegis worker panicked".to_string()),
    }
}

/// Diagnostic: take a candidate body as an S-expression string, lift it
/// to an `OwnedExpr` via `from_term`, install it as the current synth
/// candidate, and report per-constraint pass/fail. Used to determine
/// whether `dryadsynth-bv`'s eval agrees with z3 on a hand-supplied
/// candidate that we already know the encoding admits.
fn probe_candidate(
    body_str: &str,
    spec: &exact::Constraint,
    view: &parse::ProgramEnv,
) -> SolverResult<()> {
    // Wrap the candidate body in a tiny SyGuS file so the parser yields
    // a single SyGuSTerm; reuse the same Pest grammar as the real parser.
    let wrapped = format!("(set-logic BV)(define-fun __probe () CFG {body_str})");
    let parsed = SyGuSFile::from_str(&wrapped)
        .map_err(|e| format!("probe: failed to parse candidate: {e}"))?;
    let define_body = parsed
        .cmds
        .iter()
        .find_map(|c| match c {
            SyGuSCmd::DefineFun(_, _, _, body) => Some(body),
            _ => None,
        })
        .ok_or("probe: parsed file has no define-fun")?;
    let synth_env: Vec<(&str, u64)> = view
        .synth_funs
        .first()
        .map(|sf| {
            sf.args
                .iter()
                .filter_map(|a| {
                    view.sort_aliases
                        .parse_sort_width(&a.sort)
                        .map(|w| (a.name.as_str(), w as u64))
                })
                .collect()
        })
        .unwrap_or_default();
    let candidate = OwnedExpr::from_term(define_body, &synth_env)
        .map_err(|e| format!("probe: failed to lift candidate: {e}"))?;
    debg!("probe candidate: {}", candidate.summarize(200));
    deffun::set_candidate(0, Some(candidate));
    let total = spec.structural.len();
    let mut violated: Vec<usize> = Vec::new();
    for (i, expr) in spec.structural.iter().enumerate() {
        match expr.eval(&[]) {
            Ok(v) => {
                if !v.as_bool().holds() {
                    violated.push(i);
                }
            }
            Err(e) => {
                debg!("probe: structural[{i}] eval errored: {e:?}");
                violated.push(i);
            }
        }
    }
    let matches = spec.matches(&[]);
    crate::info!(
        "probe: structural total={total}, violated={}, matches={matches}",
        violated.len()
    );
    if !violated.is_empty() && violated.len() <= 20 {
        crate::info!("probe: violated indices: {:?}", violated);
    }
    let _ = view;
    Ok(())
}

fn fwd_decls_solve(
    view: &ProgramEnv<'_>,
    problem: &fwd_decls::FwdDeclsProblem,
    min: bool,
    _config_path: Option<&str>,
) -> SolverResult<OwnedExpr> {
    use crate::enumerate::grammar::Config;
    use crate::exact::{search::run_search, types::Grammar};

    // The fwd-decls auxiliaries are not enumerated — their values come
    // from the LFP iteration in the verifier. `parse_from_view` picks
    // the synth-fun with a non-trivial grammar, which is exactly the
    // entry point in our shape.
    let stub = parse::SynthProblem::parse_from_view(view)?;
    let multi = Config::from_problem(&stub)?;
    let grammar = Grammar::from_config(&multi);
    let result = run_search(grammar, problem, min, false)
        .map_err(|e| format!("fwd-decls search failed: {e}"))?;
    Ok(result)
}

fn format_fwd_decls_solution(
    view: &ProgramEnv<'_>,
    problem: &fwd_decls::FwdDeclsProblem,
    result: &OwnedExpr,
) -> String {
    // Returns the inner `(define-fun …)` only; the caller
    // (`solve_sygus_file`) supplies the outer `(\n…\n)` wrapping.
    let entry_sf = view.synth_funs[problem.entry_synth_idx];
    let arg_decls: String = entry_sf
        .args
        .iter()
        .map(|a| format!("({} {})", a.name, a.sort))
        .collect::<Vec<_>>()
        .join(" ");
    format!(
        "(define-fun {} ({}) {} {})",
        entry_sf.name, arg_decls, entry_sf.ret, result
    )
}

fn solve_file_inner(
    file: &SyGuSFile,
    config_path: Option<&str>,
    description: String,
    min: bool,
) -> SolverResult<String> {
    let view = ProgramEnv::from_file(file);

    // Constant-hole pattern: a single nullary synth-fun whose grammar uses the
    // SyGuS `(Constant T)` construct (which the value enumerator drops).
    // Self-contained — passes define-funs verbatim to an SMT backend, so it
    // runs before the internal define-fun lowering (which rejects some shapes).
    if let Some(spec) = holes::HoleSpec::detect(&view) {
        return spec.solve();
    }

    deffun::ENV.clear();
    // Register synth-funs so `OwnedExpr::from_term` recognises their
    // names in Application position (producing `SynthApp`) — needed for
    // parent-spec emissions from delis (`(g a_arg b_arg c_arg)` inside
    // a Kleene-chain define-fun body).
    let synth_registry: Vec<deffun::SynthEntry> =
        view.synth_funs
            .iter()
            .map(|sf| -> SolverResult<_> {
                let ret_bits =
                    view.sort_aliases.parse_sort_width(sf.ret).ok_or_else(|| {
                        format!("synth-fun {} return sort: not a bit-vector", sf.name)
                    })? as usize;
                Ok(deffun::SynthEntry {
                    name: sf.name.to_string(),
                    arity: sf.args.len(),
                    ret_bits,
                })
            })
            .collect::<SolverResult<Vec<_>>>()?;
    deffun::set_synth_registry(&synth_registry);
    deffun::ENV.parse_from_view(&view)?;

    // SyGuS 2.1 :fwd-decls — when the file declares multiple synth-funs
    // and the entry point's grammar references the others as terminals,
    // route through the fwd-decls solver (LFP iteration per candidate).
    if view.features.fwd_decls && view.synth_funs.len() > 1 {
        let problem = fwd_decls::FwdDeclsProblem::from_view(&view)?;
        debg!(
            "fwd-decls search: entry={} entry_bits={} recipes={} bit_asserts={}",
            view.synth_funs[problem.entry_synth_idx].name,
            problem.entry_bits,
            problem.recipes.len(),
            problem.bit_asserts.len()
        );
        let result = fwd_decls_solve(&view, &problem, min, config_path)?;
        return Ok(format_fwd_decls_solution(&view, &problem, &result));
    }

    // LFP pattern: route through the specialized LfpSpec path when the
    // problem has the two-synth-fun closure shape that SynthProblem can't
    // represent (multiple synth-funs).
    if view.synth_funs.len() > 1 {
        if let Some(spec) = exact::lfp::LfpSpec::detect(&view) {
            debg!(
                "lfp-closure search: {} (bits={}, labels={})",
                spec.variant_tag(),
                spec.bits(),
                spec.labels().len()
            );
            return spec
                .search(&deffun::ENV)?
                .ok_or_else(|| "lfp: no solution".to_string().into());
        }
    }

    let mut problem = SynthProblem::parse_from_view(&view)?;
    problem.description = description;
    let pbecstr =
        Constraint::parse_pbe_from_view(problem.name, problem.args.len(), problem.bits, &view)?;
    if let Some(spec) = exact::Constraint::from_file(file, &problem)? {
        debg!(
            "exact search: {} (bits={}, examples={}, cmds={})",
            problem.name,
            problem.bits,
            spec.num_examples(),
            file.cmds.len()
        );
        if let Ok(probe) = env::var("DRYAD_PROBE_G") {
            probe_candidate(&probe, &spec, &view)?;
            return Ok(String::from("(probe-only run)"));
        }
        let fig = Figment::new().merge(Serialized::defaults(SearchConfig::default_exact()));
        let fig = if let Some(path) = config_path {
            fig.merge(Toml::file(path))
        } else {
            fig
        };
        let mut config: SearchConfig = fig.extract()?;
        config.min = min;
        if env::var("DRYADSYNTH_COMPOSITION").is_ok() {
            config.enable_composition = true;
        }
        let result = config.search(
            &problem,
            &spec,
            Constraint::empty(problem.args.len(), problem.bits),
        )?;
        return Ok(problem.format_solution(&result));
    }
    if pbecstr.len() > 0 {
        let fig = Figment::new().merge(Serialized::defaults(SearchConfig::default_pbe()));
        let fig = if let Some(path) = config_path {
            fig.merge(Toml::file(path))
        } else {
            fig
        };
        let mut config: SearchConfig = fig.extract()?;
        config.is_pbe = true;
        config.min = min;
        config.min = min;
        let result = config.search(
            &problem,
            &pbecstr,
            Constraint::empty(problem.args.len(), problem.bits),
        )?;
        Ok(problem.format_solution(&result))
    } else if let Some(ref_impl) = parse_ref_impl(&view, problem.name, problem.args.len())? {
        let original_problem = problem.clone();
        let defaults = if problem.has_ite() {
            SearchConfig::default_refimpl()
        } else {
            SearchConfig::default_refimpl_classic()
        };
        let fig = Figment::new().merge(Serialized::defaults(defaults));
        let fig = if let Some(path) = config_path {
            fig.merge(Toml::file(path))
        } else {
            fig
        };
        let mut config: SearchConfig = fig.extract()?;
        if config.chatgpt {
            #[cfg(not(feature = "chatgpt"))]
            {
                config.chatgpt = false;
            }
            #[cfg(feature = "chatgpt")]
            if let Ok(key) = env::var("OPENAI_API_KEY").or(env::var("OPENAI_API")) {
                unsafe {
                    env::set_var("OPENAI_KEY", key);
                };
            } else {
                config.chatgpt = false;
            }
        }
        #[cfg(feature = "chatgpt")]
        if config.chatgpt && problem.description != "" {
            let l = log::log_level();
            let (sender, receiver) = mpsc::channel();
            let sd = sender.clone();
            let _ = thread::spawn({
                let (config, problem, ref_impl) =
                    (config.clone(), problem.clone(), ref_impl.clone());
                move || sd.send(run_cegis_with_large_stack(config, problem, ref_impl))
            });
            let _ = thread::spawn(move || {
                log::set_log_level(l);
                let pbe = parse::constraint::generate_pbe(
                    &ref_impl,
                    3,
                    problem.args.len(),
                    problem.bits,
                    &mut config.rng(),
                );
                info!("Use ChatGPT to guide the search");
                let result = chatgpt::ask(&problem, pbe.clone(), config.gpt_version.clone());
                info!("Use ChatGPT to guide the search: {:?}", result);
                for r in result.iter() {
                    if let Some(last) = r.get("last") {
                        if pbe.test_owned(last).len() >= 3 {
                            if config.cegis_check(&problem, &ref_impl, last) {
                                sender.send(Ok(last.clone())).unwrap();
                                return;
                            }
                        }
                    }
                }
                let map = chatgpt::collect_subexpr(result);
                let v = map
                    .into_iter()
                    .flat_map(|(e, i)| {
                        if i >= 4 && e.size() < 10 {
                            Some(e)
                        } else {
                            None
                        }
                    })
                    .collect_vec();
                if !v.is_empty() {
                    info!("Use ChatGPT to guide the search: {:?}", v);
                    problem.chatgpt_exprs = v;
                    sender
                        .send(run_cegis_with_large_stack(config, problem, ref_impl))
                        .unwrap();
                }
            });
            let a = receiver
                .recv()
                .unwrap()
                .map_err(|e| format!("cegis failed: {e}"))?;
            return Ok(original_problem.format_solution(&a));
        }
        let result = run_cegis_with_large_stack(config, problem, ref_impl)
            .map_err(|e| format!("cegis failed: {e}"))?;
        Ok(original_problem.format_solution(&result))
    } else {
        Err(format!(
            "Unsupported SyGuS benchmark shape for {}: expected PBE examples, a define-fun reference implementation, or a nullary bit-constraint task",
            problem.name
        )
        .into())
    }
}

fn solve_refuter_file_inner(
    file: &SyGuSFile,
    _config_path: Option<&str>,
    description: String,
    _min: bool,
) -> SolverResult<String> {
    let view = ProgramEnv::from_file(file);
    if let Some(spec) = holes::HoleSpec::detect(&view) {
        return spec.solve_refuter();
    }
    Err(format!(
        "Unsupported refuter SyGuS benchmark shape for {description}: expected a nullary const-hole task"
    )
    .into())
}

pub fn solve_sygus_file(
    file: &SyGuSFile,
    config_path: Option<&str>,
    description: &str,
    verbose: u8,
    min: bool,
) -> SolverResult<String> {
    log::set_log_level(verbose + 2);
    unsafe {
        env::set_var("RUST_MIN_STACK", "268435456");
    }
    const MAIN_STACK_SIZE: usize = 256 * 1024 * 1024;
    let file = file.clone();
    let config_path = config_path.map(str::to_string);
    let description = description.to_string();
    let handle = thread::Builder::new()
        .name("main-worker".to_string())
        .stack_size(MAIN_STACK_SIZE)
        .spawn(move || solve_file_inner(&file, config_path.as_deref(), description, min))
        .map_err(|e| format!("failed to spawn main worker: {e}"))?;
    let result = handle
        .join()
        .map_err(|_| "main worker panicked".to_string())??;
    Ok(format!("(\n{}\n)", result))
}

pub fn solve_refuter_sygus_file(
    file: &SyGuSFile,
    config_path: Option<&str>,
    description: &str,
    verbose: u8,
    min: bool,
) -> SolverResult<String> {
    log::set_log_level(verbose + 2);
    unsafe {
        env::set_var("RUST_MIN_STACK", "268435456");
    }
    const MAIN_STACK_SIZE: usize = 256 * 1024 * 1024;
    let file = file.clone();
    let config_path = config_path.map(str::to_string);
    let description = description.to_string();
    let handle = thread::Builder::new()
        .name("main-worker".to_string())
        .stack_size(MAIN_STACK_SIZE)
        .spawn(move || solve_refuter_file_inner(&file, config_path.as_deref(), description, min))
        .map_err(|e| format!("failed to spawn main worker: {e}"))?;
    let result = handle
        .join()
        .map_err(|_| "main worker panicked".to_string())??;
    Ok(format!("(\n{}\n)", result))
}

pub fn solve_sygus_cmds(
    cmds: &[SyGuSCmd],
    config_path: Option<&str>,
    description: &str,
    verbose: u8,
    min: bool,
) -> SolverResult<String> {
    let file = SyGuSFile {
        cmds: cmds.to_vec(),
    };
    match solve_sygus_file(&file, config_path, description, verbose, min) {
        Ok(result) => Ok(result),
        Err(err) => {
            let message = err.to_string();
            if !message.contains("Unsupported SyGuS benchmark shape") {
                return Err(err);
            }
            let mut normalized = Vec::new();
            sygus_parser::writer::write_cmds(&mut normalized, cmds)?;
            normalized.push(b'\n');
            let normalized = String::from_utf8(normalized)?;
            let reparsed = SyGuSFile::from_str(&normalized)
                .map_err(|e| format!("failed to normalize SyGuS commands: {e}"))?;
            solve_sygus_file(&reparsed, config_path, description, verbose, min)
        }
    }
}
