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
use parse::{constraint::RefImplConstraint, deffun, ProblemView};
use sygus_parser::ast::{SyGuSCmd, SyGuSFile};
#[cfg(feature = "chatgpt")]
use std::sync::mpsc;
use std::{env, thread};

use crate::{exact::Constraint, parse::SynthProblem, search::search::SearchConfig};

mod cegis;
#[cfg(feature = "chatgpt")]
pub mod chatgpt;
pub mod enumerate;
mod exact;
pub mod hash;
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
            sygus_parser::ast::SyGuSGTerm::SyGuSTerm(term) => term_has_ite(term),
            _ => false,
        })
    })
}
}

fn run_cegis_with_large_stack(
    mut config: SearchConfig,
    problem: SynthProblem<'static>,
    refimpl: RefImplConstraint,
) -> Result<OwnedExpr, String> {
    const CEGIS_STACK_SIZE: usize = 256 * 1024 * 1024;
    let handle = thread::Builder::new()
        .name("cegis-worker".to_string())
        .stack_size(CEGIS_STACK_SIZE)
        .spawn(move || {
            config
                .cegis_loop(&problem, &refimpl)
                .map_err(|e| e.to_string())
        })
        .map_err(|e| format!("failed to spawn cegis worker: {e}"))?;
    match handle.join() {
        Ok(res) => res,
        Err(_) => Err("cegis worker panicked".to_string()),
    }
}

fn solve_file_inner(
    file: &SyGuSFile,
    config_path: Option<&str>,
    description: String,
    min: bool,
) -> SolverResult<String> {
    let view = ProblemView::from_file(file);
    deffun::ENV.clear();
    deffun::ENV.parse_from_view(&view)?;

    // LFP pattern: either one self-referencing synth-fun, or two synth-funs
    // joined by a closure constraint. Handle before SynthProblem construction
    // because the latter assumes a single synth-fun.
    if let Some(spec) = exact::lfp::LfpSpec::detect(&view) {
        debg!(
            "lfp-closure search: {} (bits={}, labels={})",
            spec.variant_tag(),
            spec.bits(),
            spec.labels().len()
        );
        return spec.search(&deffun::ENV)?
            .ok_or_else(|| "lfp: no solution".to_string().into());
    }

    let mut problem = SynthProblem::parse_from_view(&view)?;
    problem.description = description;
    let pbecstr =
        Constraint::parse_pbe_from_view(problem.name, problem.args.len(), problem.bits, &view)?;
    if let Some(spec) = exact::Constraint::from_file(file, &problem)? {
        debg!(
            "exact search: {} (bits={}, examples={}, cmds={})",
            problem.name, problem.bits, spec.num_examples(), file.cmds.len()
        );
        let fig = Figment::new().merge(Serialized::defaults(SearchConfig::default_exact()));
        let fig = if let Some(path) = config_path {
            fig.merge(Toml::file(path))
        } else {
            fig
        };
        let mut config: SearchConfig = fig.extract()?;
        config.min = min;
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
    } else if let Some(refimpl) =
        RefImplConstraint::parse_from_view(&view, problem.name, problem.args.len())?
    {
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
                let (config, problem, refimpl) = (config.clone(), problem.clone(), refimpl.clone());
                move || sd.send(run_cegis_with_large_stack(config, problem, refimpl))
            });
            let _ = thread::spawn(move || {
                log::set_log_level(l);
                let pbe = refimpl.generate_pbe(3, problem.args.len(), problem.bits, &mut config.rng());
                info!("Use ChatGPT to guide the search");
                let result = chatgpt::ask(&problem, pbe.clone(), config.gpt_version.clone());
                info!("Use ChatGPT to guide the search: {:?}", result);
                for r in result.iter() {
                    if let Some(last) = r.get("last") {
                        if pbe.test_owned(last).len() >= 3 {
                            if config.cegis_check(&problem, &refimpl, last) {
                                sender.send(Ok(last.clone())).unwrap();
                                return;
                            }
                        }
                    }
                }
                let map = chatgpt::collect_subexpr(result);
                let v = map
                    .into_iter()
                    .flat_map(|(e, i)| if i >= 4 && e.size() < 10 { Some(e) } else { None })
                    .collect_vec();
                if !v.is_empty() {
                    info!("Use ChatGPT to guide the search: {:?}", v);
                    problem.chatgpt_exprs = v;
                    sender
                        .send(run_cegis_with_large_stack(config, problem, refimpl))
                        .unwrap();
                }
            });
            let a = receiver
                .recv()
                .unwrap()
                .map_err(|e| format!("cegis failed: {e}"))?;
            return Ok(original_problem.format_solution(&a));
        }
        let result = run_cegis_with_large_stack(config, problem, refimpl)
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

pub fn solve_sygus_file(
    file: &SyGuSFile,
    config_path: Option<&str>,
    description: &str,
    _axioms: Option<&[sygus_parser::ast::SyGuSTerm]>,
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

pub fn solve_sygus_cmds(
    cmds: &[SyGuSCmd],
    config_path: Option<&str>,
    description: &str,
    axioms: Option<&[sygus_parser::ast::SyGuSTerm]>,
    verbose: u8,
    min: bool,
) -> SolverResult<String> {
    let file = SyGuSFile { cmds: cmds.to_vec() };
    match solve_sygus_file(&file, config_path, description, axioms, verbose, min) {
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
            let reparsed =
                SyGuSFile::from_str(&normalized).map_err(|e| format!("failed to normalize SyGuS commands: {e}"))?;
            solve_sygus_file(&reparsed, config_path, description, axioms, verbose, min)
        }
    }
}
