#![feature(portable_simd)]
#![feature(map_try_insert)]
#![feature(int_roundings)]

use std::{env, fs, io::Read, sync::mpsc, thread};

use clap::Parser;
use enumerate::expr::OwnedExpr;
use figment::{
    providers::{Format, Serialized, Toml},
    Figment,
};
use itertools::Itertools;
use parse::{constraint::RefImplConstraint, deffun, PbeConstraint};
use sygus_parser::ast::SyGuSFile;

use crate::{exact::NullarySpec, parse::SynthProblem, search::search::SearchConfig};
extern crate pest;

mod cegis;
pub mod chatgpt;
mod deductive;
mod enumerate;
mod exact;
pub mod hash;
mod log;
mod parse;
mod search;
mod solutions;
mod tree_learning;

#[derive(Debug, Parser)] // requires `derive` feature
#[command(name = "bvmiddle")]
struct Cli {
    #[arg(short, long, action = clap::ArgAction::Count)]
    verbose: u8,
    path: String,
    #[arg(short, long)]
    config: Option<String>,
}

// pub fn solve_pbe(problem: SynthProblem, pbecstr: PbeConstraint) -> Self

fn main_inner(
) -> Result<(SynthProblem<'static>, OwnedExpr), Box<dyn std::error::Error + Send + Sync>> {
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

    const STDIN_SENTINEL: &str = "__CODEX_STDIN__";
    let raw_args = env::args().map(|arg| {
        if arg == "-in" {
            STDIN_SENTINEL.to_string()
        } else {
            arg
        }
    });
    let args = Cli::parse_from(raw_args);
    log::set_log_level(args.verbose + 2);
    unsafe {
        env::set_var("RUST_MIN_STACK", "268435456");
    }

    let input_data = if args.path == STDIN_SENTINEL {
        let mut buf = String::new();
        std::io::stdin().read_to_string(&mut buf)?;
        buf
    } else {
        fs::read_to_string(&args.path)?
    };
    let input = Box::leak(input_data.into_boxed_str());

    let mut description = String::new();
    for a in input.split("\n") {
        let b = a.trim();
        if b.starts_with(";") {
            description.push_str(&b[1..]);
        } else {
            break;
        }
    }

    let file = SyGuSFile::from_str(&input).map_err(|e| format!("SyGuS parse failed: {e}"))?;
    // warn!("SyGuS file parsed, total cmds={}", file.cmds.len());
    deffun::ENV.parse_from_file(&file)?;
    let mut problem = SynthProblem::parse_from_file(&file)?;
    problem.description = description;
    let pbecstr = PbeConstraint::parse_from_file(problem.name, problem.args.len(), &file)?;
    if let Some(spec) = NullarySpec::from_file(&file, &problem)? {
        let result = exact::search_nullary(&problem, &spec)?;
        return Ok((problem, result));
    }
    if pbecstr.len() > 0 {
        let fig = Figment::new().merge(Serialized::defaults(SearchConfig::default_pbe()));
        let fig = if let Some(path) = args.config {
            fig.merge(Toml::file(path))
        } else {
            fig
        };
        let mut config: SearchConfig = fig.extract()?;
        config.is_pbe = true;

        let result = config.search(&problem, &pbecstr, PbeConstraint::new(problem.args.len()))?;
        Ok((problem, result))
    } else if let Some(refimpl) =
        RefImplConstraint::parse_from_file(&file, problem.name, problem.args.len())?
    {
        let original_problem = problem.clone();
        let fig = Figment::new().merge(Serialized::defaults(SearchConfig::default_refimpl()));
        let fig = if let Some(path) = args.config {
            fig.merge(Toml::file(path))
        } else {
            fig
        };
        let mut config: SearchConfig = fig.extract()?;
        if config.chatgpt {
            if let Ok(key) = env::var("OPENAI_API_KEY").or(env::var("OPENAI_API")) {
                unsafe {
                    env::set_var("OPENAI_KEY", key);
                };
            } else {
                config.chatgpt = false;
            }
        }
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
                let pbe = refimpl.generate_pbe(3, problem.args.len(), &mut config.rng());
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
                    .flat_map(|(e, i)| {
                        if i >= 4 && e.size() < 10 {
                            Some(e)
                        } else {
                            None
                        }
                    })
                    .collect_vec();
                if v.len() > 0 {
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
            Ok((original_problem, a))
        } else {
            let result = run_cegis_with_large_stack(config, problem, refimpl)
                .map_err(|e| format!("cegis failed: {e}"))?;
            Ok((original_problem, result))
        }
    } else {
        panic!()
    }
}

#[cfg(feature = "dhat-heap")]
#[global_allocator]
static ALLOC: dhat::Alloc = dhat::Alloc;

pub fn main() -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    #[cfg(feature = "dhat-heap")]
    let _profiler = dhat::Profiler::new_heap();

    const MAIN_STACK_SIZE: usize = 256 * 1024 * 1024;
    let handle = thread::Builder::new()
        .name("main-worker".to_string())
        .stack_size(MAIN_STACK_SIZE)
        .spawn(main_inner)
        .map_err(|e| format!("failed to spawn main worker: {e}"))?;
    let result = handle
        .join()
        .map_err(|_| "main worker panicked".to_string())??;
    println!("(\n{}\n)", result.0.format_solution(&result.1));
    Ok(())
}
