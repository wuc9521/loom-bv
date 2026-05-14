#![feature(portable_simd)]
#![feature(map_try_insert)]
#![feature(int_roundings)]

use clap::{builder::BoolishValueParser, Parser};
use std::{env, fs, io::Read};

#[cfg(feature = "dhat-heap")]
#[global_allocator]
static ALLOC: dhat::Alloc = dhat::Alloc;

#[derive(Debug, Parser)]
#[command(name = "bvmiddle")]
struct Cli {
    #[arg(short, long, action = clap::ArgAction::Count)]
    verbose: u8,
    path: String,
    #[arg(short, long)]
    config: Option<String>,

    /// Enable exact-nullary relevance (bit minimization); use --min=false to disable.
    #[arg(
        long = "min",
        default_value_t = true,
        default_missing_value = "true",
        num_args = 0..=1,
        require_equals = true,
        value_parser = BoolishValueParser::new()
    )]
    min: bool,

    #[arg(long = "mitm", default_value_t = false)]
    mitm: bool,
}

pub fn main() -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    #[cfg(feature = "dhat-heap")]
    let _profiler = dhat::Profiler::new_heap();

    const STDIN_SENTINEL: &str = "__CODEX_STDIN__";
    let raw_args = env::args().map(|arg| {
        if arg == "-in" {
            STDIN_SENTINEL.to_string()
        } else {
            arg
        }
    });
    let args = Cli::parse_from(raw_args);
    let input = if args.path == STDIN_SENTINEL {
        let mut buf = String::new();
        std::io::stdin().read_to_string(&mut buf)?;
        buf
    } else {
        fs::read_to_string(&args.path)?
    };

    let mut description = String::new();
    for line in input.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with(';') {
            description.push_str(&trimmed[1..]);
        } else {
            break;
        }
    }

    let file = sygus_parser::ast::SyGuSFile::from_str(&input)
        .map_err(|e| format!("SyGuS parse failed: {e}"))?;
    let output = dryadsynth_bv::solve_sygus_file(
        &file,
        args.config.as_deref(),
        &description,
        None,
        args.verbose,
        args.min,
        args.mitm,
    )?;
    println!("{output}");
    Ok(())
}
