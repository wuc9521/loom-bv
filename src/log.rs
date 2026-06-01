use std::cell::RefCell;
use std::sync::atomic::{AtomicU8, Ordering};

/// Numeric log level shared across the crate.  Higher = more verbose.
///   0 = silent       1 = `crit!`         2 = `warn!`
///   3 = `info!`      4 = `debg!`         5 = `debg2!`
///
/// The caller (delis or the standalone binary) sets this via
/// `log::set_log_level(verbose + 2)`, so `--verbose 0` keeps WARN; `-v`/`-vv`
/// from delis enable INFO / DEBUG respectively.
pub static LOGLEVEL: AtomicU8 = AtomicU8::new(2);
thread_local! {
    pub static INDENT: RefCell<String> = RefCell::new(String::from(""));
}

pub fn set_log_level(level: u8) {
    LOGLEVEL.store(level, Ordering::Relaxed);
}
pub fn log_level() -> u8 {
    LOGLEVEL.load(Ordering::Relaxed)
}

// Format conventions (matched to delis's env_logger format):
//   info!  → bare message  (the bulk of useful output)
//   warn!  → "warning: msg"
//   crit!  → "error: msg"
//   debg!  → "debug: msg (file:line)"
//   debg2! → "trace: msg (file:line)"
// No ANSI colors, no `{:?}` quoting of the message — pass-through.

#[macro_export]
macro_rules! info {
    ($($fmt:tt)+) => {
        if $crate::log::LOGLEVEL.load(std::sync::atomic::Ordering::Relaxed) >= 3 {
            $crate::log::INDENT.with_borrow(|s| {
                eprintln!("{}{}", s, format_args!($($fmt)+))
            })
        }
    };
}

#[macro_export]
macro_rules! debg {
    ($($fmt:tt)+) => {
        if $crate::log::LOGLEVEL.load(std::sync::atomic::Ordering::Relaxed) >= 4 {
            $crate::log::INDENT.with_borrow(|s| {
                eprintln!("debug: {}{} ({}:{})", s, format_args!($($fmt)+), file!(), line!())
            })
        }
    };
}

#[macro_export]
macro_rules! debg2 {
    ($($fmt:tt)+) => {
        if $crate::log::LOGLEVEL.load(std::sync::atomic::Ordering::Relaxed) >= 5 {
            $crate::log::INDENT.with_borrow(|s| {
                eprintln!("trace: {}{} ({}:{})", s, format_args!($($fmt)+), file!(), line!())
            })
        }
    };
}

#[macro_export]
macro_rules! crit {
    ($($fmt:tt)+) => {
        if $crate::log::LOGLEVEL.load(std::sync::atomic::Ordering::Relaxed) >= 1 {
            $crate::log::INDENT.with_borrow(|s| {
                eprintln!("error: {}{}", s, format_args!($($fmt)+))
            })
        }
    };
}

#[macro_export]
macro_rules! warn {
    ($($fmt:tt)+) => {
        if $crate::log::LOGLEVEL.load(std::sync::atomic::Ordering::Relaxed) >= 2 {
            $crate::log::INDENT.with_borrow(|s| {
                eprintln!("warning: {}{}", s, format_args!($($fmt)+))
            })
        }
    };
}
