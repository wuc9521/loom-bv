mod pbe;
mod refimpl;

use pest::Span;
use sygus_parser::ast::{Identifier, Literal as SyGuSLiteral, SyGuSTerm};

use crate::enumerate::value::Value;

use super::{literals, new_custom_error_span, Error};

pub use pbe::PbeConstraint;
pub use refimpl::RefImplConstraint;

fn empty_span() -> Span<'static> {
    Span::new("", 0, 0).expect("empty span should be valid")
}

fn literal_to_value(lit: &SyGuSLiteral) -> Result<Value, Error> {
    match lit {
        SyGuSLiteral::Numeral(v) => Ok(Value::from_u64(*v as u64, 64)),
        SyGuSLiteral::Bool(v) => Ok(Value::from_u64(if *v { 1 } else { 0 }, 1)),
        SyGuSLiteral::HexConst(v) => {
            let s = if v.starts_with("#x") {
                v.clone()
            } else {
                format!("#x{}", v)
            };
            let bits = v.trim_start_matches("#x").len() * 4;
            literals::value_constant(&s, bits.max(1), empty_span())
        }
        SyGuSLiteral::BinConst(v) => {
            let s = if v.starts_with("#b") {
                v.clone()
            } else {
                format!("#b{}", v)
            };
            let bits = v.trim_start_matches("#b").len();
            literals::value_constant(&s, bits.max(1), empty_span())
        }
        SyGuSLiteral::Decimal(_) | SyGuSLiteral::StringConst(_) => Err(new_custom_error_span(
            "Constraint parser: expecting a SyGuS constant literal".into(),
            empty_span(),
        )),
    }
}

fn term_app(term: &SyGuSTerm) -> Option<(&str, &[SyGuSTerm])> {
    let SyGuSTerm::Application(id, args) = term else {
        return None;
    };
    Some((id.get_name(), args.as_slice()))
}

fn term_eq(term: &SyGuSTerm) -> Option<(&SyGuSTerm, &SyGuSTerm)> {
    let ("=", args) = term_app(term)? else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    Some((&args[0], &args[1]))
}

fn term_call_to<'a>(term: &'a SyGuSTerm, name: &str, arity: usize) -> Option<&'a [SyGuSTerm]> {
    let (head, args) = term_app(term)?;
    if head == name && args.len() == arity {
        Some(args)
    } else {
        None
    }
}

fn term_var_name(term: &SyGuSTerm) -> Option<&str> {
    let SyGuSTerm::Identifier(Identifier::Symbol(name)) = term else {
        return None;
    };
    Some(name)
}
