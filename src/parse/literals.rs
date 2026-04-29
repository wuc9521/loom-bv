use nom::{branch::alt, bytes::complete::{tag, take_while1}, combinator::map_res, sequence::preceded, IResult};
use pest::Span;

use crate::enumerate::value::Value;

use super::{Error, new_custom_error_span};


fn u64_hex(input: &str) -> Result<u64, std::num::ParseIntError> {
    u64::from_str_radix(input, 16)
}
fn u64_binary(input: &str) -> Result<u64, std::num::ParseIntError> {
    u64::from_str_radix(input, 2)
}
fn u64_decimal(input: &str) -> Result<u64, std::num::ParseIntError> {
    u64::from_str_radix(input, 10)
}

pub fn u64_constant_python<'i>(input: &str) -> Option<u64> {
    let res : IResult<&str, u64> = alt((
        preceded(tag("0x"), map_res(take_while1(|x: char| x.is_digit(16)), u64_hex)),
        preceded(tag("0b"), map_res(take_while1(|x: char| x.is_digit(2)), u64_binary)),
        map_res(take_while1(|x: char| x.is_digit(10)), u64_decimal),
    ))(input);
    res.ok().map(|(_, y)| y)
}

pub fn u64_constant<'i>(input: &str, span: Span<'i>) -> Result<u64, Error> {
    fn overflow_err<'i>(span: Span<'i>, msg: &str) -> Error {
        new_custom_error_span(msg.to_string(), span)
    }

    if let Some(rest) = input.strip_prefix("#b") {
        let bits = rest.chars().filter(|c| *c == '0' || *c == '1').collect::<String>();
        let sig = bits.trim_start_matches('0');
        if sig.len() > 64 {
            return Err(overflow_err(
                span,
                &format!(
                    "Bitvector constant width {} exceeds engine limit 64 bits",
                    sig.len()
                ),
            ));
        }
    } else if let Some(rest) = input.strip_prefix("#x") {
        let sig = rest.trim_start_matches('0');
        if sig.len() > 16 {
            return Err(overflow_err(
                span,
                &format!(
                    "Bitvector constant width {} exceeds engine limit 64 bits",
                    sig.len() * 4
                ),
            ));
        }
    }

    let res : IResult<&str, u64> = alt((
        preceded(tag("#x"), map_res(take_while1(|x: char| x.is_digit(16)), u64_hex)),
        preceded(tag("#d"), map_res(take_while1(|x: char| x.is_digit(10)), u64_decimal)),
        preceded(tag("#b"), map_res(take_while1(|x: char| x.is_digit(2)), u64_binary)),
    ))(input);
    match res {
        Ok((s, a)) => {
            if s.len() == 0 { Ok(a) }
            else { Err(new_custom_error_span("Unrecongnized Constant.".into(), span)) }
        }
        Err(_) => Err(new_custom_error_span(
            format!(
                "Unrecognized or out-of-range constant: {} (engine currently supports up to 64-bit constants)",
                input
            ),
            span,
        ))
    }
}

pub fn value_constant<'i>(input: &str, bits: usize, span: Span<'i>) -> Result<Value, Error> {
    if input.starts_with("#x") || input.starts_with("#b") || input.starts_with("#d") {
        if bits <= 64 {
            return u64_constant(input, span).map(|v| Value::from_u64(v, bits));
        }
        if let Some(raw) = input.strip_prefix("#x") {
            return num_bigint::BigUint::parse_bytes(raw.as_bytes(), 16)
                .map(|v| Value::from_biguint(v, bits))
                .ok_or_else(|| new_custom_error_span("Unrecognized Constant.".into(), span));
        }
        if let Some(raw) = input.strip_prefix("#b") {
            return num_bigint::BigUint::parse_bytes(raw.as_bytes(), 2)
                .map(|v| Value::from_biguint(v, bits))
                .ok_or_else(|| new_custom_error_span("Unrecognized Constant.".into(), span));
        }
        if let Some(raw) = input.strip_prefix("#d") {
            return num_bigint::BigUint::parse_bytes(raw.as_bytes(), 10)
                .map(|v| Value::from_biguint(v, bits))
                .ok_or_else(|| new_custom_error_span("Unrecognized Constant.".into(), span));
        }
    }
    Err(new_custom_error_span("Unrecognized Constant.".into(), span))
}

#[cfg(test)]
mod tests {
    use super::u64_constant_python;

    #[test]
    fn test1() {
        assert_eq!(u64_constant_python("0x01"), Some(1));
        assert_eq!(u64_constant_python("1"), Some(1));
        assert_eq!(u64_constant_python("011000"), Some(11000));
        assert_eq!(u64_constant_python("000011000"), Some(11000));
        assert_eq!(u64_constant_python("0b00001"), Some(1));
    }
}
