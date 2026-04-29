use sygus_parser::Rule as SyGuSRule;

pub use pest::Span;

pub type Error = pest::error::Error<SyGuSRule>;

pub fn new_custom_error_span<'i>(msg: String, span: Span<'i>) -> Error {
    Error::new_from_span(
        pest::error::ErrorVariant::CustomError { message: msg },
        span,
    )
}
