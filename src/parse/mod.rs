pub mod cfg;
pub mod constraint;
pub mod deffun;
pub mod literals;
mod problem;
mod sorts;
pub mod sexpr;

pub use sexpr::Error;
pub type Result<T> = std::result::Result<T, Error>;
pub use constraint::PbeConstraint;
pub use problem::SynthProblem;
pub use sorts::SortAliases;
pub use sexpr::new_custom_error_span;
