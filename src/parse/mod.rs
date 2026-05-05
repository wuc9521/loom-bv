pub mod axiom;
pub mod cfg;
pub mod constraint;
pub mod deffun;
pub mod literals;
mod problem;
pub mod sexpr;
mod sorts;
mod view;

pub use sexpr::Error;
pub type Result<T> = std::result::Result<T, Error>;
pub use constraint::PbeConstraint;
pub use problem::SynthProblem;
pub use sexpr::new_custom_error_span;
pub use sorts::SortAliases;
pub use view::{DefineFunView, ProblemView, SynthFunView};
