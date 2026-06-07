
pub mod cfg;
pub mod constraint;
pub mod deffun;
mod problem;
pub mod sexpr;
mod sorts;
mod view;

pub use sexpr::Error;
pub type Result<T> = std::result::Result<T, Error>;
pub use constraint::{empty_span, extract_indices_from_identifier, literal_to_value};
pub use problem::SynthProblem;
pub use sexpr::new_custom_error_span;
pub use sorts::SortAliases;
pub use view::{DefineFunView, ProblemView, SynthFunView};
