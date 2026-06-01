//! LFP synthesis frontend. See `spec::LfpSpec` for the two SyGuS-IF patterns
//! recognized (lfp-recursive: one self-referencing synth-fun; lfp-separate:
//! two synth-funs joined by `(= op aux)`). After detection the work goes
//! through the standard `NullarySpec::search` engine with
//! `fixpoint = Some(closure_name)` — there is no longer a parallel
//! enumeration / eval path. This module just builds the equivalent
//! `SynthProblem` and `NullarySpec::BitConstraints`, then formats the
//! returned operator term back into one or two `define-fun`s.

use std::collections::BTreeMap;

use crate::exact::NullarySpec;
use crate::info;
use crate::parse::cfg::Cfg;
use crate::parse::{self, deffun, new_custom_error_span, SynthProblem};

mod eval;
mod spec;

pub use spec::LfpSpec;

use crate::exact::util::empty_span;

impl<'a> LfpSpec<'a> {
    /// Drive the LFP search: wrap the operator's grammar as a single-arg
    /// SynthProblem (closure synth-fun = the arg), build the bit-constraint
    /// spec from the labels, and hand off to the unified
    /// `NullarySpec::search` with `fixpoint = Some(closure_name)`. Result is
    /// formatted as one or two `define-fun`s.
    pub fn search(&self, env: &deffun::Environ) -> parse::Result<Option<String>> {
        let op = self.operator();
        let grammar_def = op.grammar.ok_or_else(|| {
            new_custom_error_span(format!("{}: operator has no grammar", self.variant_tag()), empty_span())
        })?;
        let cfg = Cfg::from_grammar(grammar_def, None)?;
        let closure_name: &'static str = Box::leak(self.closure_name().to_string().into_boxed_str());
        let problem = SynthProblem {
            name: Box::leak(op.name.to_string().into_boxed_str()),
            args: vec![closure_name],
            arg_decls: vec![sygus_parser::ast::SortedVar {
                name: closure_name.to_string(),
                sort: op.ret.clone(),
            }],
            cfg,
            span: empty_span(),
            description: String::new(),
            chatgpt_exprs: Vec::new(),
            bits: self.bits(),
            ret_sort: op.ret.clone(),
            axioms: None,
        };
        let labels: BTreeMap<usize, bool> = self.labels().iter().copied().collect();
        let spec = NullarySpec::BitConstraints {
            bits: self.bits(),
            known_bits: labels,
            structural: Vec::new(),
        };
        info!(
            "{}: routing to exact-nullary with fixpoint='{}' (bits={}, labels={})",
            self.variant_tag(),
            closure_name,
            self.bits(),
            self.labels().len()
        );
        crate::exact::enable_eval_cache();
        let expr = spec.search(&problem, true, Some(closure_name))?;
        crate::exact::dump_and_disable_eval_cache(self.variant_tag());
        Ok(Some(self.finalize(env, expr)?))
    }
}
