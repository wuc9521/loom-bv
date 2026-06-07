use derive_more::DebugCustom;
use sygus_parser::ast::{Identifier, Index, Sort, SortedVar, SyGuSFile};

use crate::enumerate::expr::OwnedExpr;

use super::{axiom::AxiomRewriter, cfg::Cfg, new_custom_error_span, Error, ProblemView};

#[derive(Clone, DebugCustom)]
#[debug(fmt = "synth-fun {} {:?}", name, args)]
pub struct SynthProblem<'i> {
    pub name: &'i str,
    pub args: Vec<&'i str>,
    pub arg_decls: Vec<SortedVar>,
    pub cfg: Cfg<'i>,
    pub description: String,
    pub chatgpt_exprs: Vec<OwnedExpr>,
    pub bits: usize,
    pub ret_sort: Sort,
    pub axioms: Option<AxiomRewriter>,
}

impl<'i> SynthProblem<'i> {
    fn format_sort(sort: &Sort) -> String {
        fn format_identifier(id: &Identifier) -> String {
            match id {
                Identifier::Symbol(sym) => sym.clone(),
                Identifier::Indexed(sym, idxs) if sym == "BitVec" && idxs.len() == 1 => {
                    match &idxs[0] {
                        Index::Numeral(width) => format!("(_ BitVec {width})"),
                        Index::Symbol(name) => format!("(_ BitVec {name})"),
                    }
                }
                _ => format!("{id}"),
            }
        }
        match sort {
            Sort::Simple(id) => format_identifier(id),
            Sort::Parameterized(id, sorts) => {
                if let Identifier::Symbol(sym) = id {
                    if sym == "BitVec" && sorts.len() == 1 {
                        return format!("(_ BitVec {})", Self::format_sort(&sorts[0]));
                    }
                }
                let args = sorts
                    .iter()
                    .map(Self::format_sort)
                    .collect::<Vec<_>>()
                    .join(" ");
                format!("({} {args})", format_identifier(id))
            }
        }
    }

    pub fn parse_from_file(file: &SyGuSFile) -> Result<SynthProblem<'static>, Error> {
        let view = ProblemView::from_file(file);
        Self::parse_from_view(&view)
    }

    pub fn parse_from_view(view: &ProblemView<'_>) -> Result<SynthProblem<'static>, Error> {
        let synth = view.synth_fun().ok_or_else(|| {
            new_custom_error_span(
                "SynthProblem: Expecting a `synth-fun`.".into(),
                (),
            )
        })?;

        let bits = view
            .sort_aliases
            .parse_sort_width(synth.ret)
            .ok_or_else(|| {
                new_custom_error_span(
                    format!(
                        "Unknown return value: display={}, debug={:?}",
                        synth.ret, synth.ret
                    ),
                    (),
                )
            })?;

        let arg_decls = synth.args.to_vec();
        let args: Vec<&'static str> = synth
            .args
            .iter()
            .map(|x| Box::leak(x.name.clone().into_boxed_str()) as &'static str)
            .collect();

        let cfg = synth.grammar.ok_or_else(|| {
            new_custom_error_span("SynthProblem: Expecting grammar list".into(), ())
        })?;
        let axioms = AxiomRewriter::from_axioms(
            &view.axioms.iter().map(|a| (*a).clone()).collect::<Vec<_>>(),
        );
        Ok(SynthProblem {
            name: Box::leak(synth.name.to_string().into_boxed_str()),
            args,
            arg_decls,
            cfg: Cfg::from_grammar(cfg, axioms.as_ref())?,
            description: "".into(),
            chatgpt_exprs: Vec::new(),
            bits,
            ret_sort: synth.ret.clone(),
            axioms,
        })
    }

    pub fn arg(&self, name: &str) -> Option<usize> {
        self.args
            .iter()
            .enumerate()
            .find(|x| *x.1 == name)
            .map(|x| x.0)
    }

    pub fn arg_widths(&self) -> Vec<usize> {
        let aliases = super::sorts::SortAliases::default();
        self.arg_decls
            .iter()
            .map(|sv| aliases.parse_sort_width(&sv.sort).unwrap_or(1))
            .collect()
    }

    pub fn format_solution(&self, expr: &OwnedExpr) -> String {
        let args = self
            .arg_decls
            .iter()
            .map(|arg| format!("({} {})", arg.name, Self::format_sort(&arg.sort)))
            .collect::<Vec<_>>()
            .join(" ");
        format!(
            "(define-fun {} ({}) {} {})",
            self.name,
            args,
            Self::format_sort(&self.ret_sort),
            expr.to_sygus(&self.args)
        )
    }
}

