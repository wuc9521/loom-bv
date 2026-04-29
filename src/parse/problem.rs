use derive_more::DebugCustom;
use pest::Span;
use sygus_parser::ast::{Identifier, Index, Sort, SortedVar, SyGuSCmd, SyGuSFile};

use crate::enumerate::expr::OwnedExpr;

use super::{cfg::Cfg, new_custom_error_span, Error};

#[derive(Clone, DebugCustom)]
#[debug(fmt = "synth-fun {} {:?}", name, args)]
pub struct SynthProblem<'i> {
    pub name: &'i str,
    pub args: Vec<&'i str>,
    pub arg_decls: Vec<SortedVar>,
    pub cfg: Cfg<'i>,
    pub span: Span<'i>,
    pub description: String,
    pub chatgpt_exprs: Vec<OwnedExpr>,
    pub bits: usize,
    pub ret_sort: Sort,
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
        fn parse_width_from_identifier(id: &Identifier) -> Option<usize> {
            match id {
                Identifier::Symbol(sym) => sym.parse::<usize>().ok(),
                Identifier::Indexed(sym, idxs) => {
                    if sym == "_" && idxs.len() >= 2 {
                        if let (Index::Symbol(head), Index::Numeral(width)) = (&idxs[0], &idxs[1]) {
                            if head == "BitVec" {
                                return Some(*width);
                            }
                        }
                    }
                    if sym == "BitVec" {
                        if let Some(Index::Numeral(width)) = idxs.first() {
                            return Some(*width);
                        }
                    }
                    idxs.iter().find_map(|i| match i {
                        Index::Numeral(v) => Some(*v),
                        Index::Symbol(_) => None,
                    })
                }
            }
        }

        fn parse_bv_width(sort: &Sort) -> Option<usize> {
            match sort {
                Sort::Simple(id) => parse_width_from_identifier(id),
                Sort::Parameterized(id, ss) => {
                    parse_width_from_identifier(id).or_else(|| ss.iter().find_map(parse_bv_width))
                }
            }
        }

        for cmd in &file.cmds {
            if let SyGuSCmd::SynthFun(name, args, ret, cfg) = cmd {
                let bits = parse_bv_width(ret).ok_or_else(|| {
                    let span = Span::new("", 0, 0).unwrap();
                    new_custom_error_span(
                        format!("Unknown return value: display={}, debug={:?}", ret, ret),
                        span,
                    )
                })?;

                let arg_decls = args.clone();
                let args: Vec<&'static str> = args
                    .iter()
                    .map(|x| Box::leak(x.name.clone().into_boxed_str()) as &'static str)
                    .collect();

                let cfg = cfg.as_ref().ok_or_else(|| {
                    let span = Span::new("", 0, 0).unwrap();
                    new_custom_error_span("SynthProblem: Expecting grammar list".into(), span)
                })?;
                return Ok(SynthProblem {
                    name: Box::leak(name.clone().into_boxed_str()),
                    args,
                    arg_decls,
                    cfg: Cfg::from_grammar(cfg)?,
                    span: Span::new("", 0, 0).unwrap(),
                    description: "".into(),
                    chatgpt_exprs: Vec::new(),
                    bits,
                    ret_sort: ret.clone(),
                });
            }
        }
        Err(new_custom_error_span(
            "SynthProblem: Expecting a `synth-fun`.".into(),
            Span::new("", 0, 0).unwrap(),
        ))
    }

    pub fn arg(&self, name: &str) -> Option<usize> {
        self.args
            .iter()
            .enumerate()
            .find(|x| *x.1 == name)
            .map(|x| x.0)
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

#[cfg(test)]
mod tests {
    use crate::parse::SynthProblem;
    use sygus_parser::ast::SyGuSFile;

    #[test]
    fn test_problem_parse() {
        let e = SyGuSFile::from_str(
            "(synth-fun f ((x bool) (y bool)) ()
        (
            (Start bool ((bvand a b) (bvand a c) ) )
        ))",
        )
        .unwrap();
        let cfg = SynthProblem::parse_from_file(&e).unwrap();
        println!("{:?}", cfg);
    }
}
