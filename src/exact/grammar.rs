use crate::{
    enumerate::grammar::{MultiConfig, MultiRule, TemplateExpr},
    parse::deffun,
};

use super::{ExactGrammar, ExactRule};

pub fn compile_exact_grammar(grammar: &MultiConfig<'static>) -> ExactGrammar<'static> {
    let nts = grammar
        .nts
        .iter()
        .map(|(name, rules)| {
            let compiled = rules
                .iter()
                .map(|rule| match rule {
                    MultiRule::Alias(nt) => ExactRule::Alias(*nt),
                    MultiRule::Template {
                        template,
                        child_nts,
                        base_size,
                        ..
                    } => compile_exact_rule(template, child_nts, *base_size),
                })
                .collect();
            (*name, compiled)
        })
        .collect();
    ExactGrammar {
        nts,
        start: grammar.start,
    }
}

fn compile_exact_rule(template: &TemplateExpr, child_nts: &[usize], base_size: usize) -> ExactRule {
    if child_nts.is_empty() {
        if let TemplateExpr::Leaf(expr) = template {
            return ExactRule::Leaf(expr.clone());
        }
    }
    let TemplateExpr::App(id, parts) = template else {
        return ExactRule::GenericTemplate {
            template: template.clone(),
            child_nts: child_nts.to_vec(),
            base_size,
        };
    };
    if parts.len() != child_nts.len() {
        return ExactRule::GenericTemplate {
            template: template.clone(),
            child_nts: child_nts.to_vec(),
            base_size,
        };
    }
    if !parts
        .iter()
        .enumerate()
        .all(|(idx, part)| matches!(part, TemplateExpr::Slot(slot) if *slot == idx))
    {
        return ExactRule::GenericTemplate {
            template: template.clone(),
            child_nts: child_nts.to_vec(),
            base_size,
        };
    }
    let Some(fid) = deffun::ENV.lookup(id.get_name(), parts.len()) else {
        return ExactRule::GenericTemplate {
            template: template.clone(),
            child_nts: child_nts.to_vec(),
            base_size,
        };
    };
    match parts.len() {
        1 => ExactRule::Unary {
            fid,
            child_nt: child_nts[0],
        },
        2 => ExactRule::Binary {
            fid,
            lhs_nt: child_nts[0],
            rhs_nt: child_nts[1],
        },
        _ => ExactRule::Nary {
            fid,
            child_nts: child_nts.to_vec(),
        },
    }
}
