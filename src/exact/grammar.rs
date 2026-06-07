use crate::{
    enumerate::grammar::{Config, Rule, RuleClass, TemplateExpr},
    parse::deffun,
};

use super::{Grammar, ExactRule};

impl Grammar<'static> {
    pub fn from_config(grammar: &Config<'static>) -> Self {
    let nts = grammar
        .nts
        .iter()
        .map(|(name, rules)| {
            let compiled = rules
                .iter()
                .map(|rule| match rule {
                    Rule::Alias(nt) => ExactRule::Alias(*nt),
                    Rule::Template {
                        template,
                        child_nts,
                        base_size,
                        class,
                    } => ExactRule::from_template(template, child_nts, *base_size, *class),
                    Rule::ChatGPT { expr, .. } => ExactRule::Leaf(expr.clone()),
                })
                .collect();
            (*name, compiled)
        })
        .collect();
    Self {
            nts,
            start: grammar.start,
        }
    }
}

impl ExactRule {
    pub fn from_template(template: &TemplateExpr, child_nts: &[usize], base_size: usize, class: RuleClass) -> ExactRule {
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
    ExactRule::Op {
        fid,
        child_nts: child_nts.to_vec(),
        class,
    }
    }
}
