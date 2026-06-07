use crate::{
    enumerate::grammar::{MultiConfig, MultiRule, TemplateExpr},
    parse::deffun,
};

use super::{Grammar, ExactRule};

impl Grammar<'static> {
    pub fn from_config(grammar: &MultiConfig<'static>) -> Self {
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
                    } => ExactRule::from_template(template, child_nts, *base_size),
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
    /// Try to fold a `MultiRule::Template`'s template into one of the dedicated
    /// `ExactRule` variants (Leaf / Op) that don't carry the full TemplateExpr.
    /// Falls back to `GenericTemplate` whenever the shape doesn't match
    /// `op(slot_0, slot_1, ...)` exactly.
    pub fn from_template(template: &TemplateExpr, child_nts: &[usize], base_size: usize) -> ExactRule {
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
    }
    }
}
