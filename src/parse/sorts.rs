use std::collections::HashMap;

use sygus_parser::ast::{Identifier, Index, Sort, SyGuSCmd, SyGuSFile};

#[derive(Debug, Default, Clone)]
pub struct SortAliases {
    widths: HashMap<String, usize>,
}

impl SortAliases {
    pub fn from_file(file: &SyGuSFile) -> Self {
        let mut aliases = Self::default();
        for cmd in &file.cmds {
            if let SyGuSCmd::DefineSort(name, params, sort) = cmd {
                if !params.is_empty() {
                    continue;
                }
                if let Some(width) = aliases.parse_sort_width(sort) {
                    aliases.widths.insert(name.clone(), width);
                }
            }
        }
        aliases
    }

    fn parse_width_from_identifier(&self, id: &Identifier) -> Option<usize> {
        match id {
            Identifier::Symbol(sym) => self
                .widths
                .get(sym)
                .copied()
                .or_else(|| sym.parse::<usize>().ok()),
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
                    Index::Symbol(name) => self.widths.get(name).copied(),
                })
            }
        }
    }

    pub fn parse_sort_width(&self, sort: &Sort) -> Option<usize> {
        match sort {
            Sort::Simple(id) => {
                let name = id.get_name();
                if name.eq_ignore_ascii_case("bool") {
                    Some(1)
                } else {
                    self.parse_width_from_identifier(id)
                }
            }
            Sort::Parameterized(id, ss) => self
                .parse_width_from_identifier(id)
                .or_else(|| ss.iter().find_map(|s| self.parse_sort_width(s))),
        }
    }
}
