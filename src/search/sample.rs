use std::cmp::min;

use rand::rngs::StdRng;
use rand::seq::IteratorRandom;
use serde::{Deserialize, Serialize};

use crate::{
    enumerate::grammar::Config,
    exact::{Constraint, search::enumerate_start, types::Grammar},
    parse::{self, SynthProblem},
    solutions::Solutions,
};

#[derive(Deserialize, Serialize, Debug, Clone)]
pub struct SampleConfig {
    pub sample: usize,
    pub cover_limit: usize,
    pub partial_solution: bool,
    pub dag_size: bool,
    pub count_limit: usize,
}

impl SampleConfig {
    pub const fn cond_default() -> Self {
        Self {
            sample: 16,
            cover_limit: 8,
            partial_solution: true,
            dag_size: true,
            count_limit: 10000,
        }
    }
    pub const fn expr_default() -> Self {
        Self {
            sample: 8,
            cover_limit: 13,
            partial_solution: true,
            dag_size: true,
            count_limit: 10000,
        }
    }
    pub const fn expr_default_ni() -> Self {
        Self {
            sample: 64,
            cover_limit: 13,
            partial_solution: true,
            dag_size: true,
            count_limit: 10000,
        }
    }
    pub const fn improve_default() -> Self {
        Self {
            sample: 8,
            cover_limit: 13,
            partial_solution: true,
            dag_size: true,
            count_limit: 10000,
        }
    }

    fn search_inner(
        &self,
        sol: &mut Solutions,
        problem: &SynthProblem<'static>,
        rng: &mut StdRng,
    ) -> parse::Result<bool> {
        let n = min(self.sample, sol.pbecstr.len());
        let indices: Vec<usize> = sol.unsolved.iter().cloned().choose_multiple(rng, n);

        let mut examples = Vec::with_capacity(indices.len());
        for &i in &indices {
            examples.push(sol.pbecstr.examples[i].clone());
        }
        let spec = Constraint {
            bits: sol.pbecstr.bits,
            args: sol.pbecstr.args,
            examples,
            structural: Vec::new(),
            closure: None,
        };

        let multi = Config::from_problem(problem)?;
        let grammar = Grammar::from_config(&multi);

        let mut solved = false;
        let max_candidates = self.count_limit;

        enumerate_start(grammar, &spec, false, 7, max_candidates, |expr| {
            sol.add_solution_owned(expr, 0);
            if sol.unsolved.is_empty() {
                solved = true;
                return Err(());
            }
            Ok(())
        })?;

        Ok(!solved)
    }

    pub fn search(
        &self,
        sol: &mut Solutions,
        problem: &SynthProblem<'static>,
        rng: &mut StdRng,
    ) -> parse::Result<bool> {
        sol.set_cover_limit(if self.cover_limit == 0 {
            1
        } else {
            sol.pbecstr.len() / self.cover_limit
        });
        self.search_inner(sol, problem, rng)
    }
}
