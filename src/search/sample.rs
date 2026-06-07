use std::cmp::min;

use bumpalo::Bump;
use rand::rngs::StdRng;
use serde::{Deserialize, Serialize};

use crate::{
    enumerate::{algo, Algo as AAlgo},
    info,
    parse::{self, SynthProblem},
    solutions::Solutions,
};

use super::filter::FilterConfig;

#[derive(Deserialize, Serialize, Debug, Clone)]
pub struct SampleConfig {
    pub sample: usize,
    pub cover_limit: usize,
    pub partial_solution: bool,
    pub dag_size: bool,
    pub filter: FilterConfig,
}

impl SampleConfig {
    pub const fn cond_default() -> Self {
        Self {
            sample: 16,
            cover_limit: 8,
            partial_solution: true,
            filter: FilterConfig::cond_default(),
            dag_size: true,
        }
    }
    pub const fn expr_default() -> Self {
        Self {
            sample: 8,
            cover_limit: 13,
            partial_solution: true,
            filter: FilterConfig::expr_default(),
            dag_size: true,
        }
    }
    pub const fn expr_default_ni() -> Self {
        Self {
            sample: 64,
            cover_limit: 13,
            partial_solution: true,
            filter: FilterConfig::expr_default(),
            dag_size: true,
        }
    }
    pub const fn improve_default() -> Self {
        Self {
            sample: 8,
            cover_limit: 13,
            partial_solution: true,
            filter: FilterConfig::improve_default(),
            dag_size: true,
        }
    }

    pub fn search_inner<const N: usize>(
        &self,
        sol: &mut Solutions,
        problem: &SynthProblem<'static>,
        rng: &mut StdRng,
    ) -> parse::Result<bool> {
        let (args, out) = sol.sample::<N, _>(rng);
        info!(
            "Sampling with: {:x?} -> {:x?}. {}",
            args,
            out,
            sol.pbecstr.len()
        );
        let bump = Bump::new();
        let mut filter = self
            .filter
            .state(args.clone(), &out, &bump, self.partial_solution);
        let mut algo =
            algo::Algo::new(problem, args, out.clone(), self.dag_size, &bump)?;
        let _ = algo.run_until(|algo, e, v| filter.filter(algo, e, v, sol));
        let result = !filter.solved;
        info!(
            "Searched for {} {} {} Expressions.",
            algo.len(),
            algo.count(),
            algo.count2()
        );
        Ok(result)
    }

    pub fn search_inner_exact(
        &self,
        sol: &mut Solutions,
        problem: &SynthProblem<'static>,
        rng: &mut StdRng,
    ) -> parse::Result<bool> {
        use crate::enumerate::grammar::Config;
        use crate::exact::{Constraint, search::enumerate_start, types::Grammar};
        use rand::seq::IteratorRandom;

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
        let max_size = 7;

        let mut solved = false;
        let count_limit = self.filter.count_limit;
        let mut count = 0usize;

        enumerate_start(grammar, &spec, false, max_size, |expr| {
            count += 1;
            sol.add_solution_owned(expr, count);
            if sol.unsolved.is_empty() || count >= count_limit {
                solved = sol.unsolved.is_empty();
                return Err(());
            }
            Ok(())
        })?;

        Ok(!solved)
    }
    #[inline(always)]
    pub fn search(
        &self,
        sol: &mut Solutions,
        problem: &SynthProblem<'static>,
        rng: &mut StdRng,
    ) -> parse::Result<bool> {
        if std::env::var("DRYADSYNTH_EXACT_ENUM").is_ok() {
            return self.search_inner_exact(sol, problem, rng);
        }
        sol.set_cover_limit(if self.cover_limit == 0 {
            1
        } else {
            sol.pbecstr.len() / self.cover_limit
        });
        let arr = [1, 2, 4, 8, 16, 32, 48, 64, 80, 1024];
        let sample = arr[arr
            .binary_search(&min(self.sample, sol.pbecstr.len()))
            .unwrap_or_else(|a| a)];
        match sample {
            1 => self.search_inner::<1>(sol, problem, rng),
            2 => self.search_inner::<2>(sol, problem, rng),
            4 => self.search_inner::<4>(sol, problem, rng),
            8 => self.search_inner::<8>(sol, problem, rng),
            16 => self.search_inner::<16>(sol, problem, rng),
            32 => self.search_inner::<32>(sol, problem, rng),
            48 => self.search_inner::<48>(sol, problem, rng),
            64 => self.search_inner::<64>(sol, problem, rng),
            80 => self.search_inner::<80>(sol, problem, rng),
            1024 => self.search_inner::<1024>(sol, problem, rng),
            _ => panic!(
                "Unexpected sample count: {}. Expected numbers are 1, 2, 4, 8, 16, 32, 64.",
                sample
            ),
        }
    }
}
