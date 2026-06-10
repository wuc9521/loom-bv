use std::{cmp::min, sync::Arc, thread, usize};

use rand::{seq::SliceRandom, thread_rng};
use rsmt2::SmtConf;
use serde::{Deserialize, Serialize};
use spin::Mutex;

use crate::{
    cegis::CegisState,
    enumerate::{
        expr::{Expr, OwnedExpr},
        grammar::{Config, Rule, TemplateExpr},
        value::BitVec,
    },
    exact::Constraint,
    info,
    parse::{self, SynthProblem},
    solutions::Solutions,
};

use super::sample::SampleConfig;

struct JoinOnDrop(Option<thread::JoinHandle<()>>);

impl JoinOnDrop {
    fn new(handle: thread::JoinHandle<()>) -> Self {
        Self(Some(handle))
    }
}

impl Drop for JoinOnDrop {
    fn drop(&mut self) {
        if let Some(handle) = self.0.take() {
            if handle.join().is_err() {
                info!("condition-search worker panicked");
            }
        }
    }
}

#[derive(Deserialize, Serialize, Debug, Clone)]
pub struct SearchConfig {
    pub ar_ratio: usize,
    pub ite_tree_limit: usize,
    pub limited_ite: bool,
    pub smt_solver: String,
    pub random_example: usize,
    pub additional_check: usize,
    pub chatgpt: bool,
    pub gpt_version: String,
    pub cond_search: SampleConfig,
    pub expr_search: SampleConfig,
    pub improve_search: SampleConfig,
    pub is_pbe: bool,
    pub seed: usize,
    #[serde(default = "default_true")]
    pub enable_sampling: bool,
    #[serde(default = "default_true")]
    pub min: bool,
    #[serde(default)]
    pub enable_composition: bool,
    #[serde(skip)]
    pub fixpoint: Option<&'static str>,
}

fn default_true() -> bool { true }

impl SearchConfig {
    pub fn default_pbe() -> Self {
        Self {
            random_example: 1,
            additional_check: 0,
            ar_ratio: 2,
            ite_tree_limit: 100000,
            smt_solver: "bitwuzla".into(),
            limited_ite: false,
            chatgpt: false,
            cond_search: SampleConfig::cond_default(),
            expr_search: SampleConfig::expr_default(),
            improve_search: SampleConfig::improve_default(),
            gpt_version: "gpt-4o".into(),
            is_pbe: false,
            seed: usize::MAX,
            enable_sampling: true, min: true,
            enable_composition: false,
            fixpoint: None,
        }
    }
    pub fn default_refimpl() -> Self {
        Self {
            random_example: 50,
            additional_check: 0,
            ar_ratio: 2,
            ite_tree_limit: 100000,
            smt_solver: "bitwuzla".into(),
            limited_ite: true,
            chatgpt: true,
            cond_search: SampleConfig::cond_default(),
            expr_search: SampleConfig::expr_default_ni(),
            improve_search: SampleConfig::improve_default(),
            gpt_version: "gpt-4o".into(),
            is_pbe: false,
            seed: usize::MAX,
            enable_sampling: true, min: true,
            enable_composition: false,
            fixpoint: None,
        }
    }
    pub fn default_refimpl_classic() -> Self {
        Self {
            random_example: 50,
            additional_check: 0,
            ar_ratio: 2,
            ite_tree_limit: 100000,
            smt_solver: "bitwuzla".into(),
            limited_ite: false,
            chatgpt: false,
            cond_search: SampleConfig::cond_default(),
            expr_search: SampleConfig::expr_default(),
            improve_search: SampleConfig::improve_default(),
            gpt_version: "gpt-4o".into(),
            is_pbe: false,
            seed: usize::MAX,
            enable_sampling: true, min: true,
            enable_composition: false,
            fixpoint: None,
        }
    }
    pub fn default_exact() -> Self {
        Self {
            random_example: 0,
            additional_check: 0,
            ar_ratio: 2,
            ite_tree_limit: 0,
            smt_solver: "bitwuzla".into(),
            limited_ite: false,
            chatgpt: false,
            cond_search: SampleConfig::cond_default(),
            expr_search: SampleConfig::expr_default(),
            improve_search: SampleConfig::improve_default(),
            gpt_version: "gpt-4o".into(),
            is_pbe: false,
            seed: usize::MAX,
            enable_sampling: false, min: true,
            enable_composition: false,
            fixpoint: None,
        }
    }
    pub fn rng(&self) -> rand::rngs::StdRng {
        if self.seed != usize::MAX {
            rand::SeedableRng::seed_from_u64(self.seed as u64)
        } else {
            rand::SeedableRng::from_rng(thread_rng()).unwrap()
        }
    }
    pub fn search(
        &mut self,
        problem: &SynthProblem<'static>,
        pbecstr: &Constraint,
        additional_example: Constraint,
    ) -> parse::Result<OwnedExpr> {
        if !self.enable_sampling {
            return crate::exact::search::search_problem(
                problem, pbecstr, self.min, self.fixpoint, self.enable_composition,
            );
        }
        let mut limited_ite = self.limited_ite;
        if self.ite_tree_limit == 1 || pbecstr.len() <= 1 {
            limited_ite = true;
        }
        let cond = Arc::new(Mutex::new(Vec::new()));
        if self.limited_ite {
            self.cond_search.filter.count_limit = 10000;
        }
        let mut rng = self.rng();
        let cond_worker = JoinOnDrop::new(thread::spawn({
            let problem = problem.clone();
            let pbecstr = pbecstr.clone();
            let cond_search = self.cond_search.clone();
            let cond = cond.clone();
            move || {
                let cond_cstr = &pbecstr.clone().set_output(BitVec::from_u64(0, 1));
                let mut conds = Solutions::new(cond_cstr, false, true);
                conds.cond_buffer = Some(cond);
                let problem = problem;

                if let Ok(mcfg) = Config::from_problem(&problem) {
                    let start_rules = &mcfg.nts[mcfg.start].1;
                    let mut has_and = false;
                    let mut has_lshr = false;
                    let mut consts: Vec<BitVec> = Vec::new();
                    for rule in start_rules {
                        match rule {
                            Rule::Template { template, .. } => match template {
                                TemplateExpr::App(id, _) => match id.get_name() {
                                    "bvand" => has_and = true,
                                    "bvlshr" => has_lshr = true,
                                    _ => {}
                                },
                                TemplateExpr::Leaf(OwnedExpr::Const(v)) => consts.push(v.clone()),
                                _ => {}
                            },
                            _ => {}
                        }
                    }
                    if has_and && has_lshr {
                        info!("Searching Conditions.");
                        let arg_widths = problem.arg_widths();
                        for shift in &consts {
                            let shift = shift.as_u64_lossy() as usize;
                            use Expr::*;
                            for i in 0..problem.args.len() {
                                let w = arg_widths[i];
                                conds.add_solution(
                                    &And(
                                        &LShr(
                                            &Var(i, w),
                                            &Const(BitVec::from_u64(shift as u64, w)),
                                        ),
                                        &Const(BitVec::from_u64(1, w)),
                                    ),
                                    0,
                                );
                            }
                        }
                    }
                }
                cond_search.search(&mut conds, &problem, &mut rng).unwrap();

                info!("{} Condition Searched.", conds.solved.len())
            }
        }));

        let mut rng = self.rng();

        info!("Searching Expressions.");
        let mut exprs = Solutions::new(pbecstr, true, false);
        exprs.additional_check = additional_example;

        if self.limited_ite {
            self.expr_search.cover_limit = pbecstr.len();
            self.expr_search.partial_solution = false;
            exprs.sample_all = true;
            if exprs.pbecstr.len() > 5 && !self.is_pbe {
                exprs.wait_cond = 300;
            }
            exprs.check_tree_learning = Some((cond.clone(), min(self.ite_tree_limit, 7)));
        }

        while exprs.remaining() > 0 {
            if !self.expr_search.search(&mut exprs, problem, &mut rng)? {
                self.expr_search.filter.count_limit_solved *= self.ar_ratio;
            }
        }
        if exprs.solved.last().unwrap().1.len() == pbecstr.len() {
            return Ok(exprs.solved.pop().unwrap().0);
        }
        exprs.sample_all = true;
        exprs.check_tree_learning = Some((cond, self.ite_tree_limit));
        info!("Tree Learning");
        if exprs.tree_learning() {
            return Ok(exprs.get_tree());
        }
        if limited_ite {
            if let Some(best) = exprs.best_solution() {
                return Ok(best);
            }
            return Err(parse::new_custom_error_span(
                "Search: no candidate survived expression search.".into(),
                (),
            ));
        }

        if !limited_ite {
            info!("Improving Expressions.");
            self.improve_search.cover_limit = pbecstr.len() / ((self.ite_tree_limit + 1) / 2 - 1);
            self.improve_search.filter.count_limit_solved +=
                self.expr_search.filter.count_limit_solved;
            while !self.improve_search.search(&mut exprs, problem, &mut rng)? {
                self.improve_search.filter.count_limit_solved *= self.ar_ratio;
            }
        }
        if let Some(best) = exprs.best_solution() {
            drop(cond_worker);
            Ok(best)
        } else {
            let tree = exprs.get_tree();
            drop(cond_worker);
            Ok(tree)
        }
    }

    // #[inline(always)]
    // pub fn tree_learing(exprs: &Solutions, conds: &Solutions, pbe: &PbeConstraint, size_limit: usize) -> Option<OwnedExpr> {
    //     let bump = Bump::new();
    //     let tl = tree_learning::tree_learning(exprs.to_bits(), conds.to_bits(), pbe.len(), &bump, size_limit);
    //     if tl.result_size() < size_limit { Some(tl.bvexpr()) } else { None }
    // }

    pub fn cegis_loop(
        &mut self,
        problem: &SynthProblem<'static>,
        ref_impl: &OwnedExpr,
    ) -> parse::Result<OwnedExpr> {
        info!("Starting CEGIS Loop.");
        let mut cegis = CegisState::new(
            problem.arg_widths(),
            problem.bits,
            ref_impl.clone(),
            self.get_smt_conf(),
        );
        let no_additional_check = Constraint::empty(problem.args.len(), problem.bits);
        let mut additional_check = Constraint::empty(problem.args.len(), problem.bits);
        {
            let mut rng = self.rng();
            for _ in 0..self.additional_check {
                let mask = [
                    u64::MAX,
                    u64::MAX,
                    u64::MAX,
                    u64::MAX,
                    0xFF,
                    0xFFFFFFFFFFFF,
                    0xFFFFFF0000FFFFFF,
                ]
                .choose(&mut rng)
                .unwrap();
                additional_check.random_example(
                    &mut rng,
                    *mask,
                    ref_impl,
                    problem.args.len(),
                )
            }
            for _ in 0..std::cmp::max(self.random_example, 1) {
                let mask = [
                    u64::MAX,
                    u64::MAX,
                    u64::MAX,
                    u64::MAX,
                    0xFF,
                    0xFFFFFFFFFFFF,
                    0xFFFFFF0000FFFFFF,
                ]
                .choose(&mut rng)
                .unwrap();
                cegis.examples.random_example(
                    &mut rng,
                    *mask,
                    ref_impl,
                    problem.args.len(),
                );
            }
        }

        let mut result = self.search(&problem, &cegis.examples, no_additional_check.clone())?;
        while !cegis.verify(&result).map_err(|e| {
            parse::new_custom_error_span(e, ())
        })? {
            result = self.search(
                &problem,
                &cegis.examples,
                if cegis.examples.len() > 8 {
                    additional_check.clone()
                } else {
                    no_additional_check.clone()
                },
            )?;
        }
        Ok(result)
    }
    #[cfg(feature = "chatgpt")]
    pub fn cegis_check<'a>(
        &mut self,
        problem: &SynthProblem<'a>,
        ref_impl: &OwnedExpr,
        expr: &OwnedExpr,
    ) -> bool {
        let mut cegis = CegisState::new(
            problem.arg_widths(),
            problem.bits,
            ref_impl.clone(),
            self.get_smt_conf(),
        );
        cegis.verify(expr).unwrap_or(false)
    }
    pub fn get_smt_conf<'a>(&self) -> SmtConf {
        match &*self.smt_solver {
            "z3" => SmtConf::default_z3(),
            "bitwuzla" => {
                let mut conf = SmtConf::yices_2("bitwuzla");
                conf.option("--lang");
                conf.option("smt2");
                conf.option("-m");
                conf
            }
            s => panic!("Unrecongized Solver: {}", s),
        }
    }
}
unsafe impl Send for SearchConfig {}
