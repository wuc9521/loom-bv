use std::cell::UnsafeCell;
use std::hash::{Hash, Hasher};

use derive_more::DebugCustom;
use rustc_hash::FxHasher;
use sygus_parser::ast::{SyGuSFile, SyGuSTerm};

use crate::{
    enumerate::{
        expr::{DivideByZero, OwnedExpr},
        op,
        value::Value,
    },
    debg,
};

use super::{new_custom_error_span, Error, ProblemView};

fn collect_term_symbols(term: &SyGuSTerm, out: &mut Vec<String>) {
    match term {
        SyGuSTerm::Identifier(id) => out.push(id.get_name().to_string()),
        SyGuSTerm::Application(id, args) => {
            out.push(id.get_name().to_string());
            for arg in args {
                collect_term_symbols(arg, out);
            }
        }
        SyGuSTerm::Annotated(inner, _) => collect_term_symbols(inner, out),
        SyGuSTerm::Let(bindings, body) => {
            for binding in bindings {
                collect_term_symbols(&binding.term, out);
            }
            collect_term_symbols(body, out);
        }
        SyGuSTerm::Forall(_, body) | SyGuSTerm::Exists(_, body) => collect_term_symbols(body, out),
        SyGuSTerm::Literal(_) => {}
    }
}


#[derive(Clone, DebugCustom)]
#[debug(fmt = "define-fun {} {:?}", name, args)]
pub struct DefineFun {
    pub name: &'static str,
    pub args: Vec<&'static str>,
    pub arg_bits: Vec<usize>,
    pub ret_bits: usize,
    pub expr: OwnedExpr,
    plan: DefineFunPlan,
    /// Names of synth-funs (in SyGuS file order) that the body may reference.
    /// SyGuS 2.1 §3.7 allows define-fun bodies to reference any signature
    /// symbol except themselves; these synth-funs are appended to the Var
    /// index space after `args`. Callers of `eval_defined` must pass
    /// `args.len() + closure_args.len()` values: real args first, then the
    /// current value of each closure synth-fun in this list's order.
    pub closure_args: Vec<&'static str>,
    pub closure_arg_bits: Vec<usize>,
}

impl DefineFun {
    /// Evaluate this define-fun's plan on `args`, optionally with a
    /// closure binding for the synth-fun named `closure_name`. The
    /// define-fun's `closure_args` slots are filled with `closure_value`
    /// for the matching name and zero elsewhere. Plan eval needs `&env`
    /// because plan instructions can call other define-funs recursively.
    pub fn eval(
        &self,
        env: &Environ,
        args: &[Value],
        closure: Option<(&str, &Value)>,
    ) -> Result<Value, DivideByZero> {
        match closure {
            Some((closure_name, closure_value)) if !self.closure_args.is_empty() => {
                // Matches the layout established at parse time: real args
                // followed by one value per closure_args slot (see
                // `extended_env` in `parse_from_view`).
                let mut extended = Vec::with_capacity(args.len() + self.closure_args.len());
                extended.extend_from_slice(args);
                for (name, bits) in
                    self.closure_args.iter().zip(self.closure_arg_bits.iter())
                {
                    if *name == closure_name {
                        extended.push(closure_value.clone());
                    } else {
                        extended.push(Value::from_u64(0, *bits));
                    }
                }
                self.plan.eval(env, &extended)
            }
            _ => self.plan.eval(env, args),
        }
    }

    /// Hash for a `(self, args, closure)` call — used by the exact-nullary
    /// search's eval cache. Mirrors the arg layout `eval` would build, so
    /// two calls with the same observable inputs hash to the same key.
    ///
    /// Identity uses `self as *const _`: within one Environ the
    /// `DefineFun` slots never move, so the pointer is a stable per-fun
    /// id for the lifetime of a search.
    pub fn hash_call(&self, args: &[Value], closure: Option<(&str, &Value)>) -> u64 {
        let mut h = FxHasher::default();
        h.write_usize(self as *const _ as usize);
        h.write_usize(args.len());
        for v in args {
            v.hash(&mut h);
        }
        if let Some((closure_name, closure_value)) = closure {
            for (name, bits) in self.closure_args.iter().zip(self.closure_arg_bits.iter()) {
                if *name == closure_name {
                    closure_value.hash(&mut h);
                } else {
                    Value::from_u64(0, *bits).hash(&mut h);
                }
            }
        }
        h.finish()
    }

    pub fn bit_circuit_plan(&self) -> Option<&BitCircuitPlan> {
        match &self.plan {
            DefineFunPlan::BitCircuit(plan) if self.closure_args.is_empty() => Some(plan),
            _ => None,
        }
    }
}

#[derive(Clone, Debug)]
pub enum DefineFunPlan {
    Generic {
        root: usize,
        slot_count: usize,
        slot_bits: Vec<usize>,
        instrs: Vec<PlanInstr>,
    },
    BitCircuit(BitCircuitPlan),
}

#[derive(Clone, Debug)]
pub struct BitCircuitPlan {
    pub bindings: Vec<BoolNode>,
    pub output_bits: Vec<BoolAtom>,
    pub ret_bits: usize,
    pub input_slots: Vec<(usize, usize)>,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum BoolNode {
    Atom(BoolAtom),
    Not(BoolAtom),
    And(BoolAtom, BoolAtom),
    Or(BoolAtom, BoolAtom),
    Xor(BoolAtom, BoolAtom),
    Ite(BoolAtom, BoolAtom, BoolAtom),
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum BoolAtom {
    Const(bool),
    InputBit { arg: usize, bit: usize },
    Temp(usize),
}

#[derive(Clone, Debug)]
pub enum PlanInstr {
    Const(Value),
    Concat { lhs: usize, rhs: usize },
    Extract { src: usize, hi: u64, lo: u64 },
    Not { src: usize },
    Neg { src: usize },
    Add { lhs: usize, rhs: usize },
    Xor { lhs: usize, rhs: usize },
    And { lhs: usize, rhs: usize },
    Or { lhs: usize, rhs: usize },
    Mul { lhs: usize, rhs: usize },
    Sub { lhs: usize, rhs: usize },
    LShr { lhs: usize, rhs: usize },
    AShr { lhs: usize, rhs: usize },
    Shl { lhs: usize, rhs: usize },
    UDiv { lhs: usize, rhs: usize },
    URem { lhs: usize, rhs: usize },
    SDiv { lhs: usize, rhs: usize },
    SRem { lhs: usize, rhs: usize },
    BVule { lhs: usize, rhs: usize },
    BVult { lhs: usize, rhs: usize },
    BVsle { lhs: usize, rhs: usize },
    BVslt { lhs: usize, rhs: usize },
    Ite { cond: usize, then_slot: usize, else_slot: usize },
    Fop0Dyn { fid: usize },
    Fop1Dyn { fid: usize, arg: usize },
    Fop2Dyn { fid: usize, lhs: usize, rhs: usize },
    FopDyn { fid: usize, args: Vec<usize> },
}

impl DefineFunPlan {
    fn eval(&self, env: &Environ, args: &[Value]) -> Result<Value, DivideByZero> {
        match self {
            DefineFunPlan::Generic {
                root,
                slot_count,
                slot_bits: _,
                instrs,
            } => {
                let mut slots = Vec::with_capacity(*slot_count);
                slots.extend(args.iter().cloned());
                for instr in instrs {
                    let value = match instr {
                        PlanInstr::Const(value) => value.clone(),
                        PlanInstr::Concat { lhs, rhs } => {
                            slots[*lhs].concat(&slots[*rhs])
                        }
                        PlanInstr::Extract { src, hi, lo } => {
                            slots[*src].extract(*hi, *lo)
                        }
                        PlanInstr::Not { src } => op::not(slots[*src].clone()),
                        PlanInstr::Neg { src } => op::neg(slots[*src].clone()),
                        PlanInstr::Add { lhs, rhs } => {
                            op::add(slots[*lhs].clone(), slots[*rhs].clone())
                        }
                        PlanInstr::Xor { lhs, rhs } => {
                            op::xor(slots[*lhs].clone(), slots[*rhs].clone())
                        }
                        PlanInstr::And { lhs, rhs } => {
                            op::and(slots[*lhs].clone(), slots[*rhs].clone())
                        }
                        PlanInstr::Or { lhs, rhs } => {
                            op::or(slots[*lhs].clone(), slots[*rhs].clone())
                        }
                        PlanInstr::Mul { lhs, rhs } => {
                            op::mul(slots[*lhs].clone(), slots[*rhs].clone())
                        }
                        PlanInstr::Sub { lhs, rhs } => {
                            op::sub(slots[*lhs].clone(), slots[*rhs].clone())
                        }
                        PlanInstr::LShr { lhs, rhs } => {
                            op::lshr(slots[*lhs].clone(), slots[*rhs].clone())
                        }
                        PlanInstr::AShr { lhs, rhs } => {
                            op::ashr(slots[*lhs].clone(), slots[*rhs].clone())
                        }
                        PlanInstr::Shl { lhs, rhs } => {
                            op::shl(slots[*lhs].clone(), slots[*rhs].clone())
                        }
                        PlanInstr::UDiv { lhs, rhs } => {
                            op::udiv(slots[*lhs].clone(), slots[*rhs].clone())?
                        }
                        PlanInstr::URem { lhs, rhs } => {
                            op::urem(slots[*lhs].clone(), slots[*rhs].clone())?
                        }
                        PlanInstr::SDiv { lhs, rhs } => {
                            op::sdiv(slots[*lhs].clone(), slots[*rhs].clone())?
                        }
                        PlanInstr::SRem { lhs, rhs } => {
                            op::srem(slots[*lhs].clone(), slots[*rhs].clone())?
                        }
                        PlanInstr::BVule { lhs, rhs } => crate::enumerate::op::ule(slots[*lhs].clone(), slots[*rhs].clone()),
                        PlanInstr::BVult { lhs, rhs } => crate::enumerate::op::ult(slots[*lhs].clone(), slots[*rhs].clone()),
                        PlanInstr::BVsle { lhs, rhs } => crate::enumerate::op::sle(slots[*lhs].clone(), slots[*rhs].clone()),
                        PlanInstr::BVslt { lhs, rhs } => crate::enumerate::op::slt(slots[*lhs].clone(), slots[*rhs].clone()),
                        PlanInstr::Ite {
                            cond,
                            then_slot,
                            else_slot,
                        } => op::ite(
                            slots[*cond].clone(),
                            slots[*then_slot].clone(),
                            slots[*else_slot].clone(),
                        ),
                        PlanInstr::Fop0Dyn { fid } => env.eval_defined(*fid, &[])?,
                        PlanInstr::Fop1Dyn { fid, arg } => {
                            env.eval_defined(*fid, &[slots[*arg].clone()])?
                        }
                        PlanInstr::Fop2Dyn { fid, lhs, rhs } => env.eval_defined(
                            *fid,
                            &[slots[*lhs].clone(), slots[*rhs].clone()],
                        )?,
                        PlanInstr::FopDyn { fid, args } => {
                            let dyn_args =
                                args.iter().map(|slot| slots[*slot].clone()).collect::<Vec<_>>();
                            env.eval_defined(*fid, &dyn_args)?
                        }
                    };
                    slots.push(value);
                }
                Ok(slots[*root].clone())
            }
            DefineFunPlan::BitCircuit(plan) => plan.eval(args),
        }
    }
}

impl BitCircuitPlan {
    pub fn pruned(&self, demanded_output_bits: &[usize]) -> Option<Self> {
        if demanded_output_bits.len() >= self.output_bits.len() {
            return None;
        }
        let num_bindings = self.bindings.len();
        let mut needed = vec![false; num_bindings];

        fn mark_atom(atom: &BoolAtom, needed: &mut [bool]) {
            if let BoolAtom::Temp(idx) = atom {
                if !needed[*idx] {
                    needed[*idx] = true;
                }
            }
        }

        fn mark_node(node: &BoolNode, needed: &mut [bool]) {
            match node {
                BoolNode::Atom(a) => mark_atom(a, needed),
                BoolNode::Not(a) => mark_atom(a, needed),
                BoolNode::And(a, b) | BoolNode::Or(a, b) | BoolNode::Xor(a, b) => {
                    mark_atom(a, needed);
                    mark_atom(b, needed);
                }
                BoolNode::Ite(a, b, c) => {
                    mark_atom(a, needed);
                    mark_atom(b, needed);
                    mark_atom(c, needed);
                }
            }
        }

        for &bit_idx in demanded_output_bits {
            mark_atom(&self.output_bits[bit_idx], &mut needed);
        }
        for idx in (0..num_bindings).rev() {
            if needed[idx] {
                mark_node(&self.bindings[idx], &mut needed);
            }
        }

        let kept_count = needed.iter().filter(|&&b| b).count();
        if kept_count >= num_bindings * 9 / 10 {
            return None;
        }

        let mut remap = vec![0usize; num_bindings];
        let mut new_bindings = Vec::with_capacity(kept_count);
        let mut new_idx = 0;
        for (old_idx, &keep) in needed.iter().enumerate() {
            if keep {
                remap[old_idx] = new_idx;
                new_bindings.push(self.bindings[old_idx].clone());
                new_idx += 1;
            }
        }

        fn remap_atom(atom: &BoolAtom, remap: &[usize]) -> BoolAtom {
            match atom {
                BoolAtom::Temp(idx) => BoolAtom::Temp(remap[*idx]),
                other => other.clone(),
            }
        }

        fn remap_node(node: &BoolNode, remap: &[usize]) -> BoolNode {
            match node {
                BoolNode::Atom(a) => BoolNode::Atom(remap_atom(a, remap)),
                BoolNode::Not(a) => BoolNode::Not(remap_atom(a, remap)),
                BoolNode::And(a, b) => BoolNode::And(remap_atom(a, remap), remap_atom(b, remap)),
                BoolNode::Or(a, b) => BoolNode::Or(remap_atom(a, remap), remap_atom(b, remap)),
                BoolNode::Xor(a, b) => BoolNode::Xor(remap_atom(a, remap), remap_atom(b, remap)),
                BoolNode::Ite(a, b, c) => BoolNode::Ite(
                    remap_atom(a, remap),
                    remap_atom(b, remap),
                    remap_atom(c, remap),
                ),
            }
        }

        let remapped_bindings: Vec<BoolNode> = new_bindings
            .into_iter()
            .map(|node| remap_node(&node, &remap))
            .collect();

        let new_output_bits: Vec<BoolAtom> = self.output_bits
            .iter()
            .enumerate()
            .map(|(idx, atom)| {
                if demanded_output_bits.contains(&idx) {
                    remap_atom(atom, &remap)
                } else {
                    BoolAtom::Const(false)
                }
            })
            .collect();

        let ret_bits = self.ret_bits;
        let mut seen_inputs = rustc_hash::FxHashSet::default();
        for node in &remapped_bindings {
            node.collect_input_bits(&mut seen_inputs);
        }
        for atom in &new_output_bits {
            atom.collect_input_bits(&mut seen_inputs);
        }
        let input_slots: Vec<(usize, usize)> = seen_inputs.into_iter().collect();

        Some(BitCircuitPlan {
            bindings: remapped_bindings,
            output_bits: new_output_bits,
            ret_bits,
            input_slots,
        })
    }
}

impl BitCircuitPlan {
    pub fn eval(&self, args: &[Value]) -> Result<Value, DivideByZero> {
        let mut temps = Vec::with_capacity(self.bindings.len());
        for binding in &self.bindings {
            let value = binding.eval(args, &temps);
            temps.push(value);
        }
        let mut words = vec![0u64; self.ret_bits.div_ceil(64)];
        for (bit_idx, atom) in self.output_bits.iter().enumerate() {
            if atom.eval(args, &temps) {
                words[bit_idx / 64] |= 1u64 << (bit_idx % 64);
            }
        }
        Ok(value_from_words(words, self.ret_bits))
    }
}

impl BitCircuitPlan {
    /// Evaluate the circuit for up to 64 input sets simultaneously.
    /// `args_batch[candidate][arg]` gives the Value for that candidate's argument.
    /// Returns one Value per candidate (up to `count`).
    pub fn eval_batch(&self, args_batch: &[&[Value]], count: usize) -> Vec<Value> {
        debug_assert!(count <= 64 && count > 0);
        let nargs = args_batch[0].len();
        let stride = args_batch[0].iter().map(|v| v.bits()).max().unwrap_or(0);
        let input_len = nargs * stride;

        thread_local! {
            static INPUT_BUF: std::cell::RefCell<Vec<u64>> = std::cell::RefCell::new(Vec::new());
            static TEMPS_BUF: std::cell::RefCell<Vec<u64>> = std::cell::RefCell::new(Vec::new());
        }

        INPUT_BUF.with(|buf| {
            let mut input_words = buf.borrow_mut();
            input_words.clear();
            input_words.resize(input_len, 0);

            for &(arg, bit) in &self.input_slots {
                if arg >= nargs || bit >= stride {
                    continue;
                }
                let idx = arg * stride + bit;
                let mut word = 0u64;
                for (cand_idx, args) in args_batch.iter().enumerate().take(count) {
                    if args[arg].bit(bit) {
                        word |= 1u64 << cand_idx;
                    }
                }
                input_words[idx] = word;
            }

            TEMPS_BUF.with(|tbuf| {
                let mut temps = tbuf.borrow_mut();
                temps.clear();
                temps.reserve(self.bindings.len());
                for node in &self.bindings {
                    let val = node.eval_word(&input_words, &temps, stride);
                    temps.push(val);
                }

                let num_words = self.ret_bits.div_ceil(64);
                let mut out_words = vec![vec![0u64; num_words]; count];

                for (bit_idx, atom) in self.output_bits.iter().enumerate() {
                    let word = atom.word(&input_words, &temps, stride);
                    let out_word_idx = bit_idx / 64;
                    let out_bit = bit_idx % 64;
                    for cand_idx in 0..count {
                        if (word >> cand_idx) & 1 == 1 {
                            out_words[cand_idx][out_word_idx] |= 1u64 << out_bit;
                        }
                    }
                }

                out_words
                    .into_iter()
                    .map(|words| value_from_words(words, self.ret_bits))
                    .collect()
            })
        })
    }
}

impl BoolNode {
    fn eval_word(&self, input_words: &[u64], temps: &[u64], stride: usize) -> u64 {
        match self {
            BoolNode::Atom(atom) => atom.word(input_words, temps, stride),
            BoolNode::Not(atom) => !atom.word(input_words, temps, stride),
            BoolNode::And(lhs, rhs) => {
                lhs.word(input_words, temps, stride) & rhs.word(input_words, temps, stride)
            }
            BoolNode::Or(lhs, rhs) => {
                lhs.word(input_words, temps, stride) | rhs.word(input_words, temps, stride)
            }
            BoolNode::Xor(lhs, rhs) => {
                lhs.word(input_words, temps, stride) ^ rhs.word(input_words, temps, stride)
            }
            BoolNode::Ite(cond, then_atom, else_atom) => {
                let c = cond.word(input_words, temps, stride);
                let t = then_atom.word(input_words, temps, stride);
                let e = else_atom.word(input_words, temps, stride);
                (c & e) | (!c & t)
            }
        }
    }
}

impl BoolAtom {
    fn word(&self, input_words: &[u64], temps: &[u64], stride: usize) -> u64 {
        match self {
            BoolAtom::Const(true) => u64::MAX,
            BoolAtom::Const(false) => 0,
            BoolAtom::InputBit { arg, bit } => {
                let idx = arg * stride + bit;
                if idx < input_words.len() {
                    input_words[idx]
                } else {
                    0
                }
            }
            BoolAtom::Temp(idx) => temps[*idx],
        }
    }

    fn collect_input_bits(&self, out: &mut rustc_hash::FxHashSet<(usize, usize)>) {
        if let BoolAtom::InputBit { arg, bit } = self {
            out.insert((*arg, *bit));
        }
    }
}

impl BoolNode {
    fn collect_input_bits(&self, out: &mut rustc_hash::FxHashSet<(usize, usize)>) {
        match self {
            BoolNode::Atom(a) => a.collect_input_bits(out),
            BoolNode::Not(a) => a.collect_input_bits(out),
            BoolNode::And(a, b) | BoolNode::Or(a, b) | BoolNode::Xor(a, b) => {
                a.collect_input_bits(out);
                b.collect_input_bits(out);
            }
            BoolNode::Ite(a, b, c) => {
                a.collect_input_bits(out);
                b.collect_input_bits(out);
                c.collect_input_bits(out);
            }
        }
    }
}

impl BoolNode {
    fn eval(&self, args: &[Value], temps: &[bool]) -> bool {
        match self {
            BoolNode::Atom(atom) => atom.eval(args, temps),
            BoolNode::Not(atom) => !atom.eval(args, temps),
            BoolNode::And(lhs, rhs) => lhs.eval(args, temps) & rhs.eval(args, temps),
            BoolNode::Or(lhs, rhs) => lhs.eval(args, temps) | rhs.eval(args, temps),
            BoolNode::Xor(lhs, rhs) => lhs.eval(args, temps) ^ rhs.eval(args, temps),
            BoolNode::Ite(cond, then_atom, else_atom) => {
                if cond.eval(args, temps) {
                    else_atom.eval(args, temps)
                } else {
                    then_atom.eval(args, temps)
                }
            }
        }
    }
}

impl BoolAtom {
    fn eval(&self, args: &[Value], temps: &[bool]) -> bool {
        match self {
            BoolAtom::Const(value) => *value,
            BoolAtom::InputBit { arg, bit } => args[*arg].bit(*bit),
            BoolAtom::Temp(idx) => temps[*idx],
        }
    }

    fn try_leaf(expr: &OwnedExpr, nargs: usize, let_offsets: &[usize]) -> Option<Self> {
        match expr {
            OwnedExpr::Const(value) if value.bits() == 1 => Some(Self::Const(!value.is_zero())),
            OwnedExpr::Var(idx, _) if *idx < nargs => None,
            OwnedExpr::Var(idx, _) => {
                let let_idx = idx.checked_sub(nargs)?;
                let_offsets.get(let_idx).copied().map(Self::Temp)
            }
            OwnedExpr::Extract(src, hi, lo) if hi == lo => match src.as_ref() {
                OwnedExpr::Var(idx, _) if *idx < nargs => Some(Self::InputBit {
                    arg: *idx,
                    bit: *lo as usize,
                }),
                OwnedExpr::Var(idx, _) => {
                    let let_idx = idx.checked_sub(nargs)?;
                    let_offsets.get(let_idx).copied().map(Self::Temp)
                }
                _ => None,
            },
            _ => None,
        }
    }

    fn compile(
        expr: &OwnedExpr,
        nargs: usize,
        bindings: &mut Vec<BoolNode>,
        let_offsets: &[usize],
    ) -> Option<Self> {
        if let Some(atom) = Self::try_leaf(expr, nargs, let_offsets) {
            return Some(atom);
        }
        let node = BoolNode::compile(expr, nargs, bindings, let_offsets)?;
        let idx = bindings.len();
        bindings.push(node);
        Some(BoolAtom::Temp(idx))
    }

    fn compile_dedup(
        expr: &OwnedExpr,
        nargs: usize,
        bindings: &mut Vec<BoolNode>,
        let_offsets: &[usize],
        dedup: &mut rustc_hash::FxHashMap<BoolNode, usize>,
    ) -> Option<Self> {
        if let Some(atom) = Self::try_leaf(expr, nargs, let_offsets) {
            return Some(atom);
        }
        let node = BoolNode::compile_dedup(expr, nargs, bindings, let_offsets, dedup)?;
        if let Some(&idx) = dedup.get(&node) {
            return Some(BoolAtom::Temp(idx));
        }
        let idx = bindings.len();
        dedup.insert(node.clone(), idx);
        bindings.push(node);
        Some(BoolAtom::Temp(idx))
    }
}

impl BoolNode {
    fn compile(
        expr: &OwnedExpr,
        nargs: usize,
        bindings: &mut Vec<BoolNode>,
        let_offsets: &[usize],
    ) -> Option<Self> {
        match expr {
            OwnedExpr::Const(value) if value.bits() == 1 => {
                Some(Self::Atom(BoolAtom::Const(!value.is_zero())))
            }
            OwnedExpr::Var(_, _) | OwnedExpr::Extract(_, _, _) => {
                Some(Self::Atom(BoolAtom::try_leaf(expr, nargs, let_offsets)?))
            }
            OwnedExpr::Not(inner) => Some(Self::Not(BoolAtom::compile(
                inner,
                nargs,
                bindings,
                let_offsets,
            )?)),
            OwnedExpr::And(lhs, rhs) => Some(Self::And(
                BoolAtom::compile(lhs, nargs, bindings, let_offsets)?,
                BoolAtom::compile(rhs, nargs, bindings, let_offsets)?,
            )),
            OwnedExpr::Or(lhs, rhs) => Some(Self::Or(
                BoolAtom::compile(lhs, nargs, bindings, let_offsets)?,
                BoolAtom::compile(rhs, nargs, bindings, let_offsets)?,
            )),
            OwnedExpr::Xor(lhs, rhs) => Some(Self::Xor(
                BoolAtom::compile(lhs, nargs, bindings, let_offsets)?,
                BoolAtom::compile(rhs, nargs, bindings, let_offsets)?,
            )),
            OwnedExpr::Ite(cond, then_expr, else_expr) => Some(Self::Ite(
                BoolAtom::compile(cond, nargs, bindings, let_offsets)?,
                BoolAtom::compile(then_expr, nargs, bindings, let_offsets)?,
                BoolAtom::compile(else_expr, nargs, bindings, let_offsets)?,
            )),
            _ => None,
        }
    }

    fn compile_dedup(
        expr: &OwnedExpr,
        nargs: usize,
        bindings: &mut Vec<BoolNode>,
        let_offsets: &[usize],
        dedup: &mut rustc_hash::FxHashMap<BoolNode, usize>,
    ) -> Option<Self> {
        match expr {
            OwnedExpr::Const(value) if value.bits() == 1 => {
                Some(Self::Atom(BoolAtom::Const(!value.is_zero())))
            }
            OwnedExpr::Var(_, _) | OwnedExpr::Extract(_, _, _) => {
                Some(Self::Atom(BoolAtom::try_leaf(expr, nargs, let_offsets)?))
            }
            OwnedExpr::Not(inner) => Some(Self::Not(BoolAtom::compile_dedup(
                inner,
                nargs,
                bindings,
                let_offsets,
                dedup,
            )?)),
            OwnedExpr::And(lhs, rhs) => Some(Self::And(
                BoolAtom::compile_dedup(lhs, nargs, bindings, let_offsets, dedup)?,
                BoolAtom::compile_dedup(rhs, nargs, bindings, let_offsets, dedup)?,
            )),
            OwnedExpr::Or(lhs, rhs) => Some(Self::Or(
                BoolAtom::compile_dedup(lhs, nargs, bindings, let_offsets, dedup)?,
                BoolAtom::compile_dedup(rhs, nargs, bindings, let_offsets, dedup)?,
            )),
            OwnedExpr::Xor(lhs, rhs) => Some(Self::Xor(
                BoolAtom::compile_dedup(lhs, nargs, bindings, let_offsets, dedup)?,
                BoolAtom::compile_dedup(rhs, nargs, bindings, let_offsets, dedup)?,
            )),
            OwnedExpr::Ite(cond, then_expr, else_expr) => Some(Self::Ite(
                BoolAtom::compile_dedup(cond, nargs, bindings, let_offsets, dedup)?,
                BoolAtom::compile_dedup(then_expr, nargs, bindings, let_offsets, dedup)?,
                BoolAtom::compile_dedup(else_expr, nargs, bindings, let_offsets, dedup)?,
            )),
            _ => None,
        }
    }
}

fn value_from_words(words: Vec<u64>, bits: usize) -> Value {
    if bits <= 64 {
        Value::from_u64(words.first().copied().unwrap_or(0), bits)
    } else {
        let mut raw = num_bigint::BigUint::from(0u8);
        for word in words.iter().enumerate().rev() {
            raw <<= 64;
            raw |= num_bigint::BigUint::from(word.1.to_owned());
        }
        Value::from_biguint(raw, bits)
    }
}

fn flatten_concat_bits<'a>(expr: &'a OwnedExpr, out: &mut Vec<&'a OwnedExpr>) -> bool {
    match expr {
        OwnedExpr::Concat(high, low) => {
            if !flatten_concat_bits(low, out) {
                return false;
            }
            flatten_concat_bits(high, out)
        }
        OwnedExpr::Const(value) if value.bits() == 1 => {
            out.push(expr);
            true
        }
        _ if expr.width() == 1 => {
            out.push(expr);
            true
        }
        _ => false,
    }
}

fn flatten_concat_bits_or_consts<'a>(expr: &'a OwnedExpr, out: &mut Vec<&'a OwnedExpr>) -> bool {
    match expr {
        OwnedExpr::Concat(high, low) => {
            if !flatten_concat_bits_or_consts(low, out) {
                return false;
            }
            flatten_concat_bits_or_consts(high, out)
        }
        OwnedExpr::Const(_) => {
            out.push(expr);
            true
        }
        _ if expr.width() == 1 => {
            out.push(expr);
            true
        }
        _ => false,
    }
}

impl BitCircuitPlan {
    /// Try to compile a define-fun body into a flat boolean circuit.
    /// Handles let-bindings (must be 1-bit each), then a concat tree whose
    /// leaves are either 1-bit expressions or multi-bit constants.
    /// Returns `None` for any shape we don't recognize (callers fall back
    /// to the Generic plan).
    pub fn try_compile(expr: &OwnedExpr, nargs: usize, ret_bits: usize) -> Option<Self> {
        let mut bindings = Vec::new();
        let mut let_offsets: Vec<usize> = Vec::new();
        let mut current = expr;
        while let OwnedExpr::Let(_, value, body) = current {
            if value.width() != 1 {
                return None;
            }
            let node = BoolNode::compile(value, nargs, &mut bindings, &let_offsets)?;
            let pos = bindings.len();
            bindings.push(node);
            let_offsets.push(pos);
            current = body;
        }
        if let OwnedExpr::Const(_) = current {
            return None;
        }
        let mut raw_bits = Vec::new();
        if !flatten_concat_bits(current, &mut raw_bits) {
            raw_bits.clear();
            if !flatten_concat_bits_or_consts(current, &mut raw_bits) {
                return None;
            }
        }
        let mut output_bits = Vec::new();
        let mut dedup = rustc_hash::FxHashMap::default();
        for leaf in &raw_bits {
            match leaf {
                OwnedExpr::Const(value) if value.bits() > 1 => {
                    for i in 0..value.bits() {
                        output_bits.push(BoolAtom::Const(value.bit(i)));
                    }
                }
                _ => {
                    output_bits.push(BoolAtom::compile_dedup(leaf, nargs, &mut bindings, &let_offsets, &mut dedup)?);
                }
            }
        }
        if output_bits.len() != ret_bits {
            return None;
        }
        let mut seen_inputs = rustc_hash::FxHashSet::default();
        for node in &bindings {
            node.collect_input_bits(&mut seen_inputs);
        }
        for atom in &output_bits {
            atom.collect_input_bits(&mut seen_inputs);
        }
        let input_slots: Vec<(usize, usize)> = seen_inputs.into_iter().collect();
        Some(BitCircuitPlan {
            bindings,
            output_bits,
            ret_bits,
            input_slots,
        })
    }
}

impl DefineFunPlan {
    /// Compile an OwnedExpr to an executable plan. Prefers the
    /// boolean-circuit fast-path when possible, otherwise falls back to a
    /// generic stack-machine plan.
    pub fn compile(expr: &OwnedExpr, arg_bits: &[usize]) -> Self {
        let nargs = arg_bits.len();
        let ret_bits = expr.width();
        if let Some(plan) = BitCircuitPlan::try_compile(expr, nargs, ret_bits) {
            return DefineFunPlan::BitCircuit(plan);
        }
        compile_generic(expr, arg_bits, ret_bits)
    }
}

fn compile_generic(expr: &OwnedExpr, arg_bits: &[usize], _ret_bits: usize) -> DefineFunPlan {
    let nargs = arg_bits.len();
    fn compile_expr(
        expr: &OwnedExpr,
        env_slots: &mut Vec<usize>,
        next_slot: &mut usize,
        slot_bits: &mut Vec<usize>,
        instrs: &mut Vec<PlanInstr>,
    ) -> usize {
        let push = |
            instr: PlanInstr,
            width: usize,
            next_slot: &mut usize,
            slot_bits: &mut Vec<usize>,
            instrs: &mut Vec<PlanInstr>,
        | {
            let slot = *next_slot;
            *next_slot += 1;
            slot_bits.push(width);
            instrs.push(instr);
            slot
        };
        match expr {
            OwnedExpr::Var(idx, _) => env_slots[*idx],
            OwnedExpr::Const(value) => push(
                PlanInstr::Const(value.clone()),
                value.bits(),
                next_slot,
                slot_bits,
                instrs,
            ),
            OwnedExpr::Concat(lhs, rhs) => {
                let lhs = compile_expr(lhs, env_slots, next_slot, slot_bits, instrs);
                let rhs = compile_expr(rhs, env_slots, next_slot, slot_bits, instrs);
                push(
                    PlanInstr::Concat { lhs, rhs },
                    expr.width(),
                    next_slot,
                    slot_bits,
                    instrs,
                )
            }
            OwnedExpr::Extract(src, hi, lo) => {
                let src = compile_expr(src, env_slots, next_slot, slot_bits, instrs);
                push(
                    PlanInstr::Extract { src, hi: *hi, lo: *lo },
                    expr.width(),
                    next_slot,
                    slot_bits,
                    instrs,
                )
            }
            OwnedExpr::Not(src) => {
                let src = compile_expr(src, env_slots, next_slot, slot_bits, instrs);
                push(PlanInstr::Not { src }, expr.width(), next_slot, slot_bits, instrs)
            }
            OwnedExpr::Neg(src) => {
                let src = compile_expr(src, env_slots, next_slot, slot_bits, instrs);
                push(PlanInstr::Neg { src }, expr.width(), next_slot, slot_bits, instrs)
            }
            OwnedExpr::Add(lhs, rhs) => {
                let lhs = compile_expr(lhs, env_slots, next_slot, slot_bits, instrs);
                let rhs = compile_expr(rhs, env_slots, next_slot, slot_bits, instrs);
                push(PlanInstr::Add { lhs, rhs }, expr.width(), next_slot, slot_bits, instrs)
            }
            OwnedExpr::Xor(lhs, rhs) => {
                let lhs = compile_expr(lhs, env_slots, next_slot, slot_bits, instrs);
                let rhs = compile_expr(rhs, env_slots, next_slot, slot_bits, instrs);
                push(PlanInstr::Xor { lhs, rhs }, expr.width(), next_slot, slot_bits, instrs)
            }
            OwnedExpr::And(lhs, rhs) => {
                let lhs = compile_expr(lhs, env_slots, next_slot, slot_bits, instrs);
                let rhs = compile_expr(rhs, env_slots, next_slot, slot_bits, instrs);
                push(PlanInstr::And { lhs, rhs }, expr.width(), next_slot, slot_bits, instrs)
            }
            OwnedExpr::Or(lhs, rhs) => {
                let lhs = compile_expr(lhs, env_slots, next_slot, slot_bits, instrs);
                let rhs = compile_expr(rhs, env_slots, next_slot, slot_bits, instrs);
                push(PlanInstr::Or { lhs, rhs }, expr.width(), next_slot, slot_bits, instrs)
            }
            OwnedExpr::Mul(lhs, rhs) => {
                let lhs = compile_expr(lhs, env_slots, next_slot, slot_bits, instrs);
                let rhs = compile_expr(rhs, env_slots, next_slot, slot_bits, instrs);
                push(PlanInstr::Mul { lhs, rhs }, expr.width(), next_slot, slot_bits, instrs)
            }
            OwnedExpr::Sub(lhs, rhs) => {
                let lhs = compile_expr(lhs, env_slots, next_slot, slot_bits, instrs);
                let rhs = compile_expr(rhs, env_slots, next_slot, slot_bits, instrs);
                push(PlanInstr::Sub { lhs, rhs }, expr.width(), next_slot, slot_bits, instrs)
            }
            OwnedExpr::LShr(lhs, rhs) => {
                let lhs = compile_expr(lhs, env_slots, next_slot, slot_bits, instrs);
                let rhs = compile_expr(rhs, env_slots, next_slot, slot_bits, instrs);
                push(PlanInstr::LShr { lhs, rhs }, expr.width(), next_slot, slot_bits, instrs)
            }
            OwnedExpr::AShr(lhs, rhs) => {
                let lhs = compile_expr(lhs, env_slots, next_slot, slot_bits, instrs);
                let rhs = compile_expr(rhs, env_slots, next_slot, slot_bits, instrs);
                push(PlanInstr::AShr { lhs, rhs }, expr.width(), next_slot, slot_bits, instrs)
            }
            OwnedExpr::Shl(lhs, rhs) => {
                let lhs = compile_expr(lhs, env_slots, next_slot, slot_bits, instrs);
                let rhs = compile_expr(rhs, env_slots, next_slot, slot_bits, instrs);
                push(PlanInstr::Shl { lhs, rhs }, expr.width(), next_slot, slot_bits, instrs)
            }
            OwnedExpr::UDiv(lhs, rhs) => {
                let lhs = compile_expr(lhs, env_slots, next_slot, slot_bits, instrs);
                let rhs = compile_expr(rhs, env_slots, next_slot, slot_bits, instrs);
                push(PlanInstr::UDiv { lhs, rhs }, expr.width(), next_slot, slot_bits, instrs)
            }
            OwnedExpr::URem(lhs, rhs) => {
                let lhs = compile_expr(lhs, env_slots, next_slot, slot_bits, instrs);
                let rhs = compile_expr(rhs, env_slots, next_slot, slot_bits, instrs);
                push(PlanInstr::URem { lhs, rhs }, expr.width(), next_slot, slot_bits, instrs)
            }
            OwnedExpr::SDiv(lhs, rhs) => {
                let lhs = compile_expr(lhs, env_slots, next_slot, slot_bits, instrs);
                let rhs = compile_expr(rhs, env_slots, next_slot, slot_bits, instrs);
                push(PlanInstr::SDiv { lhs, rhs }, expr.width(), next_slot, slot_bits, instrs)
            }
            OwnedExpr::SRem(lhs, rhs) => {
                let lhs = compile_expr(lhs, env_slots, next_slot, slot_bits, instrs);
                let rhs = compile_expr(rhs, env_slots, next_slot, slot_bits, instrs);
                push(PlanInstr::SRem { lhs, rhs }, expr.width(), next_slot, slot_bits, instrs)
            }
            OwnedExpr::BVule(lhs, rhs) => {
                let lhs = compile_expr(lhs, env_slots, next_slot, slot_bits, instrs);
                let rhs = compile_expr(rhs, env_slots, next_slot, slot_bits, instrs);
                push(PlanInstr::BVule { lhs, rhs }, 1, next_slot, slot_bits, instrs)
            }
            OwnedExpr::BVult(lhs, rhs) => {
                let lhs = compile_expr(lhs, env_slots, next_slot, slot_bits, instrs);
                let rhs = compile_expr(rhs, env_slots, next_slot, slot_bits, instrs);
                push(PlanInstr::BVult { lhs, rhs }, 1, next_slot, slot_bits, instrs)
            }
            OwnedExpr::BVsle(lhs, rhs) => {
                let lhs = compile_expr(lhs, env_slots, next_slot, slot_bits, instrs);
                let rhs = compile_expr(rhs, env_slots, next_slot, slot_bits, instrs);
                push(PlanInstr::BVsle { lhs, rhs }, 1, next_slot, slot_bits, instrs)
            }
            OwnedExpr::BVslt(lhs, rhs) => {
                let lhs = compile_expr(lhs, env_slots, next_slot, slot_bits, instrs);
                let rhs = compile_expr(rhs, env_slots, next_slot, slot_bits, instrs);
                push(PlanInstr::BVslt { lhs, rhs }, 1, next_slot, slot_bits, instrs)
            }
            OwnedExpr::Ite(cond, then_expr, else_expr) => {
                let cond = compile_expr(cond, env_slots, next_slot, slot_bits, instrs);
                let then_slot = compile_expr(then_expr, env_slots, next_slot, slot_bits, instrs);
                let else_slot = compile_expr(else_expr, env_slots, next_slot, slot_bits, instrs);
                push(
                    PlanInstr::Ite { cond, then_slot, else_slot },
                    expr.width(),
                    next_slot,
                    slot_bits,
                    instrs,
                )
            }
            OwnedExpr::Let(_, value, body) => {
                let value_slot = compile_expr(value, env_slots, next_slot, slot_bits, instrs);
                env_slots.push(value_slot);
                let body_slot = compile_expr(body, env_slots, next_slot, slot_bits, instrs);
                env_slots.pop();
                body_slot
            }
            OwnedExpr::Func(fid, args) => {
                let compiled_args: Vec<usize> = args
                    .iter()
                    .map(|arg| compile_expr(arg, env_slots, next_slot, slot_bits, instrs))
                    .collect();
                if compiled_args.is_empty() {
                    push(
                        PlanInstr::Fop0Dyn { fid: *fid },
                        expr.width(),
                        next_slot,
                        slot_bits,
                        instrs,
                    )
                } else if compiled_args.len() == 1 {
                    push(
                        PlanInstr::Fop1Dyn { fid: *fid, arg: compiled_args[0] },
                        expr.width(),
                        next_slot,
                        slot_bits,
                        instrs,
                    )
                } else if compiled_args.len() == 2 {
                    push(
                        PlanInstr::Fop2Dyn { fid: *fid, lhs: compiled_args[0], rhs: compiled_args[1] },
                        expr.width(),
                        next_slot,
                        slot_bits,
                        instrs,
                    )
                } else {
                    push(
                        PlanInstr::FopDyn { fid: *fid, args: compiled_args },
                        expr.width(),
                        next_slot,
                        slot_bits,
                        instrs,
                    )
                }
            }
        }
    }

    let mut instrs = Vec::new();
    let mut env_slots = (0..nargs).collect::<Vec<_>>();
    let mut slot_bits = arg_bits.to_vec();
    let mut next_slot = nargs;
    let root = compile_expr(expr, &mut env_slots, &mut next_slot, &mut slot_bits, &mut instrs);
    DefineFunPlan::Generic {
        root,
        slot_count: next_slot,
        slot_bits,
        instrs,
    }
}

pub struct Environ(UnsafeCell<Vec<DefineFun>>);

impl Environ {
    pub fn new() -> Self {
        Environ(Vec::new().into())
    }

    pub fn inner(&self) -> &mut Vec<DefineFun> {
        unsafe { self.0.get().as_mut().unwrap() }
    }

    pub fn clear(&self) {
        self.inner().clear();
    }

    pub fn parse_from_file(&self, file: &SyGuSFile) -> Result<(), Error> {
        let view = ProblemView::from_file(file);
        self.parse_from_view(&view)
    }

    pub fn parse_from_view(&self, view: &ProblemView<'_>) -> Result<(), Error> {
        // SyGuS 2.1 §3.7: define-fun bodies may reference synth-funs.
        // We append referenced nullary synth-funs to the parsing env as
        // closure slots after the real args; callers of `eval_defined` must
        // supply the current value of each referenced synth-fun in this order.
        let synth_candidates: Vec<(&'static str, u64)> = view
            .synth_funs
            .iter()
            .filter(|sf| sf.args.is_empty())
            .filter_map(|sf| {
                let bits = view.sort_aliases.parse_sort_width(sf.ret)? as u64;
                let name: &'static str = Box::leak(sf.name.to_string().into_boxed_str());
                Some((name, bits))
            })
            .collect();

        for def in &view.define_funs {
            if def.name == "if0" || def.name == "im" {
                continue;
            }
            let args: Vec<(&'static str, u64)> = def
                .args
                .iter()
                .map(|x| {
                    let name = Box::leak(x.name.clone().into_boxed_str()) as &'static str;
                    let bits = view.sort_aliases.parse_sort_width(&x.sort).unwrap_or(1) as u64;
                    (name, bits)
                })
                .collect();
            let name = Box::leak(def.name.to_string().into_boxed_str());
            let ret_bits = view.sort_aliases.parse_sort_width(def.ret).ok_or_else(|| {
                new_custom_error_span(
                    format!(
                        "DefineFun: unsupported return sort for {}: {}",
                        name, def.ret
                    ),
                    pest::Span::new("", 0, 0).unwrap(),
                )
            })?;
            let mut symbols = Vec::new();
            collect_term_symbols(def.body, &mut symbols);
            let closure_args = synth_candidates
                .iter()
                .copied()
                .filter(|(candidate, _)| *candidate != name && symbols.iter().any(|sym| sym == candidate))
                .collect::<Vec<_>>();
            let mut extended_env = args.clone();
            extended_env.extend(closure_args.iter().copied());
            let expr = OwnedExpr::from_term(def.body, extended_env.as_slice())?;
            let arg_bits = args.iter().map(|(_, bits)| *bits as usize).collect::<Vec<_>>();
            let extended_arg_bits = extended_env
                .iter()
                .map(|(_, bits)| *bits as usize)
                .collect::<Vec<_>>();
            let plan = DefineFunPlan::compile(&expr, &extended_arg_bits);
            debg!(
                "DefineFun: {} {} -> {}",
                name,
                args.iter().map(|(n, _)| *n).collect::<Vec<_>>().join(", "),
                expr.summarize(160)
            );
            self.inner().push(DefineFun {
                name,
                args: args.iter().map(|(name, _)| *name).collect(),
                arg_bits,
                ret_bits,
                plan,
                expr,
                closure_args: closure_args.iter().map(|(n, _)| *n).collect(),
                closure_arg_bits: closure_args
                    .iter()
                    .map(|(_, bits)| *bits as usize)
                    .collect(),
            });
        }
        Ok(())
    }

    pub fn lookup(&self, name: &str, nargs: usize) -> Option<usize> {
        self.inner()
            .iter()
            .enumerate()
            .find(|(_, p)| p.name == name && p.args.len() == nargs)
            .map(|(i, _)| i)
    }

    pub fn deffun(&self, id: usize) -> &DefineFun {
        &self.inner()[id]
    }

    pub fn apply(&self, id: usize) -> &OwnedExpr {
        &self.inner()[id].expr
    }
    pub fn plan(&self, id: usize) -> &DefineFunPlan {
        &self.inner()[id].plan
    }
    pub fn ret_bits(&self, id: usize) -> usize {
        self.inner()[id].ret_bits
    }
    pub fn arg_bits(&self, id: usize) -> &[usize] {
        &self.inner()[id].arg_bits
    }
    pub fn name(&self, id: usize) -> &'static str {
        &self.inner()[id].name
    }
    pub fn closure_args(&self, id: usize) -> &[&'static str] {
        &self.inner()[id].closure_args
    }
    pub fn closure_arg_bits(&self, id: usize) -> &[usize] {
        &self.inner()[id].closure_arg_bits
    }
    pub fn eval_defined(
        &self,
        id: usize,
        args: &[Value],
    ) -> Result<Value, DivideByZero> {
        self.plan(id).eval(self, args)
    }
}

/// True iff the grammar is just `((<NT> <Sort> ((Constant <Sort>))))` — the
/// LFP-placeholder shape used for closure synth-funs.

unsafe impl Sync for Environ {}

lazy_static::lazy_static!(
    pub static ref ENV: Environ = Environ::new();
);

#[cfg(test)]
mod tests {
    use super::*;

    fn make_random_value(bits: usize, seed: u64) -> Value {
        let mut rng = seed;
        let num_words = bits.div_ceil(64);
        let mut words = vec![0u64; num_words];
        for w in words.iter_mut() {
            rng ^= rng << 13;
            rng ^= rng >> 7;
            rng ^= rng << 17;
            *w = rng;
        }
        if bits % 64 != 0 {
            words[num_words - 1] &= (1u64 << (bits % 64)) - 1;
        }
        value_from_words(words, bits)
    }

    fn verify_pruned_circuit(plan: &BitCircuitPlan, demanded: &[usize], num_trials: usize) {
        let pruned = match plan.pruned(demanded) {
            Some(p) => p,
            None => return,
        };
        let nargs = plan.input_slots.iter().map(|(a, _)| a + 1).max().unwrap_or(0);
        let max_bits = plan.input_slots.iter().map(|(_, b)| b + 1).max().unwrap_or(1);

        for trial in 0..num_trials {
            let args: Vec<Value> = (0..nargs)
                .map(|a| make_random_value(max_bits, (trial as u64 + 1) * 1000 + a as u64))
                .collect();

            let full_result = plan.eval(&args).unwrap();
            let pruned_result = pruned.eval(&args).unwrap();

            for &bit_idx in demanded {
                let full_bit = full_result.bit(bit_idx);
                let pruned_bit = pruned_result.bit(bit_idx);
                assert_eq!(
                    full_bit, pruned_bit,
                    "Divergence at demanded bit {} on trial {} (nargs={}, max_bits={})",
                    bit_idx, trial, nargs, max_bits
                );
            }
        }
    }

    fn verify_pruned_circuit_batch(plan: &BitCircuitPlan, demanded: &[usize], num_trials: usize) {
        let pruned = match plan.pruned(demanded) {
            Some(p) => p,
            None => return,
        };
        let nargs = plan.input_slots.iter().map(|(a, _)| a + 1).max().unwrap_or(1).max(1);
        let max_bits = plan.input_slots.iter().map(|(_, b)| b + 1).max().unwrap_or(1);

        let batch_size = 64.min(num_trials);
        let args_batch: Vec<Vec<Value>> = (0..batch_size)
            .map(|i| {
                (0..nargs)
                    .map(|a| make_random_value(max_bits, (i as u64 + 1) * 7919 + a as u64))
                    .collect()
            })
            .collect();
        let refs: Vec<&[Value]> = args_batch.iter().map(|v| v.as_slice()).collect();

        let full_results = plan.eval_batch(&refs, batch_size);
        let pruned_results = pruned.eval_batch(&refs, batch_size);

        for (cand_idx, (full, pruned_val)) in
            full_results.iter().zip(pruned_results.iter()).enumerate()
        {
            for &bit_idx in demanded {
                assert_eq!(
                    full.bit(bit_idx),
                    pruned_val.bit(bit_idx),
                    "Batch divergence at demanded bit {} candidate {}",
                    bit_idx, cand_idx
                );
            }
        }
    }

    #[test]
    fn test_pruned_simple_and_chain() {
        // Circuit: out[0] = in[0,0] & in[0,1]; out[1] = in[0,2]; out[2] = in[0,0] | in[0,3]
        let bindings = vec![
            BoolNode::And(
                BoolAtom::InputBit { arg: 0, bit: 0 },
                BoolAtom::InputBit { arg: 0, bit: 1 },
            ),
            BoolNode::Or(
                BoolAtom::InputBit { arg: 0, bit: 0 },
                BoolAtom::InputBit { arg: 0, bit: 3 },
            ),
        ];
        let output_bits = vec![
            BoolAtom::Temp(0),
            BoolAtom::InputBit { arg: 0, bit: 2 },
            BoolAtom::Temp(1),
        ];
        let plan = BitCircuitPlan {
            bindings,
            output_bits,
            ret_bits: 3,
            input_slots: vec![(0, 0), (0, 1), (0, 2), (0, 3)],
        };

        // Demand only bit 0 → should prune binding[1] (the OR gate)
        verify_pruned_circuit(&plan, &[0], 1000);
        // Demand only bit 2 → should prune binding[0] (the AND gate)
        verify_pruned_circuit(&plan, &[2], 1000);
        // Demand bits 0 and 2 → no pruning (both gates needed)
        verify_pruned_circuit(&plan, &[0, 2], 1000);
    }

    #[test]
    fn test_pruned_ite_gate() {
        // out[0] = ITE(in[0,0], in[0,1], in[0,2])
        // out[1] = in[0,3]
        let bindings = vec![BoolNode::Ite(
            BoolAtom::InputBit { arg: 0, bit: 0 },
            BoolAtom::InputBit { arg: 0, bit: 1 },
            BoolAtom::InputBit { arg: 0, bit: 2 },
        )];
        let output_bits = vec![
            BoolAtom::Temp(0),
            BoolAtom::InputBit { arg: 0, bit: 3 },
        ];
        let plan = BitCircuitPlan {
            bindings,
            output_bits,
            ret_bits: 2,
            input_slots: vec![(0, 0), (0, 1), (0, 2), (0, 3)],
        };

        verify_pruned_circuit(&plan, &[0], 1000);
        verify_pruned_circuit(&plan, &[1], 1000);
        verify_pruned_circuit_batch(&plan, &[0], 64);
    }

    #[test]
    fn test_pruned_deep_chain() {
        // Deep chain: t0 = in[0,0] & in[0,1]; t1 = t0 | in[0,2]; t2 = !t1;
        //             t3 = in[0,3] ^ in[0,4]; t4 = t3 & in[0,5]
        // out[0] = t2; out[1] = t4
        let bindings = vec![
            BoolNode::And(
                BoolAtom::InputBit { arg: 0, bit: 0 },
                BoolAtom::InputBit { arg: 0, bit: 1 },
            ),
            BoolNode::Or(BoolAtom::Temp(0), BoolAtom::InputBit { arg: 0, bit: 2 }),
            BoolNode::Not(BoolAtom::Temp(1)),
            BoolNode::Xor(
                BoolAtom::InputBit { arg: 0, bit: 3 },
                BoolAtom::InputBit { arg: 0, bit: 4 },
            ),
            BoolNode::And(BoolAtom::Temp(3), BoolAtom::InputBit { arg: 0, bit: 5 }),
        ];
        let output_bits = vec![BoolAtom::Temp(2), BoolAtom::Temp(4)];
        let plan = BitCircuitPlan {
            bindings,
            output_bits,
            ret_bits: 2,
            input_slots: vec![(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5)],
        };

        // Demand bit 0 → needs t0, t1, t2 (bindings 0,1,2); should prune t3,t4
        verify_pruned_circuit(&plan, &[0], 1000);
        // Demand bit 1 → needs t3, t4 (bindings 3,4); should prune t0,t1,t2
        verify_pruned_circuit(&plan, &[1], 1000);
        verify_pruned_circuit_batch(&plan, &[0], 64);
        verify_pruned_circuit_batch(&plan, &[1], 64);
    }

    #[test]
    fn test_pruned_two_arg_circuit() {
        // Binary operator: out[0] = in[0,0] & in[1,0]; out[1] = in[0,1] | in[1,1]
        let bindings = vec![
            BoolNode::And(
                BoolAtom::InputBit { arg: 0, bit: 0 },
                BoolAtom::InputBit { arg: 1, bit: 0 },
            ),
            BoolNode::Or(
                BoolAtom::InputBit { arg: 0, bit: 1 },
                BoolAtom::InputBit { arg: 1, bit: 1 },
            ),
        ];
        let output_bits = vec![BoolAtom::Temp(0), BoolAtom::Temp(1)];
        let plan = BitCircuitPlan {
            bindings,
            output_bits,
            ret_bits: 2,
            input_slots: vec![(0, 0), (0, 1), (1, 0), (1, 1)],
        };

        verify_pruned_circuit(&plan, &[0], 1000);
        verify_pruned_circuit(&plan, &[1], 1000);
        verify_pruned_circuit_batch(&plan, &[0], 64);
    }

    #[test]
    fn test_pruned_wide_bitvector() {
        // Simulate a wide BV (128 bits output) with shared sub-DAGs
        let mut bindings = Vec::new();
        // t0..t63: AND of in[0,i] and in[1,i]
        for i in 0..64 {
            bindings.push(BoolNode::And(
                BoolAtom::InputBit { arg: 0, bit: i },
                BoolAtom::InputBit { arg: 1, bit: i },
            ));
        }
        // t64..t127: XOR of in[0,i] and in[1,i]
        for i in 0..64 {
            bindings.push(BoolNode::Xor(
                BoolAtom::InputBit { arg: 0, bit: i },
                BoolAtom::InputBit { arg: 1, bit: i },
            ));
        }
        let mut output_bits = Vec::new();
        for i in 0..64 {
            output_bits.push(BoolAtom::Temp(i));
        }
        for i in 64..128 {
            output_bits.push(BoolAtom::Temp(i));
        }

        let mut input_slots = Vec::new();
        for i in 0..64 {
            input_slots.push((0, i));
            input_slots.push((1, i));
        }

        let plan = BitCircuitPlan {
            bindings,
            output_bits,
            ret_bits: 128,
            input_slots,
        };

        // Demand only lower 64 bits (AND results)
        let demanded_lower: Vec<usize> = (0..64).collect();
        verify_pruned_circuit(&plan, &demanded_lower, 500);
        verify_pruned_circuit_batch(&plan, &demanded_lower, 64);

        // Demand only upper 64 bits (XOR results)
        let demanded_upper: Vec<usize> = (64..128).collect();
        verify_pruned_circuit(&plan, &demanded_upper, 500);
        verify_pruned_circuit_batch(&plan, &demanded_upper, 64);

        // Demand scattered bits
        let demanded_scattered: Vec<usize> = (0..128).step_by(7).collect();
        verify_pruned_circuit(&plan, &demanded_scattered, 500);
        verify_pruned_circuit_batch(&plan, &demanded_scattered, 64);
    }

    #[test]
    fn test_pruned_shared_subdag() {
        // t0 = in[0,0] & in[0,1] (shared)
        // t1 = t0 | in[0,2]      → feeds out[0]
        // t2 = t0 ^ in[0,3]      → feeds out[1]
        // t3 = in[0,4]           → feeds out[2] (independent)
        let bindings = vec![
            BoolNode::And(
                BoolAtom::InputBit { arg: 0, bit: 0 },
                BoolAtom::InputBit { arg: 0, bit: 1 },
            ),
            BoolNode::Or(BoolAtom::Temp(0), BoolAtom::InputBit { arg: 0, bit: 2 }),
            BoolNode::Xor(BoolAtom::Temp(0), BoolAtom::InputBit { arg: 0, bit: 3 }),
            BoolNode::Atom(BoolAtom::InputBit { arg: 0, bit: 4 }),
        ];
        let output_bits = vec![
            BoolAtom::Temp(1),
            BoolAtom::Temp(2),
            BoolAtom::Temp(3),
        ];
        let plan = BitCircuitPlan {
            bindings,
            output_bits,
            ret_bits: 3,
            input_slots: vec![(0, 0), (0, 1), (0, 2), (0, 3), (0, 4)],
        };

        // Demand bit 0 → needs t0, t1
        verify_pruned_circuit(&plan, &[0], 1000);
        // Demand bit 1 → needs t0, t2
        verify_pruned_circuit(&plan, &[1], 1000);
        // Demand bit 2 → needs only t3
        verify_pruned_circuit(&plan, &[2], 1000);
        // Demand bits 0,1 → needs t0, t1, t2 (shared t0)
        verify_pruned_circuit(&plan, &[0, 1], 1000);
    }
}
