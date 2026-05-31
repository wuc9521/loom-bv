use std::cell::UnsafeCell;

use derive_more::DebugCustom;
use sygus_parser::ast::{SyGuSFile, SyGuSTerm};

use crate::{
    enumerate::{
        expr::{DivideByZero, OwnedExpr},
        op,
        value::Value,
    },
    info,
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

fn summarize_expr(expr: &OwnedExpr, limit: usize) -> String {
    let rendered = expr.to_string();
    let total = rendered.chars().count();
    if total <= limit {
        return rendered;
    }
    let prefix = rendered.chars().take(limit).collect::<String>();
    format!("{prefix}... <{} chars total>", total)
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

#[derive(Clone, Debug)]
pub(crate) enum DefineFunPlan {
    Generic {
        root: usize,
        slot_count: usize,
        slot_bits: Vec<usize>,
        instrs: Vec<PlanInstr>,
    },
    BitCircuit(BitCircuitPlan),
}

#[derive(Clone, Debug)]
pub(crate) struct BitCircuitPlan {
    pub(crate) bindings: Vec<BoolNode>,
    pub(crate) output_bits: Vec<BoolAtom>,
    pub(crate) ret_bits: usize,
}

#[derive(Clone, Debug)]
pub(crate) enum BoolNode {
    Atom(BoolAtom),
    Not(BoolAtom),
    And(BoolAtom, BoolAtom),
    Or(BoolAtom, BoolAtom),
    Xor(BoolAtom, BoolAtom),
    Ite(BoolAtom, BoolAtom, BoolAtom),
}

#[derive(Clone, Debug)]
pub(crate) enum BoolAtom {
    Const(bool),
    InputBit { arg: usize, bit: usize },
    Temp(usize),
}

#[derive(Clone, Debug)]
pub(crate) enum PlanInstr {
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
                        PlanInstr::Ite {
                            cond,
                            then_slot,
                            else_slot,
                        } => op::ite(
                            slots[*cond].clone(),
                            slots[*then_slot].clone(),
                            slots[*else_slot].clone(),
                        ),
                        PlanInstr::Fop0Dyn { fid } => env.eval_defined(*fid, 0, &[])?,
                        PlanInstr::Fop1Dyn { fid, arg } => {
                            env.eval_defined(*fid, 1, &[slots[*arg].clone()])?
                        }
                        PlanInstr::Fop2Dyn { fid, lhs, rhs } => env.eval_defined(
                            *fid,
                            2,
                            &[slots[*lhs].clone(), slots[*rhs].clone()],
                        )?,
                        PlanInstr::FopDyn { fid, args } => {
                            let dyn_args =
                                args.iter().map(|slot| slots[*slot].clone()).collect::<Vec<_>>();
                            env.eval_defined(*fid, args.len(), &dyn_args)?
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
    fn eval(&self, args: &[Value]) -> Result<Value, DivideByZero> {
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

    fn try_leaf(expr: &OwnedExpr, nargs: usize) -> Option<Self> {
        match expr {
            OwnedExpr::Const(value) if value.bits() == 1 => Some(Self::Const(!value.is_zero())),
            OwnedExpr::Var(idx, _) if *idx < nargs => None,
            OwnedExpr::Var(idx, _) => Some(Self::Temp(idx.checked_sub(nargs)?)),
            OwnedExpr::Extract(src, hi, lo) if hi == lo => match src.as_ref() {
                OwnedExpr::Var(idx, _) if *idx < nargs => Some(Self::InputBit {
                    arg: *idx,
                    bit: *lo as usize,
                }),
                OwnedExpr::Var(idx, _) => Some(Self::Temp(idx.checked_sub(nargs)?)),
                _ => None,
            },
            _ => None,
        }
    }

    fn compile(expr: &OwnedExpr, nargs: usize, bindings: &mut Vec<BoolNode>) -> Option<Self> {
        if let Some(atom) = Self::try_leaf(expr, nargs) {
            return Some(atom);
        }
        let node = BoolNode::compile(expr, nargs, bindings)?;
        let idx = bindings.len();
        bindings.push(node);
        Some(BoolAtom::Temp(idx))
    }
}

impl BoolNode {
    fn compile(expr: &OwnedExpr, nargs: usize, bindings: &mut Vec<BoolNode>) -> Option<Self> {
        match expr {
            OwnedExpr::Const(value) if value.bits() == 1 => {
                Some(Self::Atom(BoolAtom::Const(!value.is_zero())))
            }
            OwnedExpr::Var(_, _) | OwnedExpr::Extract(_, _, _) => {
                Some(Self::Atom(BoolAtom::try_leaf(expr, nargs)?))
            }
            OwnedExpr::Not(inner) => {
                Some(Self::Not(BoolAtom::compile(inner, nargs, bindings)?))
            }
            OwnedExpr::And(lhs, rhs) => Some(Self::And(
                BoolAtom::compile(lhs, nargs, bindings)?,
                BoolAtom::compile(rhs, nargs, bindings)?,
            )),
            OwnedExpr::Or(lhs, rhs) => Some(Self::Or(
                BoolAtom::compile(lhs, nargs, bindings)?,
                BoolAtom::compile(rhs, nargs, bindings)?,
            )),
            OwnedExpr::Xor(lhs, rhs) => Some(Self::Xor(
                BoolAtom::compile(lhs, nargs, bindings)?,
                BoolAtom::compile(rhs, nargs, bindings)?,
            )),
            OwnedExpr::Ite(cond, then_expr, else_expr) => Some(Self::Ite(
                BoolAtom::compile(cond, nargs, bindings)?,
                BoolAtom::compile(then_expr, nargs, bindings)?,
                BoolAtom::compile(else_expr, nargs, bindings)?,
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
        _ if expr.width() == 1 => {
            out.push(expr);
            true
        }
        _ => false,
    }
}

fn try_compile_bit_circuit(expr: &OwnedExpr, nargs: usize, ret_bits: usize) -> Option<BitCircuitPlan> {
    let mut bindings = Vec::new();
    let mut current = expr;
    while let OwnedExpr::Let(_, value, body) = current {
        if value.width() != 1 {
            return None;
        }
        let node = BoolNode::compile(value, nargs, &mut bindings)?;
        bindings.push(node);
        current = body;
    }
    let mut raw_bits = Vec::new();
    if !flatten_concat_bits(current, &mut raw_bits) {
        return None;
    }
    if raw_bits.len() != ret_bits {
        return None;
    }
    let output_bits = raw_bits
        .into_iter()
        .map(|bit| BoolAtom::compile(bit, nargs, &mut bindings))
        .collect::<Option<Vec<_>>>()?;
    Some(BitCircuitPlan {
        bindings,
        output_bits,
        ret_bits,
    })
}

fn compile_plan(expr: &OwnedExpr, arg_bits: &[usize]) -> DefineFunPlan {
    let nargs = arg_bits.len();
    let ret_bits = expr.width();
    if let Some(plan) = try_compile_bit_circuit(expr, nargs, ret_bits) {
        return DefineFunPlan::BitCircuit(plan);
    }
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
            OwnedExpr::Fop0Dyn(fid) => push(
                PlanInstr::Fop0Dyn { fid: *fid },
                expr.width(),
                next_slot,
                slot_bits,
                instrs,
            ),
            OwnedExpr::Fop1Dyn(fid, arg) => {
                let arg = compile_expr(arg, env_slots, next_slot, slot_bits, instrs);
                push(
                    PlanInstr::Fop1Dyn { fid: *fid, arg },
                    expr.width(),
                    next_slot,
                    slot_bits,
                    instrs,
                )
            }
            OwnedExpr::Fop2Dyn(fid, lhs, rhs) => {
                let lhs = compile_expr(lhs, env_slots, next_slot, slot_bits, instrs);
                let rhs = compile_expr(rhs, env_slots, next_slot, slot_bits, instrs);
                push(
                    PlanInstr::Fop2Dyn { fid: *fid, lhs, rhs },
                    expr.width(),
                    next_slot,
                    slot_bits,
                    instrs,
                )
            }
            OwnedExpr::FopDyn(fid, args) => {
                let args = args
                    .iter()
                    .map(|arg| compile_expr(arg, env_slots, next_slot, slot_bits, instrs))
                    .collect();
                push(
                    PlanInstr::FopDyn { fid: *fid, args },
                    expr.width(),
                    next_slot,
                    slot_bits,
                    instrs,
                )
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

pub struct Environ(UnsafeCell<Vec<Vec<DefineFun>>>);

impl Environ {
    pub fn new() -> Self {
        Environ(vec![Vec::new(), Vec::new(), Vec::new()].into())
    }

    pub fn inner(&self) -> &mut Vec<Vec<DefineFun>> {
        unsafe { self.0.get().as_mut().unwrap() }
    }

    pub fn clear(&self) {
        for defs in self.inner().iter_mut() {
            defs.clear();
        }
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
            if self.inner().len() <= args.len() {
                self.inner().resize_with(args.len() + 1, Vec::new);
            }
            let arg_bits = args.iter().map(|(_, bits)| *bits as usize).collect::<Vec<_>>();
            let extended_arg_bits = extended_env
                .iter()
                .map(|(_, bits)| *bits as usize)
                .collect::<Vec<_>>();
            let plan = compile_plan(&expr, &extended_arg_bits);
            info!(
                "DefineFun: {} {} -> {}",
                name,
                args.iter().map(|(n, _)| *n).collect::<Vec<_>>().join(", "),
                summarize_expr(&expr, 160)
            );
            self.inner()[args.len()].push(DefineFun {
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
            .get(nargs)?
            .iter()
            .enumerate()
            .find(|(_, p)| p.name == name)
            .map(|(a, _)| a)
    }
    pub fn apply(&self, id: usize, nargs: usize) -> &OwnedExpr {
        &self.inner()[nargs][id].expr
    }
    pub(crate) fn plan(&self, id: usize, nargs: usize) -> &DefineFunPlan {
        &self.inner()[nargs][id].plan
    }
    pub fn ret_bits(&self, id: usize, nargs: usize) -> usize {
        self.inner()[nargs][id].ret_bits
    }
    pub fn arg_bits(&self, id: usize, nargs: usize) -> &[usize] {
        &self.inner()[nargs][id].arg_bits
    }
    pub fn name(&self, id: usize, nargs: usize) -> &'static str {
        &self.inner()[nargs][id].name
    }
    /// Names of closure-shaped synth-funs that this define-fun's body may
    /// reference (in SyGuS file order). Callers must append the current
    /// value of each one to `args` when invoking `eval_defined`.
    pub fn closure_args(&self, id: usize, nargs: usize) -> &[&'static str] {
        &self.inner()[nargs][id].closure_args
    }
    pub fn closure_arg_bits(&self, id: usize, nargs: usize) -> &[usize] {
        &self.inner()[nargs][id].closure_arg_bits
    }
    pub fn eval_defined(
        &self,
        id: usize,
        nargs: usize,
        args: &[Value],
    ) -> Result<Value, DivideByZero> {
        self.plan(id, nargs).eval(self, args)
    }
}

/// True iff the grammar is just `((<NT> <Sort> ((Constant <Sort>))))` — the
/// LFP-placeholder shape used for closure synth-funs.
fn is_constant_grammar(grammar: &sygus_parser::ast::GrammarDef) -> bool {
    if grammar.grouped_rule_lists.len() != 1 {
        return false;
    }
    let rules = &grammar.grouped_rule_lists[0].terms;
    rules.len() == 1 && matches!(&rules[0], sygus_parser::ast::SyGuSGTerm::Constant(_))
}

unsafe impl Sync for Environ {}

lazy_static::lazy_static!(
    pub static ref ENV: Environ = Environ::new();
);
