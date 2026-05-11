use std::cell::UnsafeCell;

use derive_more::DebugCustom;
use sygus_parser::ast::SyGuSFile;

use crate::{
    enumerate::{
        expr::{DivideByZero, OwnedExpr},
        op,
        value::Value,
    },
    info,
};

use super::{new_custom_error_span, Error, ProblemView};

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
}

#[derive(Clone, Debug)]
enum DefineFunPlan {
    Generic {
        root: usize,
        slot_count: usize,
        instrs: Vec<PlanInstr>,
    },
    BitCircuit(BitCircuitPlan),
}

#[derive(Clone, Debug)]
struct BitCircuitPlan {
    bindings: Vec<BoolBinding>,
    output_bits: Vec<BoolAtom>,
    ret_bits: usize,
}

#[derive(Clone, Debug)]
struct BoolBinding {
    expr: BoolNode,
}

#[derive(Clone, Debug)]
enum BoolNode {
    Atom(BoolAtom),
    Not(BoolAtom),
    And(BoolAtom, BoolAtom),
    Or(BoolAtom, BoolAtom),
    Xor(BoolAtom, BoolAtom),
    Ite(BoolAtom, BoolAtom, BoolAtom),
}

#[derive(Clone, Debug)]
enum BoolAtom {
    Const(bool),
    InputBit { arg: usize, bit: usize },
    Temp(usize),
}

#[derive(Clone, Debug)]
enum PlanInstr {
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
                instrs,
            } => {
                let mut slots = Vec::with_capacity(*slot_count);
                slots.extend(args.iter().cloned());
                for instr in instrs {
                    let value = match instr {
                        PlanInstr::Const(value) => value.clone(),
                        PlanInstr::Concat { lhs, rhs } => {
                            value_concat(slots[*lhs].clone(), slots[*rhs].clone())
                        }
                        PlanInstr::Extract { src, hi, lo } => {
                            value_extract(slots[*src].clone(), *hi, *lo)
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
            let value = eval_bool_node(&binding.expr, args, &temps);
            temps.push(value);
        }
        let mut words = vec![0u64; self.ret_bits.div_ceil(64)];
        for (bit_idx, atom) in self.output_bits.iter().enumerate() {
            if eval_bool_atom(atom, args, &temps) {
                words[bit_idx / 64] |= 1u64 << (bit_idx % 64);
            }
        }
        Ok(value_from_words(words, self.ret_bits))
    }
}

fn eval_bool_node(node: &BoolNode, args: &[Value], temps: &[bool]) -> bool {
    match node {
        BoolNode::Atom(atom) => eval_bool_atom(atom, args, temps),
        BoolNode::Not(atom) => !eval_bool_atom(atom, args, temps),
        BoolNode::And(lhs, rhs) => {
            eval_bool_atom(lhs, args, temps) & eval_bool_atom(rhs, args, temps)
        }
        BoolNode::Or(lhs, rhs) => {
            eval_bool_atom(lhs, args, temps) | eval_bool_atom(rhs, args, temps)
        }
        BoolNode::Xor(lhs, rhs) => {
            eval_bool_atom(lhs, args, temps) ^ eval_bool_atom(rhs, args, temps)
        }
        BoolNode::Ite(cond, then_atom, else_atom) => {
            if eval_bool_atom(cond, args, temps) {
                eval_bool_atom(else_atom, args, temps)
            } else {
                eval_bool_atom(then_atom, args, temps)
            }
        }
    }
}

fn eval_bool_atom(atom: &BoolAtom, args: &[Value], temps: &[bool]) -> bool {
    match atom {
        BoolAtom::Const(value) => *value,
        BoolAtom::InputBit { arg, bit } => args[*arg].bit(*bit),
        BoolAtom::Temp(idx) => temps[*idx],
    }
}

fn value_extract(value: Value, hi: u64, lo: u64) -> Value {
    let width = (hi - lo + 1) as usize;
    if width == 1 {
        return Value::from_u64(value.bit(lo as usize) as u64, 1);
    }
    if value.bits() <= 64 {
        return Value::from_u64(value.as_u64_lossy() >> lo, width);
    }
    let shifted = value.to_biguint() >> (lo as usize);
    let mask = (num_bigint::BigUint::from(1u8) << width) - num_bigint::BigUint::from(1u8);
    Value::from_biguint(shifted & mask, width)
}

fn value_concat(lhs: Value, rhs: Value) -> Value {
    let rhs_bits = rhs.bits();
    let total_bits = lhs.bits() + rhs_bits;
    let raw = (lhs.to_biguint() << rhs_bits) | rhs.to_biguint();
    Value::from_biguint(raw, total_bits)
}

fn owned_expr_width(expr: &OwnedExpr) -> usize {
    match expr {
        OwnedExpr::Concat(a, b) => owned_expr_width(a) + owned_expr_width(b),
        OwnedExpr::Extract(_, hi, lo) => (hi - lo + 1) as usize,
        OwnedExpr::Fop0Dyn(id) => ENV.ret_bits(*id, 0),
        OwnedExpr::FopDyn(id, args) => ENV.ret_bits(*id, args.len()),
        OwnedExpr::Const(v) => v.bits(),
        OwnedExpr::Var(_) => 64,
        OwnedExpr::Let(_, _, body) => owned_expr_width(body),
        OwnedExpr::Not(a)
        | OwnedExpr::Neg(a)
        | OwnedExpr::Fop1Dyn(_, a) => owned_expr_width(a),
        OwnedExpr::Add(a, _)
        | OwnedExpr::Xor(a, _)
        | OwnedExpr::And(a, _)
        | OwnedExpr::Or(a, _)
        | OwnedExpr::Mul(a, _)
        | OwnedExpr::Sub(a, _)
        | OwnedExpr::Fop2Dyn(_, a, _)
        | OwnedExpr::LShr(a, _)
        | OwnedExpr::AShr(a, _)
        | OwnedExpr::Shl(a, _)
        | OwnedExpr::UDiv(a, _)
        | OwnedExpr::URem(a, _)
        | OwnedExpr::SDiv(a, _)
        | OwnedExpr::SRem(a, _) => owned_expr_width(a),
        OwnedExpr::Ite(_, a, _) => owned_expr_width(a),
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

fn compile_bool_atom(expr: &OwnedExpr, nargs: usize) -> Option<BoolAtom> {
    match expr {
        OwnedExpr::Const(value) if value.bits() == 1 => Some(BoolAtom::Const(!value.is_zero())),
        OwnedExpr::Var(idx) if *idx < nargs => None,
        OwnedExpr::Var(idx) => Some(BoolAtom::Temp(idx.checked_sub(nargs)?)),
        OwnedExpr::Extract(src, hi, lo) if hi == lo => match src.as_ref() {
            OwnedExpr::Var(idx) if *idx < nargs => Some(BoolAtom::InputBit {
                arg: *idx,
                bit: *lo as usize,
            }),
            OwnedExpr::Var(idx) => Some(BoolAtom::Temp(idx.checked_sub(nargs)?)),
            _ => None,
        },
        _ => None,
    }
}

fn compile_bool_node(expr: &OwnedExpr, nargs: usize) -> Option<BoolNode> {
    match expr {
        OwnedExpr::Const(value) if value.bits() == 1 => {
            Some(BoolNode::Atom(BoolAtom::Const(!value.is_zero())))
        }
        OwnedExpr::Var(_) | OwnedExpr::Extract(_, _, _) => {
            Some(BoolNode::Atom(compile_bool_atom(expr, nargs)?))
        }
        OwnedExpr::Not(inner) => Some(BoolNode::Not(compile_bool_atom(inner, nargs)?)),
        OwnedExpr::And(lhs, rhs) => Some(BoolNode::And(
            compile_bool_atom(lhs, nargs)?,
            compile_bool_atom(rhs, nargs)?,
        )),
        OwnedExpr::Or(lhs, rhs) => Some(BoolNode::Or(
            compile_bool_atom(lhs, nargs)?,
            compile_bool_atom(rhs, nargs)?,
        )),
        OwnedExpr::Xor(lhs, rhs) => Some(BoolNode::Xor(
            compile_bool_atom(lhs, nargs)?,
            compile_bool_atom(rhs, nargs)?,
        )),
        OwnedExpr::Ite(cond, then_expr, else_expr) => Some(BoolNode::Ite(
            compile_bool_atom(cond, nargs)?,
            compile_bool_atom(then_expr, nargs)?,
            compile_bool_atom(else_expr, nargs)?,
        )),
        _ => None,
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
        _ if owned_expr_width(expr) == 1 => {
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
        if owned_expr_width(value) != 1 {
            return None;
        }
        let node = compile_bool_node(value, nargs)?;
        bindings.push(BoolBinding { expr: node });
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
        .map(|bit| compile_bool_atom(bit, nargs))
        .collect::<Option<Vec<_>>>()?;
    Some(BitCircuitPlan {
        bindings,
        output_bits,
        ret_bits,
    })
}

fn compile_plan(expr: &OwnedExpr, nargs: usize) -> DefineFunPlan {
    let ret_bits = owned_expr_width(expr);
    if let Some(plan) = try_compile_bit_circuit(expr, nargs, ret_bits) {
        return DefineFunPlan::BitCircuit(plan);
    }
    fn compile_expr(
        expr: &OwnedExpr,
        env_slots: &mut Vec<usize>,
        next_slot: &mut usize,
        instrs: &mut Vec<PlanInstr>,
    ) -> usize {
        let push = |instr: PlanInstr, next_slot: &mut usize, instrs: &mut Vec<PlanInstr>| {
            let slot = *next_slot;
            *next_slot += 1;
            instrs.push(instr);
            slot
        };
        match expr {
            OwnedExpr::Var(idx) => env_slots[*idx],
            OwnedExpr::Const(value) => push(PlanInstr::Const(value.clone()), next_slot, instrs),
            OwnedExpr::Concat(lhs, rhs) => {
                let lhs = compile_expr(lhs, env_slots, next_slot, instrs);
                let rhs = compile_expr(rhs, env_slots, next_slot, instrs);
                push(PlanInstr::Concat { lhs, rhs }, next_slot, instrs)
            }
            OwnedExpr::Extract(src, hi, lo) => {
                let src = compile_expr(src, env_slots, next_slot, instrs);
                push(PlanInstr::Extract { src, hi: *hi, lo: *lo }, next_slot, instrs)
            }
            OwnedExpr::Not(src) => {
                let src = compile_expr(src, env_slots, next_slot, instrs);
                push(PlanInstr::Not { src }, next_slot, instrs)
            }
            OwnedExpr::Neg(src) => {
                let src = compile_expr(src, env_slots, next_slot, instrs);
                push(PlanInstr::Neg { src }, next_slot, instrs)
            }
            OwnedExpr::Add(lhs, rhs) => {
                let lhs = compile_expr(lhs, env_slots, next_slot, instrs);
                let rhs = compile_expr(rhs, env_slots, next_slot, instrs);
                push(PlanInstr::Add { lhs, rhs }, next_slot, instrs)
            }
            OwnedExpr::Xor(lhs, rhs) => {
                let lhs = compile_expr(lhs, env_slots, next_slot, instrs);
                let rhs = compile_expr(rhs, env_slots, next_slot, instrs);
                push(PlanInstr::Xor { lhs, rhs }, next_slot, instrs)
            }
            OwnedExpr::And(lhs, rhs) => {
                let lhs = compile_expr(lhs, env_slots, next_slot, instrs);
                let rhs = compile_expr(rhs, env_slots, next_slot, instrs);
                push(PlanInstr::And { lhs, rhs }, next_slot, instrs)
            }
            OwnedExpr::Or(lhs, rhs) => {
                let lhs = compile_expr(lhs, env_slots, next_slot, instrs);
                let rhs = compile_expr(rhs, env_slots, next_slot, instrs);
                push(PlanInstr::Or { lhs, rhs }, next_slot, instrs)
            }
            OwnedExpr::Mul(lhs, rhs) => {
                let lhs = compile_expr(lhs, env_slots, next_slot, instrs);
                let rhs = compile_expr(rhs, env_slots, next_slot, instrs);
                push(PlanInstr::Mul { lhs, rhs }, next_slot, instrs)
            }
            OwnedExpr::Sub(lhs, rhs) => {
                let lhs = compile_expr(lhs, env_slots, next_slot, instrs);
                let rhs = compile_expr(rhs, env_slots, next_slot, instrs);
                push(PlanInstr::Sub { lhs, rhs }, next_slot, instrs)
            }
            OwnedExpr::LShr(lhs, rhs) => {
                let lhs = compile_expr(lhs, env_slots, next_slot, instrs);
                let rhs = compile_expr(rhs, env_slots, next_slot, instrs);
                push(PlanInstr::LShr { lhs, rhs }, next_slot, instrs)
            }
            OwnedExpr::AShr(lhs, rhs) => {
                let lhs = compile_expr(lhs, env_slots, next_slot, instrs);
                let rhs = compile_expr(rhs, env_slots, next_slot, instrs);
                push(PlanInstr::AShr { lhs, rhs }, next_slot, instrs)
            }
            OwnedExpr::Shl(lhs, rhs) => {
                let lhs = compile_expr(lhs, env_slots, next_slot, instrs);
                let rhs = compile_expr(rhs, env_slots, next_slot, instrs);
                push(PlanInstr::Shl { lhs, rhs }, next_slot, instrs)
            }
            OwnedExpr::UDiv(lhs, rhs) => {
                let lhs = compile_expr(lhs, env_slots, next_slot, instrs);
                let rhs = compile_expr(rhs, env_slots, next_slot, instrs);
                push(PlanInstr::UDiv { lhs, rhs }, next_slot, instrs)
            }
            OwnedExpr::URem(lhs, rhs) => {
                let lhs = compile_expr(lhs, env_slots, next_slot, instrs);
                let rhs = compile_expr(rhs, env_slots, next_slot, instrs);
                push(PlanInstr::URem { lhs, rhs }, next_slot, instrs)
            }
            OwnedExpr::SDiv(lhs, rhs) => {
                let lhs = compile_expr(lhs, env_slots, next_slot, instrs);
                let rhs = compile_expr(rhs, env_slots, next_slot, instrs);
                push(PlanInstr::SDiv { lhs, rhs }, next_slot, instrs)
            }
            OwnedExpr::SRem(lhs, rhs) => {
                let lhs = compile_expr(lhs, env_slots, next_slot, instrs);
                let rhs = compile_expr(rhs, env_slots, next_slot, instrs);
                push(PlanInstr::SRem { lhs, rhs }, next_slot, instrs)
            }
            OwnedExpr::Ite(cond, then_expr, else_expr) => {
                let cond = compile_expr(cond, env_slots, next_slot, instrs);
                let then_slot = compile_expr(then_expr, env_slots, next_slot, instrs);
                let else_slot = compile_expr(else_expr, env_slots, next_slot, instrs);
                push(PlanInstr::Ite { cond, then_slot, else_slot }, next_slot, instrs)
            }
            OwnedExpr::Let(_, value, body) => {
                let value_slot = compile_expr(value, env_slots, next_slot, instrs);
                env_slots.push(value_slot);
                let body_slot = compile_expr(body, env_slots, next_slot, instrs);
                env_slots.pop();
                body_slot
            }
            OwnedExpr::Fop0Dyn(fid) => push(PlanInstr::Fop0Dyn { fid: *fid }, next_slot, instrs),
            OwnedExpr::Fop1Dyn(fid, arg) => {
                let arg = compile_expr(arg, env_slots, next_slot, instrs);
                push(PlanInstr::Fop1Dyn { fid: *fid, arg }, next_slot, instrs)
            }
            OwnedExpr::Fop2Dyn(fid, lhs, rhs) => {
                let lhs = compile_expr(lhs, env_slots, next_slot, instrs);
                let rhs = compile_expr(rhs, env_slots, next_slot, instrs);
                push(PlanInstr::Fop2Dyn { fid: *fid, lhs, rhs }, next_slot, instrs)
            }
            OwnedExpr::FopDyn(fid, args) => {
                let args = args
                    .iter()
                    .map(|arg| compile_expr(arg, env_slots, next_slot, instrs))
                    .collect();
                push(PlanInstr::FopDyn { fid: *fid, args }, next_slot, instrs)
            }
        }
    }

    let mut instrs = Vec::new();
    let mut env_slots = (0..nargs).collect::<Vec<_>>();
    let mut next_slot = nargs;
    let root = compile_expr(expr, &mut env_slots, &mut next_slot, &mut instrs);
    DefineFunPlan::Generic {
        root,
        slot_count: next_slot,
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
            let expr = OwnedExpr::from_term(def.body, args.as_slice())?;
            info!(
                "DefineFun: {} {} -> {}",
                name,
                args.iter().map(|(n, _)| *n).collect::<Vec<_>>().join(", "),
                summarize_expr(&expr, 160)
            );
            if self.inner().len() <= args.len() {
                self.inner().resize_with(args.len() + 1, Vec::new);
            }
            self.inner()[args.len()].push(DefineFun {
                name,
                args: args.iter().map(|(name, _)| *name).collect(),
                arg_bits: args.iter().map(|(_, bits)| *bits as usize).collect(),
                ret_bits,
                plan: compile_plan(&expr, args.len()),
                expr,
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
    fn plan(&self, id: usize, nargs: usize) -> &DefineFunPlan {
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
    pub fn eval_defined(
        &self,
        id: usize,
        nargs: usize,
        args: &[Value],
    ) -> Result<Value, DivideByZero> {
        self.plan(id, nargs).eval(self, args)
    }
}

unsafe impl Sync for Environ {}

lazy_static::lazy_static!(
    pub static ref ENV: Environ = Environ::new();
);
