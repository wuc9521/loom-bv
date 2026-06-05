# CLAUDE.md

## Project Overview

dryadsynth-bv is a bitvector SyGuS (Syntax-Guided Synthesis) solver. It enumerates candidate terms bottom-up over a grammar, evaluating each against a specification to find a satisfying program.

## Architecture

The solver dispatches through a cascade of backends:

1. **LFP (lfp.rs)** — Detects recursive/closure-constraint patterns, runs Kleene fixpoint iteration
2. **BitSpec (bitspec.rs)** — Unified bit-constraint solver handling nullary, non-nullary (PBE-shaped), and LFP problems
3. **PBE / RefImpl** — Fallback CEGIS paths for standard PBE or reference-implementation constraints

The core search engine (`exact/search.rs`) is a bottom-up enumerator with multi-example evaluation and projected dedup.

## Key Performance-Critical Paths

### DefineFunPlan evaluation (parse/deffun.rs)

Each define-fun is compiled to either:
- **BitCircuitPlan** — Fast path: pure boolean evaluation (Vec<bool> temporaries). Only fires when the expression is a concat of 1-bit leaves with 1-bit let-bindings.
- **Generic plan** — Slow path: stack-machine interpreter over Vec<Value> slots. Every instruction allocates a new Value (Arc<BigUint> for wide BVs).

The Generic path dominates runtime for String/PROSE benchmarks where define-funs are 100K+ character bit-blasted expressions.

### BitCircuitPlan Detection Gap

The delis frontend applies optimizations before emitting SyGuS:

1. **BoolExpr::compact** (emit.rs) groups consecutive constant bits into multi-bit literals (e.g., `#b00101` instead of five 1-bit concats). This reduces Generic plan instruction count but breaks BitCircuit detection.

2. **try_lift_native_bv** (optim.rs) detects uniform/segmented bit patterns and replaces them with native BV ops (bvand, bvor, multi-bit extracts). This is a net win for the Generic path but prevents BitCircuit compilation entirely.

Both optimizations introduce multi-bit leaves into the concat tree, causing `flatten_concat_bits` to reject the expression. The define-funs are structurally boolean circuits (concat of ite-over-input-bit-extracts) but the multi-bit grouping hides this.

**Implication**: To enable BitCircuit compilation for the large String define-funs, either:
- dryadsynth-bv's `flatten_concat_bits` must handle multi-bit constants/extracts by splitting them into individual bits
- Or delis must emit a "BitCircuit-friendly" form (no multi-bit grouping) when targeting the in-process backend

## Backward Relevance (exact/relevance/)

Demand-driven dataflow analysis: starts from constrained output bits, propagates backward through grammar operators to determine which sub-NT bits are actually needed. Projects dedup keys to only relevant bits, increasing dedup hit rate.

Seeded from `BitSpec::demanded_bits()` — the union of all examples' known_bits.

## Multi-Example Evaluation (exact/search.rs)

The `Candidate` struct holds `Vec<Value>` (one per example). For K examples, each grammar operator is evaluated K times. Dedup keys are flat-concatenated projections of all K values. For K=1 (nullary), this degenerates to the old single-value behavior.

## Value Representation (enumerate/value.rs)

- `Value::Small { bits, raw: u64 }` — widths <= 64 bits
- `Value::Big { bits, raw: Arc<BigUint> }` — wider values, heap-allocated

Every BV operation on Big values allocates a new BigUint. This is the irreducible per-instruction cost in the Generic eval path. Arc enables cheap cloning (refcount bump) but each new result is a fresh allocation.
