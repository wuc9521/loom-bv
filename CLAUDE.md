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

### BitCircuit multi-bit constant handling (fixed)

`flatten_concat_bits` previously rejected multi-bit constant leaves (width > 1),
forcing any define-fun with grouped constant bits onto the slow Generic path.
Fixed via a two-pass approach in `try_compile`:

1. `flatten_concat_bits` tries the strict 1-bit-only path (fast, unchanged hot path)
2. On failure, `flatten_concat_bits_or_consts` accepts multi-bit `OwnedExpr::Const`
   leaves, which are expanded bit-by-bit into `BoolAtom::Const` entries

A bare `OwnedExpr::Const` at the top level (no concat) is rejected — those
all-constant define-funs are cheaper on the Generic path (one instruction).

### BitCircuit hash-consing (the big win)

When multiple output bits share identical boolean sub-expression trees, the old
code compiled each independently — creating duplicate `BoolNode` entries
evaluated redundantly at runtime. Now `try_compile` uses an
`FxHashMap<BoolNode, usize>` dedup map during the output-bit compilation phase.
`BoolAtom::compile_dedup` / `BoolNode::compile_dedup` check the map before
pushing, reusing existing indices for structurally identical nodes.

Effect on String/0001.sl define-funs:
- `int.indexof`: 639,804 → 26,661 bindings (**96% reduction**)
- `str.++`: 135,360 → 61,326 bindings (55%)
- `str.substr`: 132,573 → 35,274 bindings (73%)

Required `Hash + PartialEq + Eq` derives on `BoolNode` and `BoolAtom`.

## What didn't work (don't re-try)

- **Thread-local `Vec<bool>` buffer for BitCircuit eval temps**: Replaced
  `Vec::with_capacity(n)` with a TLS `RefCell<Vec<bool>>` that's cleared and
  reused across calls. No measurable improvement — the allocation isn't the
  bottleneck; the 61K `BoolNode::eval` iterations dominate. RefCell overhead
  may have slightly regressed.

- **Removing `try_lift_native_bv` from delis**: Caused 20% regression on Reg
  benchmarks. The lift detects uniform bit patterns (all bits have the same
  formula shifted by index) and emits a single native BV op (`bvand`, `bvor`).
  For `re.union` this means 1 instruction vs 98 individual bit evaluations.
  The lift is a genuine semantic compression for uniform patterns; removing it
  forces BitCircuit to do O(n) work where O(1) sufficed. Keep in delis.

## Responsibility boundary: delis vs dryadsynth-bv

- **delis** owns problem-size reduction: bisim quotient, let-binding structure,
  `try_lift_native_bv` for uniform patterns, `BoolExpr::compact` grouping
  consecutive constants.
- **dryadsynth-bv** owns efficient evaluation of whatever IR arrives:
  BitCircuit detection (including multi-bit constants), hash-consing dedup,
  backward relevance, eval caching, search strategies.
- The SyGuS BV file is the contract between them. Neither side assumes
  internal details of the other's implementation.

## Regression test suite

Run all on the remote server (`sync-rust-to-remote` then SSH). Baselines
from clean builds of both repos at their respective main HEADs.

| Benchmark | Baseline | After hash-cons | Notes |
|---|---|---|---|
| `Reg/0003.sl` | 5.33s | 3.86s | 1.4× faster |
| `Reg/0019.sl` | 3.05s | 2.16s | 1.4× faster |
| `String/0031.sl` | 6.70s | 2.75s | 2.4× faster |
| `CTL/0002.sl` | 0.20s | 0.19s | unchanged |
| `String/0001.sl` | >120s | >120s (size 8 @ 42s) | blocked on search space, not eval |

All produce correct solutions (same output as baseline). CTL/0002 is fast
because its search space is tiny (solved at size 3).

## Backward Relevance (exact/relevance/)

Demand-driven dataflow analysis: starts from constrained output bits, propagates backward through grammar operators to determine which sub-NT bits are actually needed. Projects dedup keys to only relevant bits, increasing dedup hit rate.

Seeded from `BitSpec::demanded_bits()` — the union of all examples' known_bits.

## Multi-Example Evaluation (exact/search.rs)

The `Candidate` struct holds `Vec<Value>` (one per example). For K examples, each grammar operator is evaluated K times. Dedup keys are flat-concatenated projections of all K values. For K=1 (nullary), this degenerates to the old single-value behavior.

## Value Representation (enumerate/value.rs)

- `Value::Small { bits, raw: u64 }` — widths <= 64 bits
- `Value::Big { bits, raw: Arc<BigUint> }` — wider values, heap-allocated

Every BV operation on Big values allocates a new BigUint. This is the irreducible per-instruction cost in the Generic eval path. Arc enables cheap cloning (refcount bump) but each new result is a fresh allocation.
