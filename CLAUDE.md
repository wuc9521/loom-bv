# CLAUDE.md

## Project Overview

dryadsynth-bv is a bitvector SyGuS (Syntax-Guided Synthesis) solver. It enumerates candidate terms bottom-up over a grammar, evaluating each against a specification to find a satisfying program.

## Architecture

The solver dispatches through a cascade of backends:

1. **LFP (lfp.rs)** — Detects recursive/closure-constraint patterns, runs Kleene fixpoint iteration
2. **BitSpec (bitspec.rs)** — Unified bit-constraint solver handling nullary, non-nullary (PBE-shaped), and LFP problems
3. **PBE / RefImpl** — Fallback CEGIS paths for standard PBE or reference-implementation constraints

The core search engine (`exact/search.rs`) is a bottom-up enumerator with multi-example evaluation and projected dedup.

### Environ (parse/deffun.rs)

The `Environ` stores all parsed `DefineFun` entries in a flat `Vec<DefineFun>`,
indexed by a global `fid`. Each `DefineFun` knows its own arity via `args.len()`.
`lookup(name, nargs)` scans the flat vec to find a function by name and arity,
returning its global fid. All other accessors take just `id: usize`.

This replaced an earlier 2D `Vec<Vec<DefineFun>>` indexed by `[nargs][fid]`,
which caused a key-collision bug in COI pruning (a unary fid=0 and binary fid=0
were different functions sharing the same numeric id).

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

- **COI pruning for eval_batch speedup (binary/unary batch path only)**: The
  word-parallel batch path for binary/unary rules is already fast (< 1% of
  runtime on String/0001). Pruning those circuits showed zero improvement.
  The real bottleneck is the **nary scalar eval path** (str.substr, int.indexof)
  which processes tuples one-by-one. COI only helps when applied there.

## Responsibility boundary: delis vs dryadsynth-bv

- **delis** owns problem-size reduction: bisim quotient, let-binding structure,
  `try_lift_native_bv` for uniform patterns, `BoolExpr::compact` grouping
  consecutive constants.
- **dryadsynth-bv** owns efficient evaluation of whatever IR arrives:
  BitCircuit detection (including multi-bit constants), hash-consing dedup,
  backward relevance, COI pruning, eval caching, search strategies.
- The SyGuS BV file is the contract between them. Neither side assumes
  internal details of the other's implementation.

## Regression test suite

Run all on the remote server (`sync-rust-to-remote` then SSH). Baselines
from clean builds of both repos at their respective main HEADs.

| Benchmark | Baseline | After hash-cons | After word-parallel | After COI |
|---|---|---|---|---|
| `Reg/0003.sl` | 5.33s | 3.86s | 2.19s | ~1.2s |
| `Reg/0019.sl` | 3.05s | 2.16s | 1.42s | ~0.75s |
| `String/0031.sl` | 6.70s | 2.75s | 1.38s | ~1.3s |
| `CTL/0002.sl` | 0.20s | 0.19s | ~5.3s* | ~5.3s* |
| `String/0001.sl` size 8 | >120s | 42s | 9.7s | **6.7s** |
| `String/0001.sl` size 9 | — | — | 34.3s | **23.5s** |

*CTL/0002 at 0.19s is from cvc5 winning the solver race. In-process dryadsynth-bv
alone takes ~5.3s (tiny search space, unrelated to eval optimizations).

COI gives **1.46x** speedup on String/0001 (eval-bound). On small benchmarks
(Reg, String/0031) the speedup is negligible because those solve quickly and
the COI overhead (~1ms relevance + pruned plan construction) offsets the savings.

## Backward Relevance (exact/relevance/)

Demand-driven dataflow analysis: starts from constrained output bits, propagates backward through grammar operators to determine which sub-NT bits are actually needed. Projects dedup keys to only relevant bits, increasing dedup hit rate.

Seeded from `BitSpec::demanded_bits()` — the union of all examples' known_bits.

## Cone-of-Influence Pruning (enabled)

Uses the backward relevance analysis to physically prune BitCircuitPlans:

1. For each (nt_idx, fid) pair, call `BitCircuitPlan::pruned(relevant_bits[nt_idx])`
2. The pruned plan removes gates not in the transitive fanin of demanded output bits
3. Pruned plans are stored in `Rc<BitCircuitPlan>` in `pruned_plans` HashMap
4. Used in both the batch eval path (binary/unary) and the nary scalar eval path

The nary scalar path (`eval_nary_with_plan`) is where the benefit is realized:
str.substr goes from 35K → 12K gates per eval, int.indexof from 27K → 9K.
On String/0001 this accounts for the 1.46x speedup at size 8-9.

**Key invariant**: pruned plans are keyed on `(nt_idx, fid)` where `fid` is
globally unique (flat Environ). The earlier 2D Environ caused a key-collision
bug where a unary fid=0 and binary fid=0 shared the same pruned plan entry.

**Correctness**: `BitCircuitPlan::pruned()` is structurally correct (backward
marking + index compaction). Fuzz tests in `parse/deffun.rs::tests` verify
pruned vs full eval on random inputs for various circuit topologies.

## Multi-Example Evaluation (exact/search.rs)

The `Candidate` struct holds `Vec<Value>` (one per example). For K examples, each grammar operator is evaluated K times. Dedup keys are flat-concatenated projections of all K values. For K=1 (nullary), this degenerates to the old single-value behavior.

## Value Representation (enumerate/value.rs)

- `Value::Small { bits, raw: u64 }` — widths <= 64 bits
- `Value::Big { bits, raw: Arc<BigUint> }` — wider values, heap-allocated

Every BV operation on Big values allocates a new BigUint. This is the irreducible per-instruction cost in the Generic eval path. Arc enables cheap cloning (refcount bump) but each new result is a fresh allocation.

## Word-Parallel BitCircuit Evaluation (eval_batch)

Replaces scalar `Vec<bool>` simulation with `Vec<u64>` word-parallel simulation.
Each `u64` carries 64 independent candidates' wire values through the same gate.
One circuit pass evaluates 64 candidates simultaneously — same instruction count,
64x throughput on the gate evaluation itself.

Implementation (`BitCircuitPlan::eval_batch` in `parse/deffun.rs`):
1. **Sparse input transpose**: Only `InputBit` positions listed in `input_slots`
   (precomputed at compile time) are transposed. Each input wire becomes one `u64`
   with bit `k` = candidate `k`'s value at that wire.
2. **Gate simulation**: `BoolNode::eval_word` performs `&`/`|`/`^`/`!` on `u64` words.
3. **Output transpose**: Extract per-candidate results from the `u64` output words.
4. **Thread-local buffers**: `input_words` and `temps` are TLS `Vec<u64>` reused
   across calls (clear + resize, no reallocation).

The search loop (`exact/search.rs`) batches Binary and Unary rule evaluations:
collect up to 64 (lhs, rhs) pairs, call `eval_batch` once per example, then
process results sequentially through `try_push_new`. Falls back to scalar eval
when the plan is Generic, has closure args, or < 256 bindings.

## String/0001 Performance Profile

At size 8 (CEGIS round 3, 2 examples, 9 constraints):
- 6812 candidates at nt[0] (String, 1455 bits)
- Dominant cost: nary scalar eval (str.substr 35K gates, int.indexof 27K gates)
- Binary batch eval (str.++ 61K gates) is fast due to word-parallel (< 5% of time)
- The search is combinatorially bound: candidate count doubles per size level
- COI reduces nary eval cost by ~60%, giving 1.46x overall speedup

The problem remains unsolved within 60s — would need size ~10-11 to find the
answer. Further progress requires reducing the number of candidates explored
(smarter dedup, conflict learning, or grammar restriction), not faster eval.
