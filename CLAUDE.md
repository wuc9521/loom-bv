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

| Benchmark | Hash-cons baseline | After word-parallel | Speedup |
|---|---|---|---|
| `Reg/0003.sl` | 3.86s | 2.19s | 1.8x |
| `Reg/0019.sl` | 2.16s | 1.42s | 1.5x |
| `String/0031.sl` | 2.75s | 1.38s | 2.0x |
| `CTL/0002.sl` | ~5.5s | ~5.3s | unchanged (uses delis closure solver) |
| `String/0001.sl` size 8 | 42s | 9.7s | **4.3x** |
| `String/0001.sl` size 9 | unreachable | 34.3s | new |

Note: CTL/0002 baseline of 0.19s in the earlier table was from cvc5 winning the
solver race. With in-process dryadsynth-bv only, it takes ~5.5s (pre-existing,
unrelated to eval_batch).

## Cone-of-Influence Pruning (not yet enabled)

**Idea**: The backward relevance analysis computes which output bits of the start
NT are actually demanded by the spec (`relevant_bits[start]`). Many circuits have
large sub-DAGs that feed only non-demanded output bits. Pruning removes those gates:

1. Mark all gates in the transitive fanin of demanded output bits
2. Remove unmarked gates, remap Temp indices
3. Set non-demanded output bits to `BoolAtom::Const(false)` (zeroed)

The pruned circuit produces the correct value at all demanded positions and zeros
elsewhere. This is safe for `spec.matches` (only checks demanded bits) and for
projected dedup (only hashes demanded bits).

Infrastructure is implemented (`BitCircuitPlan::pruned` in `parse/deffun.rs`):
- Backward reachability from demanded output bits
- Gate remapping with index compaction
- input_slots recomputation for the reduced circuit
- Bail-out when reduction < 10% (not worth the overhead)

**Difficulties encountered (not yet resolved)**:

1. **CEGIS interaction**: delis wraps the dryadsynth-bv search in a CEGIS loop
   that progressively adds examples. Each round creates a fresh `Searcher` with
   a different `demanded_bits` set. The pruned plan must be recomputed per round
   (currently done). However, a candidate found in round N with fewer demanded
   bits might not satisfy the expanded demands in round N+1 — this is handled
   correctly by CEGIS (it re-verifies and adds counterexamples). The issue is
   more subtle.

2. **Incorrect results on String/0031 despite passing validation**: The pruned
   plan passes a 4-pattern spot check (zeros, all-ones, 0xAAAA, 0x5555) comparing
   demanded-position bits against the full plan — no mismatches detected. Yet the
   search fails to find the solution (searches to size 13+ without matching, while
   the unpruned version solves at ~size 7). This implies the pruning corrupts
   results on specific input patterns not covered by the spot check.

3. **Suspected root cause**: The `BoolAtom::word` function returns 0 for
   `InputBit` references where `arg * stride + bit >= input_words.len()`. This
   handles plans compiled with extra argument slots (e.g., closure args) that
   aren't passed at eval time. However, if a gate in the demanded fanin cone
   depends on such an out-of-bounds InputBit, the pruned circuit silently
   computes wrong values (reads 0 instead of the correct bit). The full plan
   has the same issue but it doesn't manifest because the full plan's output
   at demanded positions doesn't depend on those bits (the relevance analysis
   already excluded them). The **pruned** plan's marking step may incorrectly
   include gates that transitively reference out-of-bounds inputs through paths
   that are actually dead in practice but structurally reachable.

4. **Required next step**: Build a proper fuzz-testing harness that generates
   random wide-bitvector inputs (matching actual candidate widths from the search)
   and compares pruned vs full plan outputs at all demanded positions. The current
   spot-check with 64-bit patterns is insufficient for 345-bit values. Once the
   divergence is caught, the fix likely involves filtering the fanin marking to
   exclude gates whose InputBit references are provably out-of-bounds for the
   runtime arg count.
