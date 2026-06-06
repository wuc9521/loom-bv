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

Flat `Vec<DefineFun>` indexed by a global `fid`. Each `DefineFun` knows its
own arity via `args.len()`. `lookup(name, nargs)` scans to find a function by
name and arity, returning its global fid. All accessors take just `id: usize`.

### ExactRule (exact/types.rs)

```rust
pub enum ExactRule {
    Alias(usize),
    Leaf(OwnedExpr),
    Op { fid: usize, child_nts: Vec<usize> },
    GenericTemplate { template, child_nts, base_size },
}
```

A single `Op` variant handles all arities. The search loop uses one unified
code path with `for_each_size_split` + `for_each_candidate_tuple` for the
Cartesian product, and word-parallel `eval_batch` for circuits > 256 bindings.

## Key Performance-Critical Paths

### DefineFunPlan evaluation (parse/deffun.rs)

Each define-fun is compiled to either:
- **BitCircuitPlan** — Fast path: boolean gate DAG, evaluated word-parallel (64 candidates/pass)
- **Generic plan** — Slow path: stack-machine interpreter, one Value allocation per instruction

### BitCircuit hash-consing

Dedup map during compilation. Effect on String/0001.sl:
- `int.indexof`: 639K → 27K bindings (96% reduction)
- `str.++`: 135K → 61K bindings (55%)
- `str.substr`: 133K → 35K bindings (73%)

### Word-Parallel Evaluation (eval_batch)

`Vec<u64>` simulation where each u64 carries 64 candidates through the same
gate. The search loop batches all `Op` rule evaluations (any arity) into groups
of 64, calling `eval_batch` once per example per batch.

### COI Pruning

Backward relevance analysis determines demanded bits per NT. `BitCircuitPlan::pruned()`
removes gates not in the transitive fanin. Pruned plans stored in `Rc<BitCircuitPlan>`
keyed on `(nt_idx, fid)`. Reduces gate count by 33-67% on String benchmarks.

## Regression test suite

Run on the remote server (`sync-rust-to-remote` then SSH):
```bash
ssh aliyun-gpu-server-1-wct-container
source ~/.cargo/env
cd Codes/Rust/delis
cargo build --release
```

### Benchmarks

| Benchmark | What it tests |
|---|---|
| `String/0031.sl` | Fast-solving, correctness check |
| `Reg/0003.sl` | Eval-heavy regex benchmark |
| `Reg/0019.sl` | Eval-heavy regex benchmark |
| `CTL/0002.sl` | Tiny search space, sanity check |
| `String/0001.sl` | Stress test: search-space-bound, eval_batch-heavy |

### Timing commands
```bash
# Correctness (all should produce output):
./target/release/delis --min benchmark/String/0031.sl
./target/release/delis --min benchmark/Reg/0003.sl

# Performance (compare --min vs --min=false for COI impact):
for f in benchmark/String/0031.sl benchmark/Reg/0003.sl benchmark/Reg/0019.sl; do
  printf "%s: " "$f"
  start=$(date +%s%N)
  ./target/release/delis --min "$f" >/dev/null
  end=$(date +%s%N)
  echo "$(( (end - start) / 1000000 )) ms"
done

# String/0001 search depth (shows per-size progress):
timeout 60 ./target/release/delis --min -v -v benchmark/String/0001.sl 2>&1 | grep "search size"
```

### Current baselines (remote server)

| Benchmark | Time |
|---|---|
| `String/0031.sl` | ~1.3s |
| `Reg/0003.sl` | ~1.2s |
| `Reg/0019.sl` | ~0.75s |
| `String/0001.sl` size 8 | ~0.65s |
| `String/0001.sl` size 9 | ~2.4s |
| `String/0001.sl` size 10 | ~8s |

## What didn't work (don't re-try)

- **TLS Vec<bool> buffer for BitCircuit temps**: No improvement. Gate iteration
  dominates, not allocation.

- **Removing `try_lift_native_bv` from delis**: 20% regression on Reg. The lift
  compresses uniform patterns to native BV ops.

- **COI on the batch path only (ignoring nary scalar)**: Zero improvement. The
  binary batch path was already fast (< 1% of runtime). The nary scalar path
  dominated. Fixed by applying COI to the nary path too.

- **Early-rejection filter at start NT** (both candidate-level and tuple-level):
  Unsound when the start NT is self-referencing (e.g., `str.++(nt[0], nt[0])`).
  Two variants were tried:
  1. *Candidate-level*: reject candidates that don't match spec → prevents storage
     → children unavailable for later compositions.
  2. *Tuple-level*: skip operator applications whose result can't match spec →
     result never stored → same problem (the result is needed as a child).
  Both cause String/0031 to fail (goes to size 19+ instead of solving at size 5).
  **Fundamental constraint**: in a self-referencing grammar, every candidate must
  be stored regardless of whether it matches the spec, because it may be composed
  into a matching result at a later size.

## Methodology: How to improve this project

### Principle: Data-driven, never guessing

Every optimization attempt must be motivated by measurement. The workflow:

1. **Instrument**: Add timing/counters to identify WHERE time goes
   - `search size=N: per-nt=[...] elapsed=...` already shows per-level cost
   - Use `-v -v` to get debug output from both delis and dryadsynth-bv
   - Key metrics: candidates per size, time per size, dedup hit rate

2. **Identify the bottleneck**: What fraction of time is:
   - Gate simulation (eval_batch / scalar eval)?
   - Candidate construction (Vec cloning, Value allocation)?
   - Dedup hashing (projecting + hashing wide BVs)?
   - Combinatorial explosion (too many tuples to evaluate)?

3. **Compute theoretical bounds**: Before implementing, calculate:
   - How many ops does the optimization save?
   - What's the overhead (extra allocations, cache misses)?
   - Will the savings dominate the overhead at the relevant problem sizes?

4. **Test on the right benchmark**: Match the optimization to the bottleneck:
   - Eval speed → String/0001 (large circuits, many candidates)
   - Search strategy → String/0001 (combinatorial growth at 3x/level)
   - Problem reduction → String/0031 (fast solve, tests compilation path)
   - Correctness → all 4 regression benchmarks

5. **Verify causation**: Compare with/without on the SAME machine:
   - Remote server has low noise (dedicated, no contention)
   - Use `--min` vs `--min=false` to toggle relevance/COI
   - Compare candidate counts (not just time) to confirm the mechanism

### Current bottleneck (String/0001)

At size 10: 24K candidates at nt[0], growing ~3x per level. The search is
**combinatorially bound** — eval is fast (word-parallel), dedup rejection is
low (3:1), and most candidates are genuinely distinct at 992 projected bits.

To solve String/0001 within 60s, we need either:
- Reach size ~13 (where the solution likely lives) — requires 10x fewer candidates
- Find the solution at a smaller size — requires a different CEGIS strategy
  that adds more discriminating constraints earlier

The next optimization should reduce the candidate count itself (not eval cost).
Possible approaches (each needs data to validate):
- Observational equivalence with fewer projected bits (coarser dedup)
- Grammar restriction (remove provably-useless productions based on type analysis)
- Constraint propagation to sub-NTs (backward filtering through the grammar)
- Better CEGIS: pick constraints that maximally reduce the search space

### Anti-patterns to avoid

- Guessing an optimization without profiling data
- Implementing a filter/pruning that can discard the solution
- Optimizing a path that accounts for < 10% of runtime
- Assuming the remote server has noise (it doesn't)
