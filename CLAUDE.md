# CLAUDE.md — dryadsynth-bv

## Project Overview

dryadsynth-bv is a bitvector SyGuS (Syntax-Guided Synthesis) solver. It has two search engines:

1. **Exact Searcher** (`src/exact/search.rs`): Bottom-up enumerator evaluating candidates on ALL constraint examples simultaneously. Has symmetry breaking, relevance/COI pruning, batch BitCircuit evaluation. Used for nullary and sparse bit-extract problems.

2. **Sampling Engine** (`src/enumerate/algo.rs` + `src/search/`): Finds partial solutions on randomly-sampled subsets using `Bv<N> = [u64; N]` packed evaluation, combines them with ITE-tree-learning, verifies with CEGIS. Uses deductive rules (`CombineRules`, `ReverseRule`) and `for_each_subexpr` to derive additional boolean conditions. Used for refimpl problems.

Both share grammar compilation (`src/enumerate/grammar.rs` → `Config`) and expression representation (`OwnedExpr`).

## The Unification Task

### Goal
Remove `Bv<N>`, `Algo<N>`, and the separate sampling engine. Route ALL paths through the unified exact Searcher using `Vec<BitVec>`.

### What's Already Done (commits on main)
- `6250826` — Removed pest/nom; fixed perf regression (BitVec::matches_masked)
- `b946a5e` — RuleClass symmetry breaking in exact Searcher (2x speedup on hd-11)
- `7ecb1ce` — Simplified Constraint::from_file dispatch
- `025a4e7` — `enumerate_start` callback mode with candidate budget
- `c6c57fb` — `eval_op_on_values` direct operator dispatch (no AST allocation)
- `fcb4362` — **ATTEMPTED** full removal of Bv<N>/Algo (-1626 lines) — REVERTED
- `16d015c` — Revert of above

### What Was Proven
- The exact Searcher with `enumerate_start` + budget successfully replaces `Algo<N>` for **expression search** (finds partial solutions like `#b0`/`#b1` instantly).
- Performance is competitive: ~0.3s vs old 0.6s on hd-11's expression search phase.
- `eval_op_on_values` eliminates the per-evaluation AST allocation bottleneck.
- The `Vec<BitVec>` representation overhead vs `[u64; N]` is negligible (not the bottleneck).

### What Broke (Why the Revert)
When `Bv<N>` was removed, the **condition search** stopped finding good boolean conditions for ITE-tree-learning. hd-11 failed because tree learning couldn't construct the right ITE tree.

Root cause: these components were deleted because they depend on `Bv<N>`:

1. **`for_each_subexpr`** (`src/enumerate/expr.rs`, ~110 lines): Walks all sub-expressions of a candidate and calls a filter callback with each sub-expr + its `Bv<N>` value. The condition search uses this to extract conditions from sub-expressions of enumerated BV64 expressions.

2. **`CombineRules`** (`src/deductive/combine.rs`): Combines previously-seen expressions via bitwise AND/OR to derive new boolean conditions. Fields: `mask: Bv<N>`, `output: Bv<N>`.

3. **`ReverseRule`** (`src/deductive/reverse.rs`): Derives expressions by reversing arithmetic ops. Uses `algo.map().get(&(output - v))` to look up expressions by their evaluated value.

4. **`FilterState::filter`** (`src/search/filter.rs`): Orchestrates the above on each enumerated candidate — calls `for_each_subexpr`, `CombineRules`, `ReverseRule`.

### The Fix Required
Port these four components to use `BitVec`/`Vec<BitVec>` instead of `Bv<N>`:

1. **`for_each_subexpr`**: Reimplement on `OwnedExpr`. Walk the tree, evaluate each sub-expression with `expr.eval(args)` on the sampled examples, yield `(&OwnedExpr, Vec<BitVec>)` pairs to the callback.

2. **`CombineRules`**: Replace `Bv<N>` fields with `Vec<BitVec>` (for K examples of Bool output, this is K 1-bit values). The mask/output logic stays the same — just operates on `Vec<BitVec>` element-wise.

3. **`ReverseRule`**: Replace the `algo.map()` lookup with a `HashMap<Vec<u64>, OwnedExpr>` (for 64-bit values with K examples, key = K u64 values). This map is equivalent to the exact Searcher's start-NT dedup map.

4. **Filter callback in `search_inner`**: After `enumerate_start` yields a start-NT candidate, additionally call `for_each_subexpr` + `CombineRules` + `ReverseRule` on it, passing derived expressions to `sol.add_solution_owned`.

### Key Design Constraint
`enumerate_start`'s callback currently receives only `&OwnedExpr`. For deductive rules to work, it also needs the candidate's evaluated values on sampled examples. Options:
- Change callback signature to `FnMut(&OwnedExpr, &[BitVec]) -> Result<(), ()>`
- Or re-evaluate the expression inside the callback (cheap since it's just K u64 ops for bits≤64)

## How to Benchmark

### Setup
```bash
# Sync from Mac to remote
sync-rust-to-remote    # or: /Users/chentian/.local/bin/sync-rust-to-remote

# Build on remote
ssh aliyun-gpu-server-1-wct-container "source ~/.cargo/env && cd ~/Codes/Rust/dryadsynth-bv && cargo build --release"
ssh aliyun-gpu-server-1-wct-container "source ~/.cargo/env && cd ~/Codes/Rust/delis && cargo build --release"
```

### Three benchmark cases:

```bash
# 1. Reg/0003 — nullary exact path (via delis). Target: ≤2.2s
ssh aliyun-gpu-server-1-wct-container "source ~/.cargo/env && cd ~/Codes/Rust/delis && time ./target/release/delis benchmark/Reg/0003.sl > /dev/null"

# 2. String/0031 — non-nullary sparse bit-extract (via delis). Target: ≤0.9s
ssh aliyun-gpu-server-1-wct-container "source ~/.cargo/env && cd ~/Codes/Rust/delis && time ./target/release/delis benchmark/String/0031.sl > /dev/null"

# 3. hd-11 — refimpl CEGIS+sampling (direct dryadsynth-bv). Target: ≤0.7s, ≥7/10 success
# IMPORTANT: Nondeterministic. ~30% of runs fail due to bitwuzla race condition.
ssh aliyun-gpu-server-1-wct-container "source ~/.cargo/env && cd ~/Codes/Rust/dryadsynth-bv && for i in 1 2 3 4 5 6 7 8 9 10; do ./target/release/dryadsynth-bv ./benchmarks.v2/hackers-delight/hd-11.sl 2>/dev/null && echo OK || echo FAIL; done"
```

### Success criteria:
- Reg/0003: Correct answer, ≤2.2s
- String/0031: Correct answer, ≤0.9s
- hd-11: ≥7/10 runs succeed, ≤0.7s per successful run

### The bitwuzla issue:
Error "parse error: expected `sat` or `unsat` on `eoi`" is a race condition in rsmt2's communication with bitwuzla 0.9.1-dev (installed at /usr/local/bin/bitwuzla). NOT caused by our changes. Exists at all commits. Do NOT try to fix.

## Architecture Details

### Exact Searcher (`src/exact/search.rs`)
- `run()` — first-match mode (returns on spec.matches)
- `run_with_callback(max_size, max_candidates, callback)` — yield-all mode with budget
- `enumerate_start(grammar, spec, min, max_size, max_candidates, callback)` — public entry
- Symmetry breaking in `expand_rule` for `ExactRule::Op` with `RuleClass`
- `eval_op_on_values` in `types.rs` — direct operator dispatch for GenericTemplate

### Sampling Path (`src/search/`)
- `search.rs::SearchConfig::search` — if `enable_sampling=true`, runs sampling loop
- `search.rs::SearchConfig::cegis_loop` — CEGIS verification wrapper
- `sample.rs::SampleConfig::search` → `search_inner::<N>` (const-generic dispatch)
- `filter.rs::FilterState::filter` — THE critical callback (deductive rules here)
- Flow: expr_search finds partials → cond_search finds conditions (parallel thread) → tree_learning combines → CEGIS verifies

### Key Types
- `Bv<N>` (`enumerate/mod.rs`): `[u64; N]`, stack-allocated packed evaluation
- `BitVec` (`enumerate/value.rs`): `enum { Small { bits, raw: u64 }, Big { bits, raw: Arc<BigUint> } }`
- `Constraint` (`exact/bitspec.rs`): `{ bits, args, examples: Vec<Example>, structural, closure }`
- `OwnedExpr` (`enumerate/expr.rs`): Heap-allocated expression AST
- `Grammar`/`ExactRule` (`exact/types.rs`): Compiled grammar for exact searcher
- `Config`/`Rule` (`enumerate/grammar.rs`): Shared grammar IR (both engines use this)

## What NOT to Re-try

- **Removing Bv<N> without porting deductive rules**: Commit `fcb4362`. Breaks hd-11 condition search.
- **Using exact searcher on ALL 50 examples at once for hd-11**: Times out. The grammar has 14+ binary BV64 operators → search space explodes at size 3+. Partial-solution + ITE strategy is required.
- **Replacing Vec<BitVec> with column-major BitMatrix**: Doesn't work for arithmetic ops (bvadd, bvmul need hardware addition, not bit-parallel ops).
- **Early-rejection filter at start NT**: Unsound for self-referencing grammars (see earlier CLAUDE.md notes).
