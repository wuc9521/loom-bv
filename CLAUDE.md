# CLAUDE.md — dryadsynth-bv

## Working Environment

- **Use codegraph** (`mcp__codegraph__codegraph_explore`, `codegraph_node`, etc.) as the primary tool for understanding code. The project is indexed. Prefer it over grep/read for exploration.
- **Remote server**: All benchmarks run on `aliyun-gpu-server-1-wct-container`. Local Mac is for editing only. Workflow: edit locally → `sync-rust-to-remote` → build on remote → test on remote.
- **SSH output buffering**: When piping SSH output through `grep`, use `grep --line-buffered` or the output may not appear. Alternatively, avoid piping and capture full output.
- **Cannot scp files to remote**: Use `cp` to `~/Codes/Rust/` and run `sync-rust-to-remote` instead.

## Project Overview

dryadsynth-bv is a bitvector SyGuS (Syntax-Guided Synthesis) solver, primarily used as the backend for **delis** (`../delis`). Delis compiles typed semantic DSLs (first-order logic over finite models, string transformations, CFG learning, LTL) into SyGuS BV problems using an **aspect-based encoding** (Krogmeier & Madhusudan 2023) where each bitvector bit is a semantic aspect — a boolean property invariant under semantic equivalence. **Bitvector equality = semantic equality** by construction. See `../delis/CLAUDE.md` for delis internals.

dryadsynth-bv has two search engines:

1. **Exact Searcher** (`src/exact/search.rs`): Bottom-up enumerator evaluating candidates on ALL constraint examples simultaneously. Has symmetry breaking, relevance/COI pruning, batch BitCircuit evaluation, and interleaved BitDep-guided decomposition. Used for nullary and sparse bit-extract problems, and as the primary engine for delis-compiled problems.

2. **Sampling Engine** (`src/enumerate/algo.rs` + `src/search/`): Finds partial solutions on randomly-sampled subsets using `Bv<N> = [u64; N]` packed evaluation, combines them with ITE-tree-learning, verifies with CEGIS. Uses deductive rules (`CombineRules`, `ReverseRule`) and `for_each_subexpr` to derive additional boolean conditions. Used for refimpl problems (e.g., hackers-delight).

Both share grammar compilation (`src/enumerate/grammar.rs` → `Config`) and expression representation (`OwnedExpr`).

## How the Exact Searcher Works

**Entry**: `search_problem()` → `run_search()` → `Searcher::new()` + `Searcher::run()`.

**`Searcher::run()` loop** (the hot path):
```
for size = 1, 2, 3, ...:
    expand_rules(size)    // generate candidate tuples, evaluate via BitCircuit, dedup
    alias_fixpoint(size)  // promote through Alias rules
    try_decompose()       // BitDep-guided composition (if enabled)
    log_size_stats()
```

**`expand_rule`** for `ExactRule::Op { fid, child_nts, class }`:
1. Compute size splits across children (e.g., binary rule at size 5 → splits (1,3), (2,2), (3,1))
2. For each split, build child pools from `by_size[child_nt][child_size]`
3. Cross-product: iterate all candidate tuples from child pools
4. Evaluate each tuple via BitCircuit (`eval_nary_with_plan`) or generic eval
5. `try_push_new`: dedup check → spec match → store in `by_size[nt][size]`

**Two eval paths**:
- `use_batch = true` (BitCircuit bindings > 256): Batch-evaluates 64 tuples at once via `BitCircuitPlan::eval_batch`, using u64 word-parallel boolean simulation. Column-major: each binding computed once for all 64 candidates.
- `use_batch = false`: Per-tuple evaluation via `BitCircuitPlan::eval` or `eval_defined_with_closure`.

**Dedup** (`src/exact/dedup.rs`): Three modes:
- `MultiExact`: hash on full `Vec<BitVec>` values (all K examples concatenated)
- `MultiProjected`: hash on projected relevant bits only (uses `Relevance` analysis)
- `Pair`: for fixpoint/closure mode (LFP)

**Key data structures**:
- `Candidate { node: NodeId, values: Vec<BitVec>, values_top: Option<Vec<BitVec>> }` — stored in `by_size[nt][size]`
- `Node { nt_idx, rule_idx, children: Vec<NodeId> }` — stored in `nodes: Vec<Node>`, interned via `intern_node`
- `Grammar { nts: Vec<(&str, Vec<ExactRule>)>, start: usize }` — compiled from `Config`
- `ExactRule::Op { fid, child_nts, class }` — define-fun operator with symmetry metadata
- `ExactRule::Leaf(OwnedExpr)` — terminal (constant or variable)
- `ExactRule::Alias(usize)` — NT-to-NT forwarding
- `ExactRule::GenericTemplate { template, child_nts, base_size }` — composite template

## Relevance / COI Analysis (`src/exact/relevance/`)

**Purpose**: Reduce BitCircuit evaluation cost by computing which output bits are reachable from demanded spec bits, per NT.

- `Relevance::new()` + `advance()`: Worklist algorithm. Seeds with spec's demanded bits at Start NT, propagates backward through grammar rules using `BitDep` (per-bit dependency analysis of define-funs).
- `BitDep { per_arg: Vec<BitSet> }`: For each output bit, which input bits of each argument it depends on. Computed by `get_deffun_dep_bit(fid, bit, cache)` in `deps.rs`.
- `BitCircuitPlan::pruned(relevant_bits)`: Creates a reduced BitCircuit with only the bindings needed for the relevant output bits. Stored in `Searcher::pruned_plans`.
- **Important**: BitDep is an **overapproximation** — it reports all bits that COULD influence the output through any path (including ITE branches). It's sound for relevance (conservative = more work but correct) but NOT sound for restrictive filtering (see "What NOT to Re-try").

## Interleaved Decomposition (`src/exact/search.rs`, bottom of file)

**Purpose**: Compose solutions from sub-expressions using define-fun rules (e.g., `str.ite`). Analogous to cvc5's PBE unification.

**Architecture**: Integrated into `Searcher::run()` loop — `try_decompose()` runs after each size level. No separate pool, no budget.

- `analyze_decomposable_rules()`: Pre-analyzes Start-NT rules via `get_deffun_dep_bit`. Classifies each output bit as `Static` (owned by one child), `Conditional` (owned depends on discriminator value), or `Constant`. Produces `DecompRule` with `bit_owners: Vec<BitOwner>`.
- `try_decompose()` → `solve_sub(masks, depth)`: Recursive solver. First tries `find_match` (direct candidate lookup), then for each decomposable rule, tries `decompose(rule, disc, masks, depth)`.
- `decompose()`: Partitions demanded bits across value-children using `bit_owners` + discriminator candidate values. Recursively calls `solve_sub` for each child.
- `probe_polarity()`: Determines branch ordering for conditional bits via define-fun evaluation.

**Current status**: Works for tiny_str (2-model benchmark). Not effective on String/0122 because delis CEGIS sends very sparse specs (1-3 BV examples with ~10 demanded bits) — sub-expressions need to be nearly as complex as the full expression to match a sub-spec.

**Controlled by**: `DRYADSYNTH_COMPOSITION=1` env var → `SearchConfig::enable_composition`.

## How Delis Sends Problems to dryadsynth-bv

Delis has its own CEGIS layer (`delis/src/cegis.rs`). It:
1. Compiles the typed DSL problem into a SyGuS BV problem (define-funs, grammar, constraints)
2. Selects a SUBSET of constraints (per-aspect-per-model) as the active set
3. Sends the subset to dryadsynth-bv as a SyGuS file with `(constraint ...)` commands
4. dryadsynth-bv parses these into `Constraint { examples: Vec<Example> }` where each example is one input-output pair
5. If the solution fails on other constraints, delis adds more to the active set and re-solves

**Key implication**: The BV spec that dryadsynth-bv sees has very FEW examples (typically 1-3), each with a SPARSE mask (only bits corresponding to active constraints are demanded). This sparsity makes decomposition hard — there's not enough constraint surface to split across branches.

## BitCircuit Evaluation (`src/parse/deffun.rs`)

Define-funs compile to `DefineFunPlan::BitCircuit(BitCircuitPlan)` or `DefineFunPlan::Generic { instrs }`.

- `BitCircuitPlan { bindings: Vec<BoolNode>, output_bits: Vec<BoolAtom>, input_slots, ret_bits }`: Flat boolean circuit. Each `BoolNode` is `Atom | Not | And | Or | Xor | Ite` over `BoolAtom` references. `BoolAtom` is `Const | InputBit { arg, bit } | Temp(idx)`.
- `eval(args)`: Evaluate all bindings sequentially, then read output bits.
- `eval_batch(args_batch, count)`: Evaluate up to 64 candidate tuples in parallel using u64 word-level boolean ops. Each binding is computed once as a u64 word where bit `i` = candidate `i`'s value.
- Delis define-funs are LARGE: `str.++` has ~35750 bindings (pruned to ~3575 with COI), `str.ite` has ~7820 (pruned to ~782). These are the evaluation bottleneck.

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
- The exact Searcher with `enumerate_start` + budget successfully replaces `Algo<N>` for **expression search**.
- `eval_op_on_values` eliminates the per-evaluation AST allocation bottleneck.
- The `Vec<BitVec>` representation overhead vs `[u64; N]` is negligible (not the bottleneck).

### What Broke (Why the Revert)
When `Bv<N>` was removed, the **condition search** stopped finding good boolean conditions for ITE-tree-learning. hd-11 failed because tree learning couldn't construct the right ITE tree.

Root cause: four `Bv<N>`-dependent components were deleted: `for_each_subexpr`, `CombineRules`, `ReverseRule`, `FilterState::filter`. These need to be ported to `BitVec`/`Vec<BitVec>` before unification can proceed.

## How to Benchmark

### Setup
```bash
sync-rust-to-remote
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

### The bitwuzla issue:
Error "parse error: expected `sat` or `unsat` on `eoi`" is a race condition in rsmt2's communication with bitwuzla 0.9.1-dev (installed at /usr/local/bin/bitwuzla). NOT caused by our changes. Exists at all commits. Do NOT try to fix.

## What NOT to Re-try

Each entry below was attempted, measured, and reverted. Read before proposing similar approaches.

- **Removing Bv<N> without porting deductive rules**: Commit `fcb4362`. Breaks hd-11 condition search. The four deductive components (`for_each_subexpr`, `CombineRules`, `ReverseRule`, `FilterState::filter`) must be ported to `Vec<BitVec>` first.

- **Using exact searcher on ALL 50 examples at once for hd-11**: Times out. The grammar has 14+ binary BV64 operators → search space explodes at size 3+. Partial-solution + ITE strategy is required.

- **Replacing Vec<BitVec> with column-major BitMatrix**: Doesn't work for arithmetic ops (bvadd, bvmul need hardware addition, not bit-parallel ops).

- **Early-rejection filter at start NT**: Unsound for self-referencing grammars.

- **Start-NT mask-projected dedup**: (1) Unsound when Start is a composition child — kills sub-expression candidates needed for `str.++ Start Start`. (2) Redundant — the existing `MultiProjected` mechanism already achieves the same via backward relevance propagation.

- **Pre-built pool decomposition** (`src/decompose/` module, deleted): Pre-enumerated a separate pool up to a size budget, then did top-down recursive solve. Two problems: (1) arbitrary budget — too small misses solutions, too large wastes time; (2) duplicates enumeration work. Replaced by interleaved decomposition in `Searcher::run()`.

- **Child pool filtering via backward BitDep propagation**: Two approaches attempted, both failed for delis define-funs:
  - *Probe-based*: Used `get_deffun_dep_bit` to find single-child-dependency output bits, then probed define-fun with zero-inputs to determine polarity. **Unsound** — zero-inputs trigger wrong ITE branches in complex circuits. Broke Reg/0003.
  - *Circuit-walk (trace_forwarding)*: Walked BitCircuit `BoolNode` chain from output bit back to input, checking for pure forwarding (only `Atom`/`Not` nodes). **Sound but inapplicable** — delis define-funs use ITE chains for length-dependent char routing, so ZERO output bits are pure forwardings. 0/1310 bits propagated on String/0122.
  - **Root cause**: Delis's aspect encoding produces complex define-funs where every output bit passes through ITE nodes. Any backward constraint propagation through these circuits requires *conditional* forwarding analysis (split on ITE condition value), not simple structural checks.

## Scaling to Larger Delis String Problems

### The Bottleneck

On String/0122 (1 arg, 4 consts, 10 models, L=8, 1310 bits), the Start-NT candidate count grows ~3x per size:

```
size=7:  per-nt=[1596, 126, 1]    total=2423     elapsed=220ms
size=9:  per-nt=[13727, 405, 0]   total=20681    elapsed=2.5s
size=10: per-nt=[40993, 614, 0]   total=62288    elapsed=8.4s
size=11: per-nt=[124196, 923, 0]  total=187407   elapsed=28.4s (no solution)
```

All 124K candidates at size 11 are **semantically distinct** (bitvector dedup = semantic dedup). The growth is intrinsic to the search space, not a dedup failure.

The dominant cost is the cross-product in `expand_rule` for binary Start-NT rules like `str.++(Start, Start)`: at size 7, ~3000 tuples evaluated through a 3575-binding BitCircuit. Each eval costs ~50µs. After eval, ~50% are rejected by dedup.

### Key Properties of Delis Define-Funs

- `str.++` compiles to a ~35750-binding BitCircuit (pruned to ~3575 by COI). Internally uses ITE chains to select char positions based on argument lengths. **Not** a simple concat at the BV level.
- `str.ite` compiles to a ~7820-binding BitCircuit (pruned to ~782). Uses per-model ITE: each model's output bits are selected independently by the corresponding SBool bit.
- `str.replace` is a constant (no args in the grammar produce different strings matching the replace pattern). Compiles to a flat constant, no BitCircuit.
- `int.+`, `int.-` use arithmetic ITE chains. ~4420 chars in the define-fun.
- `bool.prefixof`, `bool.suffixof`, `bool.contains` are complex nested ITE chains.

### What Currently Helps (native BV only)

`classify_op` (`src/enumerate/grammar.rs:141`) provides `RuleClass` for native BV operators:
- `bvadd`, `bvmul`, `bvxor`: commutative → half the cross-product
- `bvand`, `bvor`: commutative + idempotent → skip `op(x, x)`
- `bvlshr`, `bvashr`, `bvshl`: shift_rhs_literal → rhs must be size-1 leaf
- `bvudiv`, `bvurem`, `bvsdiv`, `bvsrem`: nonzero_rhs → skip zero divisors

**None of this applies to delis operators** — they're define-funs with names like `str.++`, which fall to `_ => RuleClass::default()`.

### Promising Directions Not Yet Tried

1. **Operator property detection by probing**: For any define-fun `op(x, y)`, evaluate on random test values to detect commutativity (`op(a,b) == op(b,a)`), identity elements (`op(id, x) == x`), associativity (`op(op(a,b),c) == op(a,op(b,c))`). Must work for ANY arity, not just binary. Apply the detected `RuleClass` properties. This must be done SOUNDLY — use multiple random tests and only declare a property if ALL tests pass (probabilistically sound for large-bit values).

2. **Conditional backward propagation**: The current `trace_forwarding` walks BoolNode chains and gives up at any ITE. A smarter analysis could split on ITE conditions: "if condition C holds, output bit b forwards input bit k; otherwise it forwards input bit j." This would enable child pool filtering for delis define-funs. Requires tracking condition dependencies through the circuit.

3. **Delis-level CEGIS bypass**: For composition to work well, dryadsynth-bv needs DENSE specs (many demanded bits across many examples). Delis's CEGIS sends sparse subsets. An option: send ALL constraints at once for the initial attempt, fall back to CEGIS subsetting only if that times out.

### Comparison with cvc5

cvc5 solves String/0122 in 2.6s in the **native string domain** but times out on the **BV-compiled** version. The BV encoding makes the problem fundamentally harder for any bottom-up enumerator. Our advantage: perfect semantic dedup (BV equality = semantic equality). Our disadvantage: evaluation cost (3575-binding BitCircuit vs native string concat).
