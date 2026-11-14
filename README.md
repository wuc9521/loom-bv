# loom-bv

The bit-vector SyGuS solver behind [Loom](https://github.com/wuc9521/loom),
derived from [DryadSynth](https://github.com/purdue-cap/DryadSynth). Loom links
it as a library; it also builds as a standalone binary.

## Usage

```bash
cargo run --release -- [-c <config.toml>] <file.sl>   # or `-in` to read stdin
```

| Flag | Effect |
|---|---|
| `-c`, `--config <FILE>` | Search configuration (TOML); see [`conf.toml`](conf.toml) and [`config/`](config) |
| `--min=false` | Disable candidate deduplication and relevance/circuit pruning |
| `-v`, `-vv` | More logging |

Example configuration:

```toml
random_example = 10   # extra random examples drawn from the reference implementation
limited_ite = true    # cap ITE condition search at 10000
smt_solver = "bitwuzla"

[expr_search]
sample = 64           # number of samples
dag_size = true       # graph-based enumeration
filter = { deductive_combine = true, deductive_reverse = true }
```

## Publication

Yuantian Ding, Xiaokang Qiu.
[Enhanced Enumeration Techniques for Syntax-Guided Synthesis of Bit-Vector Manipulations](https://dl.acm.org/doi/10.1145/3632913).
POPL 2024.
