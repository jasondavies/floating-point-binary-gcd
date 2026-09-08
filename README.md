# floating-point-binary-gcd

This repository contains three related pieces of work:

- CUDA implementations of a floating-point binary-GCD variant for exact `u24`
  (`fp32`) and exact `u53` (`fp64`) inputs, plus `u32`/`u64` hybrid variants.
- An exact reverse-search tool for worst-case step counts of the underlying
  left-shift absolute-difference GCD dynamics.
- English and Lean proof artifacts for the strong pruning bound used by that
  search.

## Repository layout

- `gcd_fp32.c`
  CPU reference and validator for the exact `fp32` / `u24` loop.
- `gcd_fp32.cu`
  CUDA benchmark for `fp32_u24`, `stein_u24`, `fp32_u32`, and `stein_u32`.
- `gcd_fp64.cu`
  CUDA benchmark for `fp64_u53`, `stein_u53`, `fp64_u64`, and `stein_u64`.
- `bench_host.cuh`, `bench_cli.h`, `parse_decimal.h`
  Shared CUDA host harness and strict decimal argument parsing.
- `modal_fp32_bench.py`, `modal_fp64_bench.py`
  Thin Modal entrypoints using `modal_bench_common.py` for build and execution
  and `bench_config.py` for workloads, targets, and Python defaults.
- `run_modal_repeats.py`
  Repeats Modal runs across target GPUs and can regenerate
  `benchmarks.md`.
- `benchmarks.md`
  Historical benchmark snapshot combining March and July 2026 runs.
- `Makefile`, `tests/`
  Local CPU, argument-parser, report, and optional CUDA checks.
- `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`
  Pinned Lean 4.28.0 and Mathlib dependencies for building both proofs.
- `exact_threshold_search.c`
  Exact reverse search for threshold, max-step, frontier, and Pareto queries
  up to `k = 128`.
- `table.txt`
  Checked-in exact max-step table through `k = 128`.
- `strong_bound_proof.md`
  English proof of the strong pruning bound used by the search.
- `StrongBoundProof.lean`
  Lean 4 formalization of that strong bound.
- `SteinBound.lean`
  Separate Lean formalization of worst-case iteration bounds for Stein's
  binary GCD.
- `strong_bound_proof_prompt.md`
  Original proof prompt and audit checklist.

## Algorithm summary

For exact `u24` inputs, both operands are represented as `fp32` values. Given
`a <= b`, one loop iteration:

1. takes the mantissa of `a` and the exponent of `b`,
2. forms the aligned value `t`,
3. computes `r = |b - t|`,
4. reorders `(a, r)` back to `(min(a, r), max(a, r))`.

Because every `u24` value is exactly representable in `fp32`, this is still an
exact integer GCD algorithm. On NVIDIA GPUs the hot loop lowers to one
bit-select, one floating-point subtraction, and two `min/max` instructions.

The larger-width variants are hybrids:

- `fp32_u32` strips common powers of two, runs `9` Stein frontend iterations,
  then switches to the exact `u24` core.
- `fp64_u64` does the same with `12` Stein frontend iterations before
  switching to the exact `u53` core.

The exact-search tool studies the corresponding left-shift absolute-difference
transition system and computes exact worst-case step counts inside the
`k`-bit box.

## Current benchmark snapshot

The current checked-in benchmark report is [benchmarks.md](benchmarks.md).
The direct `u24` and `u53` rows come from Modal runs on 2026-03-17; the
corrected `u32` and `u64` hybrid rows were run on 2026-07-24. All runs used
`count=1048576`, `rounds=1024`, `launches=20`, `block_size=256`, and
`repeats=3` per requested GPU target.

Takeaways:

- `fp32_u24` beats Stein on every GPU in the current snapshot.
- `fp64_u53` wins on A100/H100/B200, but loses badly on T4.
- The corrected hybrids beat Stein on A100/H100/B200; `fp32_u32` also wins on
  T4, while `fp64_u64` loses there because of T4's limited `fp64` throughput.
- The direct `fp64_u53` variant is also expected to lose on consumer GeForce
  cards such as RTX 3090 and RTX 4090 because of heavily rate-limited `fp64`
  throughput.

## Build

Build the CPU tools and run the local checks (C/C++ compilers and Python 3.11+):

```sh
make check
```

This checks the CPU loop, compares small reverse-search results with an
independent forward model, and tests strict argument parsing, saved-report
metadata, and benchmark checkpointing. These checks do not require Modal or a GPU.

Equivalent CPU build commands:

```sh
cc -O3 -std=c11 -Wall -Wextra -Wpedantic gcd_fp32.c -lm -o gcd_fp32
cc -O3 -std=c11 -Wall -Wextra -Wpedantic -pthread exact_threshold_search.c -o exact_threshold_search
```

CUDA benchmarks:

```sh
make cuda CUDA_ARCH=sm_90
```

Set `NVCC=/path/to/nvcc` if the compiler is outside `PATH`.
`make check-cuda-cli` compiles both binaries and checks their help entrypoints
without a GPU. `make check-cuda CUDA_ARCH=sm_90` runs small random and fixed-pair
validation workloads on a compatible NVIDIA GPU.

The Modal target-to-architecture mapping is defined in `bench_config.py`.

To check the proofs, install Lean's `elan` toolchain manager, then run:

```sh
make proofs
```

`lean-toolchain` selects Lean 4.28.0. Lake resolves the exact Mathlib revision and
transitive dependencies from the checked-in manifest, downloads the prebuilt
Mathlib cache, and builds `StrongBoundProof` and `SteinBound`.
You can also set `LAKE=/path/to/lake` for an existing matching toolchain.

## Local examples

Validate the CPU `u24` loop on one pair:

```sh
./gcd_fp32 25 18
```

Exhaustively check all pairs in a small box:

```sh
./gcd_fp32 --scan 255
```

Run the CUDA benchmark locally after building:

```sh
./gcd_bench both_u24
./gcd_bench both_u32
./gcd_bench_u53 both_u53
./gcd_bench_u53 both_u64
```

Before timing, each CUDA executable validates both implementations against an
independent host GCD on the benchmark inputs and explicit regression cases.
Fixed-pair inputs are used exactly as supplied, including zero and even values;
`u24` and `u53` modes reject values outside their exact-width domains.
Unknown modes, malformed numbers, zero timing parameters, and incomplete fixed
pairs are rejected. Use `./gcd_bench --help` or `./gcd_bench_u53 --help` for
the positional argument order.

Generate exact worst-case data for `k = 1..8`:

```sh
./exact_threshold_search table 8 4 1 1000000
```

Inspect the reverse frontier at a fixed depth:

```sh
./exact_threshold_search frontier 8 3
```

Notes for `exact_threshold_search`:

- `frontier`, `search`, `parallel`, `max`, `table`, `pareto`, and
  `pareto_table` are the supported modes.
- `max`, `parallel`, `pareto`, and larger `table` runs are exhaustive searches
  and can run for a long time even with pruning.
- `visit_limit_hit=1` means the run did not finish exactly within the chosen
  search budget; the command exits with a nonzero status.
- `table.txt` is the checked-in output table through `k = 128`.

## Modal benchmarking

Install and configure Modal first:

```sh
python3 -m pip install -r requirements-modal.txt
python3 -m modal setup
```

Run a single benchmark directly:

```sh
python3 -m modal run modal_fp32_bench.py --mode both_u32
python3 -m modal run modal_fp64_bench.py --mode both_u53
```

The Modal entrypoints respect these environment variables:

- `MODAL_GPU_TYPE`
- `MODAL_CUDA_ARCH`
- `MODAL_CUDA_BASE_IMAGE`

For example, to pin an H100 run:

```sh
MODAL_GPU_TYPE=H100! MODAL_CUDA_ARCH=sm_90 python3 -m modal run modal_fp64_bench.py --mode both_u53
```

To collect repeated runs and generate a benchmark report:

```sh
python3 run_modal_repeats.py \
  --python python3 \
  --targets t4 a100 h100 b200 \
  --repeats 3 \
  --json-out benchmark-runs.json \
  --markdown-out benchmarks.md
```

The JSON file is atomically checkpointed after each successful run, so a later
failure preserves earlier results. Save this JSON alongside any published report.
Each result records the actual invocation parameters, timestamp, repeat index,
GPU/build configuration, metrics, and raw output.

Regenerate Markdown without running or paying for new benchmarks:

```sh
python3 run_modal_repeats.py \
  --summary-from-json benchmark-runs.json \
  --markdown-out benchmarks.md
```

Reports use saved parameters and timestamps, show the actual number of runs per
workload, and keep different input configurations and GPU models separate.
Older JSON files recover parameters from raw output when available; unavailable
metadata is reported as unknown. The existing historical `benchmarks.md`
snapshot has no source JSON in this repository and is retained as an archive.

## Proof and search artifacts

- [strong_bound_proof.md](strong_bound_proof.md) gives the English proof of the strong admissible pruning bound.
- [StrongBoundProof.lean](StrongBoundProof.lean) is the machine-checked Lean version of that argument.
- [SteinBound.lean](SteinBound.lean) formalizes worst-case bounds for bundled Stein reductions.
- [strong_bound_proof_prompt.md](strong_bound_proof_prompt.md) preserves the original proof prompt and audit checklist.
- [table.txt](table.txt) records the current exact max-step table through `k = 128`.

## Acknowledgements

- [AXLE - Axiom Lean Engine](https://axle.axiommath.ai/) for checking the Lean proof.
- [GPT-5.4](https://openai.com/index/introducing-gpt-5-4/) for proof drafting, formalization, and code changes.
- [Modal](https://modal.com/) for remote GPU benchmarking.
