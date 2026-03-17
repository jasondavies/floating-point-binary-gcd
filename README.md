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
- `modal_fp32_bench.py`, `modal_fp64_bench.py`
  Modal entrypoints that build the CUDA binaries remotely and run one benchmark.
- `run_modal_repeats.py`
  Repeats Modal runs across target GPUs and can regenerate
  `benchmarks.md`.
- `benchmarks.md`
  Current checked-in benchmark snapshot from Modal runs on 2026-03-17.
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
- `blog.md`
  Article-style writeup of the algorithm and benchmark results.

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

- `fp32_u32` strips common powers of two, runs `8` Stein frontend iterations,
  then switches to the exact `u24` core.
- `fp64_u64` does the same with `11` Stein frontend iterations before
  switching to the exact `u53` core.

The exact-search tool studies the corresponding left-shift absolute-difference
transition system and computes exact worst-case step counts inside the
`k`-bit box.

## Current benchmark snapshot

The current checked-in benchmark report is [benchmarks.md](benchmarks.md).
These numbers come from Modal runs on 2026-03-17 with
`count=1048576`, `rounds=1024`, `launches=20`, `block_size=256`,
and `repeats=3`.

| GPU | `u24` speedup | `u32` speedup | `u53` speedup | `u64` speedup |
| --- | ---: | ---: | ---: | ---: |
| NVIDIA Tesla T4 | 1.33x | 1.24x | 0.13x | 0.17x |
| NVIDIA A100-SXM4-80GB | 1.48x | 1.39x | 1.43x | 1.36x |
| NVIDIA A100 80GB PCIe | 1.67x | 1.56x | 1.44x | 1.38x |
| NVIDIA H100 80GB HBM3 | 1.71x | 1.50x | 1.58x | 1.40x |
| NVIDIA B200 | 1.83x | 1.44x | 1.55x | 1.40x |

Takeaways:

- `fp32_u24` and `fp32_u32` beat Stein on every GPU in the current snapshot.
- `fp64_u53` and `fp64_u64` win on A100/H100/B200, but lose badly on T4.
- The `fp64` variants are also expected to lose on consumer GeForce cards such
  as RTX 3090 and RTX 4090 because of heavily rate-limited `fp64` throughput.

## Build

CPU tools:

```sh
cc -O3 -std=c11 -Wall -Wextra -Wpedantic gcd_fp32.c -lm -o gcd_fp32
cc -O3 -std=c11 -Wall -Wextra -Wpedantic -pthread exact_threshold_search.c -o exact_threshold_search
```

CUDA benchmarks:

```sh
nvcc -O3 -arch=sm_89 gcd_fp32.cu -o gcd_bench
nvcc -O3 -arch=sm_90 gcd_fp64.cu -o gcd_bench_u53
```

Useful architecture flags from the checked-in Modal setup:

- `sm_75` for T4
- `sm_80` for A100
- `sm_90` for H100
- `sm_100` for B200

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
  search budget.
- `table.txt` is the checked-in output table through `k = 128`.

## Modal benchmarking

Install and configure Modal first:

```sh
python3 -m pip install modal
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

To regenerate the benchmark markdown from repeated runs:

```sh
python3 run_modal_repeats.py \
  --python python3 \
  --targets t4 a100 h100 b200 \
  --repeats 3 \
  --markdown-out benchmarks.md
```

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
