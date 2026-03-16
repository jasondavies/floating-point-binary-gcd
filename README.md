# fp-gcd

This repo contains the extracted floating-point GCD experiments and the exact
threshold search tool from the original `gcd` workspace.

## Contents

- `exact_threshold_search.c`
  Exact reverse search for threshold/max-step questions.
- `gcd_fp32.c`
  CPU prototype for the 24-bit fp32 inner loop.
- `gcd_fp32.cu`
  CUDA benchmark for 24-bit fp32, 32-bit Stein, and the 32-bit hybrid.
- `gcd_fp64.cu`
  CUDA benchmark for 53-bit fp64, 64-bit Stein, and the 64-bit hybrid.

## Floating-point GCD variant

The core idea is a GPU-oriented binary-GCD variant that uses fp32 bit
manipulation to replace the usual integer left-shift alignment step.

For a pair `a <= b`, one iteration does:

1. build `t` by combining the mantissa of `a_fp32` with the exponent of `b_fp32`
2. compute `r = |b - t|`
3. reorder `(a, r)` into `(min(a, r), max(a, r))`

For 24-bit unsigned inputs, the values are represented exactly in fp32, so this
is an exact integer algorithm despite using floating-point instructions.

### 24-bit core

The 24-bit core keeps both operands in fp32 and iterates:

```text
a_fp = min(a_in, b_in)
b_fp = max(a_in, b_in)
while (a_fp != 0) {
    t_fp = splice_mantissa(a_fp, b_fp)
    t_fp = abs(b_fp - t_fp)
    b_fp = max(a_fp, t_fp)
    a_fp = min(a_fp, t_fp)
}
return uint32(max(a_fp, b_fp))
```

The splice is implemented with a single inline-PTX `lop3.b32`, so the hot loop
on RTX 4090 lowers to essentially:

```text
LOP3.LUT   R2, R8, 0x7fffff, R7, ...
FADD       R3, -R2, R7
FMNMX      R7, |R3|, R8, !PT
FMNMX      R8, |R3|, R8, PT
```

That is:

- `1` logic instruction to build the aligned operand
- `1` floating-point subtract
- `2` floating-point min/max instructions with the absolute-value modifier folded in

So the effective fp32 inner loop is only four core instructions.

### 32-bit hybrid

A full-`uint32_t` hybrid variant is also included.

The hybrid does:

1. strip common powers of two as in Stein
2. run a fixed `8` Stein-style frontend iterations
3. switch to the 24-bit fp32 core for the remainder

This extends the fp32 method beyond the exact 24-bit fp32 range while keeping
most of the work in the fast 24-bit kernel.

### 64-bit hybrid

The fp64 benchmark also includes a full-`uint64_t` hybrid variant.

The 64-bit hybrid does:

1. strip common powers of two as in Stein
2. run a fixed `11` Stein-style frontend iterations
3. switch to the 53-bit fp64 core for the remainder

This is the direct fp64 analogue of the 32-bit fp32 hybrid: the frontend is
used only to drive the operands down into the exact `u53` regime, after which
the hot loop stays in the fp64 kernel.

## Benchmark results

Benchmarks were run on RTX 4090.

### Random 24-bit inputs

```text
fp32_u24:   121.798 ms
stein_u24:  187.148 ms
```

So the fp32 variant is about `1.54x` faster than plain Stein on this workload.

### Random 32-bit inputs

With the fixed-8 hybrid frontend:

```text
fp32_u32:   180.731 ms
stein_u32:  229.446 ms
```

So the hybrid remains about `1.27x` faster than plain 32-bit Stein on this
random workload.

### Behaviour on structured inputs

The fp32 variant has a worse worst-case step count than Stein, so there are
structured inputs where Stein wins. Conversely, there are also large odd inputs
for which the 32-bit hybrid quickly drops into the 24-bit fp32 regime and is
much faster than plain Stein.

The practical result is therefore not that the floating-point variant dominates
Stein in every regime, but that it gives substantially better bulk throughput on
GPU for the tested random workloads.

## Build

CPU:

```sh
cc -O3 -std=c11 -Wall -Wextra -Wpedantic gcd_fp32.c -lm -o gcd_fp32
cc -O3 -std=c11 -Wall -Wextra -Wpedantic -pthread exact_threshold_search.c -o exact_threshold_search
```

CUDA on RTX 4090 / Ada:

```sh
nvcc -O3 -arch=sm_89 gcd_fp32.cu -o gcd_bench
nvcc -O3 -arch=sm_89 gcd_fp64.cu -o gcd_bench_u53
```

CUDA on H100 / Hopper:

```sh
nvcc -O3 -arch=sm_90 gcd_fp64.cu -o gcd_bench_u53
```

## Example runs

24-bit benchmark:

```sh
./gcd_bench both_u24
```

32-bit benchmark:

```sh
./gcd_bench both_u32
```

53-bit benchmark:

```sh
./gcd_bench_u53 both_u53
```

64-bit benchmark:

```sh
./gcd_bench_u53 both_u64
```

53-bit benchmark on Modal H100:

```sh
python3 -m pip install modal
python3 -m modal setup
python3 -m modal run modal_fp64_bench.py
```

The Modal entrypoint compiles `gcd_fp64.cu` for Hopper with `-arch=sm_90`,
requests `gpu="H100!"`, and then runs `gcd_bench_u53 both_u53` with the same
default parameters as the local binary. The `!` matters for benchmarking:
Modal's current GPU docs say plain `"H100"` may be automatically upgraded to an
H200, while `"H100!"` keeps the request pinned to H100.

You can override the benchmark parameters from the CLI, for example:

```sh
python3 -m modal run modal_fp64_bench.py --mode fp64_u53 --count 1048576 --rounds 2048 --launches 40 --block-size 256
```

Or run the 64-bit hybrid on full `uint64_t` inputs:

```sh
python3 -m modal run modal_fp64_bench.py --mode both_u64 --count 1048576 --rounds 1024 --launches 20 --block-size 256
```

To benchmark a single fixed pair across the whole launch:

```sh
python3 -m modal run modal_fp64_bench.py --use-fixed-pair --fixed-a 9007199254740991 --fixed-b 4503599627370495
```

Exact threshold search:

```sh
./exact_threshold_search parallel 53 86 0 1 5000000
```
