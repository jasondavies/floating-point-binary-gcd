CC ?= cc
CXX ?= c++
NVCC ?= nvcc
PYTHON ?= python3
LAKE ?= lake
CUDA_ARCH ?= sm_90
CFLAGS ?= -O3 -std=c11 -Wall -Wextra -Wpedantic
CXXFLAGS ?= -O3 -std=c++14 -Wall -Wextra -Wpedantic
NVCCFLAGS ?= -O3 -std=c++14

.PHONY: all cpu cuda check check-cuda-cli check-cuda proofs gcd_bench gcd_bench_u53
all: cpu
cpu: gcd_fp32 exact_threshold_search
cuda: gcd_bench gcd_bench_u53

gcd_fp32: gcd_fp32.c parse_decimal.h
	$(CC) $(CFLAGS) $< -lm -o $@

exact_threshold_search: exact_threshold_search.c parse_decimal.h
	$(CC) $(CFLAGS) -pthread $< -o $@

# Rebuild these small binaries on each request so architecture/flag changes apply.
gcd_bench: gcd_fp32.cu bench_host.cuh bench_cli.h parse_decimal.h
	$(NVCC) $(NVCCFLAGS) -arch=$(CUDA_ARCH) $< -o $@

gcd_bench_u53: gcd_fp64.cu bench_host.cuh bench_cli.h parse_decimal.h
	$(NVCC) $(NVCCFLAGS) -arch=$(CUDA_ARCH) $< -o $@

build/bench_cli_test: tests/bench_cli_test.cpp bench_cli.h parse_decimal.h
	mkdir -p build
	$(CXX) $(CXXFLAGS) -I. $< -o $@

check: cpu build/bench_cli_test
	./build/bench_cli_test
	$(PYTHON) -m unittest discover -s tests -v

# Both binaries parse CLI arguments before touching CUDA; no GPU is required.
check-cuda-cli: cuda
	./gcd_bench --help
	./gcd_bench_u53 --help

# Requires an NVIDIA GPU compatible with CUDA_ARCH.
check-cuda: cuda
	./gcd_bench both_u24 256 3 1 64
	./gcd_bench both_u32 256 3 1 64
	./gcd_bench_u53 both_u53 256 3 1 64
	./gcd_bench_u53 both_u64 256 3 1 64
	./gcd_bench both_u24 1 1 1 1 0 0
	./gcd_bench both_u32 1 1 1 1 4294967294 2147483646
	./gcd_bench_u53 both_u53 1 1 1 1 0 9007199254740991
	./gcd_bench_u53 both_u64 1 1 1 1 18446744073709551614 9223372036854775806

proofs:
	$(LAKE) exe cache get
	$(LAKE) build
