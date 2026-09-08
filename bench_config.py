"""Shared workload, target, and invocation defaults (no Modal dependency)."""

from dataclasses import dataclass

CUDA_BASE_IMAGE_DEFAULT = "nvidia/cuda:12.8.1-devel-ubuntu22.04"
DEFAULT_COUNT = 1 << 20
DEFAULT_ROUNDS = 1024
DEFAULT_LAUNCHES = 20
DEFAULT_BLOCK_SIZE = 256
DEFAULT_REPEATS = 3
DEFAULT_TARGETS = ["h100", "b200"]


@dataclass(frozen=True)
class BenchmarkSpec:
    script: str
    mode: str
    title: str


BENCHMARKS = {
    "fp32_u24": BenchmarkSpec("modal_fp32_bench.py", "both_u24", "Random 24-bit inputs"),
    "fp32_u32": BenchmarkSpec("modal_fp32_bench.py", "both_u32", "Random 32-bit inputs"),
    "fp64_u53": BenchmarkSpec("modal_fp64_bench.py", "both_u53", "Random 53-bit inputs"),
    "fp64_u64": BenchmarkSpec("modal_fp64_bench.py", "both_u64", "Random 64-bit inputs"),
}


@dataclass(frozen=True)
class TargetSpec:
    gpu_type: str
    cuda_arch: str
    cuda_base_image: str = CUDA_BASE_IMAGE_DEFAULT


TARGETS = {
    "t4": TargetSpec("T4", "sm_75"),
    "a100": TargetSpec("A100-80GB", "sm_80"),
    "h100": TargetSpec("H100!", "sm_90"),
    "b200": TargetSpec("B200", "sm_100"),
}


def validate_parameters(count: int, rounds: int, launches: int, block_size: int) -> None:
    for name, value in (("count", count), ("rounds", rounds), ("launches", launches)):
        if not 1 <= value <= 0xffffffff:
            raise ValueError(f"{name} must be between 1 and 4294967295")
    if not 1 <= block_size <= 1024:
        raise ValueError("block_size must be between 1 and 1024")
