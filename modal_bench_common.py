"""Build and run either precision through the same Modal entrypoint factory."""

import os
import subprocess
from pathlib import Path

import modal

from bench_config import (
    CUDA_BASE_IMAGE_DEFAULT, DEFAULT_COUNT, DEFAULT_ROUNDS,
    DEFAULT_LAUNCHES, DEFAULT_BLOCK_SIZE, TARGETS, validate_parameters,
)


def create_app(precision: str):
    if precision not in ("fp32", "fp64"):
        raise ValueError(f"unknown precision: {precision}")
    default_mode = "both_u24" if precision == "fp32" else "both_u53"
    source = f"gcd_{precision}.cu"
    binary = "/workspace/gcd_bench" + ("" if precision == "fp32" else "_u53")
    target = TARGETS["h100"]
    app = modal.App(f"fp-gcd-{precision}-bench")
    cuda_arch = os.environ.get("MODAL_CUDA_ARCH", target.cuda_arch)
    # This value is interpolated into a compiler command.
    if not cuda_arch.startswith("sm_") or not cuda_arch[3:].isdigit():
        raise ValueError("MODAL_CUDA_ARCH must have the form sm_<digits>")
    image = modal.Image.from_registry(
        os.environ.get("MODAL_CUDA_BASE_IMAGE", CUDA_BASE_IMAGE_DEFAULT),
        add_python="3.11",
    ).run_commands(
        "apt-get update",
        "DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends build-essential",
        "rm -rf /var/lib/apt/lists/*",
    )
    for filename in (source, "bench_host.cuh", "bench_cli.h", "parse_decimal.h"):
        image = image.add_local_file(
            Path(__file__).with_name(filename), f"/workspace/{filename}", copy=True,
        )
    image = image.run_commands(
        f"nvcc -O3 -std=c++14 -arch={cuda_arch} /workspace/{source} -o {binary}",
    ).add_local_python_source("modal_bench_common", "bench_config")

    @app.function(image=image, gpu=os.environ.get("MODAL_GPU_TYPE", target.gpu_type),
                  timeout=60 * 60, name=f"run_{precision}_bench", serialized=True)
    def run_bench(
        mode: str = default_mode,
        count: int = DEFAULT_COUNT,
        rounds: int = DEFAULT_ROUNDS,
        launches: int = DEFAULT_LAUNCHES,
        block_size: int = DEFAULT_BLOCK_SIZE,
        use_fixed_pair: bool = False,
        fixed_a: int = 0,
        fixed_b: int = 0,
    ) -> str:
        validate_parameters(count, rounds, launches, block_size)
        gpu_info = subprocess.run(
            ["nvidia-smi", "--query-gpu=name,memory.total,driver_version", "--format=csv,noheader"],
            check=True, text=True, capture_output=True,
        ).stdout.strip()
        command = [binary, mode, str(count), str(rounds), str(launches), str(block_size)]
        if use_fixed_pair:
            command.extend([str(fixed_a), str(fixed_b)])
        result = subprocess.run(
            command, check=True, text=True, capture_output=True, cwd="/workspace",
        )
        lines = [f"gpu={gpu_info}", f"binary={binary}", f"command={' '.join(command)}"]
        if result.stderr.strip():
            lines.append(f"stderr={result.stderr.strip()}")
        lines.append(result.stdout.strip())
        return "\n".join(lines)

    return app, run_bench


def invoke(
    remote,
    precision: str,
    mode: str,
    count: int = DEFAULT_COUNT,
    rounds: int = DEFAULT_ROUNDS,
    launches: int = DEFAULT_LAUNCHES,
    block_size: int = DEFAULT_BLOCK_SIZE,
    use_fixed_pair: bool = False,
    fixed_a: int = 0,
    fixed_b: int = 0,
) -> None:
    validate_parameters(count, rounds, launches, block_size)
    widths = ("u24", "u32") if precision == "fp32" else ("u53", "u64")
    modes = {"both", precision, "stein"} | {
        f"{kind}_{width}" for width in widths for kind in ("both", precision, "stein")
    }
    if mode not in modes:
        raise ValueError(f"unknown mode: {mode}")
    if use_fixed_pair:
        bits = int((mode.rsplit("_", 1)[1] if "_" in mode else widths[0])[1:])
        if not 0 <= fixed_a < 1 << bits or not 0 <= fixed_b < 1 << bits:
            raise ValueError(f"fixed pair must contain unsigned {bits}-bit integers")
    print(remote.remote(
        mode=mode, count=count, rounds=rounds, launches=launches,
        block_size=block_size, use_fixed_pair=use_fixed_pair,
        fixed_a=fixed_a, fixed_b=fixed_b,
    ))
