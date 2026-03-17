from __future__ import annotations

import os
import subprocess
from pathlib import Path

import modal

APP_NAME = "fp-gcd-fp64-bench"
CUDA_BASE_IMAGE = os.environ.get("MODAL_CUDA_BASE_IMAGE", "nvidia/cuda:12.8.1-devel-ubuntu22.04")
CUDA_ARCH = os.environ.get("MODAL_CUDA_ARCH", "sm_90")
GPU_TYPE = os.environ.get("MODAL_GPU_TYPE", "H100!")
REMOTE_WORKDIR = "/workspace"

SOURCE_FILE = Path(__file__).with_name("gcd_fp64.cu")
REMOTE_SOURCE = f"{REMOTE_WORKDIR}/gcd_fp64.cu"
REMOTE_BINARY = f"{REMOTE_WORKDIR}/gcd_bench_u53"

app = modal.App(APP_NAME)

image = (
    modal.Image.from_registry(CUDA_BASE_IMAGE, add_python="3.11")
    .run_commands(
        "apt-get update",
        "DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends build-essential",
        "rm -rf /var/lib/apt/lists/*",
    )
    .add_local_file(SOURCE_FILE, REMOTE_SOURCE, copy=True)
    .run_commands(
        f"nvcc -O3 -arch={CUDA_ARCH} {REMOTE_SOURCE} -o {REMOTE_BINARY}",
    )
)


@app.function(image=image, gpu=GPU_TYPE, timeout=60 * 60)
def run_fp64_bench(
    mode: str = "both_u53",
    count: int = 1 << 20,
    rounds: int = 1024,
    launches: int = 20,
    block_size: int = 256,
    use_fixed_pair: bool = False,
    fixed_a: int = 0,
    fixed_b: int = 0,
) -> str:
    gpu_info = subprocess.run(
        [
            "nvidia-smi",
            "--query-gpu=name,memory.total,driver_version",
            "--format=csv,noheader",
        ],
        check=True,
        text=True,
        capture_output=True,
    ).stdout.strip()

    command = [
        REMOTE_BINARY,
        mode,
        str(count),
        str(rounds),
        str(launches),
        str(block_size),
    ]
    if use_fixed_pair:
        command.extend([str(fixed_a), str(fixed_b)])

    result = subprocess.run(
        command,
        check=True,
        text=True,
        capture_output=True,
        cwd=REMOTE_WORKDIR,
    )

    lines = [
        f"gpu={gpu_info}",
        f"binary={REMOTE_BINARY}",
        f"command={' '.join(command)}",
    ]
    if result.stderr.strip():
        lines.append(f"stderr={result.stderr.strip()}")
    lines.append(result.stdout.strip())
    return "\n".join(lines)


@app.local_entrypoint()
def main(
    mode: str = "both_u53",
    count: int = 1 << 20,
    rounds: int = 1024,
    launches: int = 20,
    block_size: int = 256,
    use_fixed_pair: bool = False,
    fixed_a: int = 0,
    fixed_b: int = 0,
) -> None:
    output = run_fp64_bench.remote(
        mode=mode,
        count=count,
        rounds=rounds,
        launches=launches,
        block_size=block_size,
        use_fixed_pair=use_fixed_pair,
        fixed_a=fixed_a,
        fixed_b=fixed_b,
    )
    print(output)
