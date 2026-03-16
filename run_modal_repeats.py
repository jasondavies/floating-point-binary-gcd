#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import re
import statistics
import subprocess
import sys
from dataclasses import asdict, dataclass
from pathlib import Path


ANSI_RE = re.compile(r"\x1b(?:[@-Z\\-_]|\[[0-?]*[ -/]*[@-~])")
METRIC_RE = re.compile(
    r"^(?P<name>\w+): elapsed_ms=(?P<elapsed_ms>[0-9.]+) calls=(?P<calls>[0-9]+) "
    r"calls_per_second=(?P<calls_per_second>[0-9.e+-]+) ns_per_call=(?P<ns_per_call>[0-9.]+) "
    r"checksum=(?P<checksum>[0-9a-fA-F]+)$"
)


@dataclass
class Metric:
    name: str
    elapsed_ms: float
    calls: int
    calls_per_second: float
    ns_per_call: float
    checksum: str


@dataclass
class RunResult:
    benchmark: str
    mode: str
    gpu: str
    gpu_model: str
    gpu_memory_mib: int
    gpu_driver: str
    run_url: str
    metrics: list[Metric]
    raw_output: str


BENCHMARKS = {
    "fp32_u24": ("modal_fp32_bench.py", "both_u24"),
    "fp32_u32": ("modal_fp32_bench.py", "both_u32"),
    "fp64_u53": ("modal_fp64_bench.py", "both_u53"),
    "fp64_u64": ("modal_fp64_bench.py", "both_u64"),
}


def strip_ansi(text: str) -> str:
    return ANSI_RE.sub("", text).replace("\r", "\n")


def run_modal_bench(
    workdir: Path,
    python_bin: str,
    gpu_type: str,
    cuda_arch: str,
    script_name: str,
    mode: str,
    count: int,
    rounds: int,
    launches: int,
    block_size: int,
) -> str:
    env = os.environ.copy()
    env["MODAL_GPU_TYPE"] = gpu_type
    env["MODAL_CUDA_ARCH"] = cuda_arch

    cmd = [
        python_bin,
        "-m",
        "modal",
        "run",
        script_name,
        "--mode",
        mode,
        "--count",
        str(count),
        "--rounds",
        str(rounds),
        "--launches",
        str(launches),
        "--block-size",
        str(block_size),
    ]

    completed = subprocess.run(
        cmd,
        cwd=workdir,
        env=env,
        text=True,
        capture_output=True,
    )
    combined = strip_ansi(completed.stdout + "\n" + completed.stderr)
    if completed.returncode != 0:
        raise RuntimeError(f"modal run failed for {script_name} {mode}\n{combined}")
    return combined


def parse_result(benchmark: str, mode: str, text: str) -> RunResult:
    gpu = None
    gpu_model = None
    gpu_memory_mib = 0
    gpu_driver = None
    run_url = ""
    metrics: list[Metric] = []

    for line in text.splitlines():
        line = line.strip()
        if not line:
            continue
        if line.startswith("gpu="):
            gpu = line[len("gpu=") :]
            parts = [part.strip() for part in gpu.split(",")]
            if len(parts) >= 3:
                gpu_model = parts[0]
                gpu_memory_mib = int(parts[1].split()[0])
                gpu_driver = parts[2]
            continue
        if line.startswith("https://modal.com/apps/"):
            run_url = line
            continue
        if "View run at" in line:
            continue
        match = METRIC_RE.match(line)
        if match:
            metrics.append(
                Metric(
                    name=match.group("name"),
                    elapsed_ms=float(match.group("elapsed_ms")),
                    calls=int(match.group("calls")),
                    calls_per_second=float(match.group("calls_per_second")),
                    ns_per_call=float(match.group("ns_per_call")),
                    checksum=match.group("checksum"),
                )
            )

    if gpu is None:
        raise RuntimeError(f"failed to parse GPU from output for {benchmark}\n{text}")
    if gpu_model is None or gpu_driver is None:
        raise RuntimeError(f"failed to parse GPU details from output for {benchmark}\n{text}")
    if not metrics:
        raise RuntimeError(f"failed to parse metrics from output for {benchmark}\n{text}")

    return RunResult(
        benchmark=benchmark,
        mode=mode,
        gpu=gpu,
        gpu_model=gpu_model,
        gpu_memory_mib=gpu_memory_mib,
        gpu_driver=gpu_driver,
        run_url=run_url,
        metrics=metrics,
        raw_output=text,
    )


def print_summary(results: list[RunResult]) -> None:
    gpu_groups: dict[str, list[RunResult]] = {}
    for result in results:
        gpu_groups.setdefault(result.gpu_model, []).append(result)

    print("\nSummary by exact GPU:")
    for gpu in sorted(gpu_groups):
        gpu_results = gpu_groups[gpu]
        print(f"\n{gpu}")
        benchmarks = sorted({result.benchmark for result in gpu_results})
        for benchmark in benchmarks:
            bench_results = [result for result in gpu_results if result.benchmark == benchmark]
            metric_map: dict[str, list[Metric]] = {}
            for result in bench_results:
                for metric in result.metrics:
                    metric_map.setdefault(metric.name, []).append(metric)

            driver_set = sorted({result.gpu_driver for result in bench_results})
            print(f"  {benchmark}: {len(bench_results)} run(s), drivers={', '.join(driver_set)}")
            for name in sorted(metric_map):
                metrics = metric_map[name]
                elapsed = statistics.median(metric.elapsed_ms for metric in metrics)
                cps = statistics.median(metric.calls_per_second for metric in metrics)
                nspc = statistics.median(metric.ns_per_call for metric in metrics)
                print(f"    - {name}: {elapsed:.3f} ms, {cps:.3e} calls/s, {nspc:.3f} ns/call")


def load_results(path: Path) -> list[RunResult]:
    data = json.loads(path.read_text())
    results: list[RunResult] = []
    for item in data:
        metrics = [Metric(**metric) for metric in item["metrics"]]
        item = dict(item)
        item["metrics"] = metrics
        if "gpu_model" not in item or "gpu_driver" not in item or "gpu_memory_mib" not in item:
            parts = [part.strip() for part in item["gpu"].split(",")]
            if len(parts) < 3:
                raise RuntimeError(f"could not parse legacy GPU field: {item['gpu']}")
            item["gpu_model"] = parts[0]
            item["gpu_memory_mib"] = int(parts[1].split()[0])
            item["gpu_driver"] = parts[2]
        results.append(RunResult(**item))
    return results


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--python", default=".venv/bin/python")
    parser.add_argument("--gpu-type", default="A100-80GB")
    parser.add_argument("--cuda-arch", default="sm_80")
    parser.add_argument("--count", type=int, default=1 << 20)
    parser.add_argument("--rounds", type=int, default=1024)
    parser.add_argument("--launches", type=int, default=20)
    parser.add_argument("--block-size", type=int, default=256)
    parser.add_argument("--repeats", type=int, default=3)
    parser.add_argument(
        "--benchmarks",
        nargs="+",
        choices=sorted(BENCHMARKS),
        default=["fp32_u24", "fp32_u32", "fp64_u53", "fp64_u64"],
    )
    parser.add_argument("--summary-from-json", default="")
    parser.add_argument("--json-out", default="")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    workdir = Path(__file__).resolve().parent
    results: list[RunResult]

    if args.summary_from_json:
        results = load_results(Path(args.summary_from_json))
        print_summary(results)
        return 0

    results = []

    total_runs = len(args.benchmarks) * args.repeats
    run_index = 0

    for benchmark in args.benchmarks:
        script_name, mode = BENCHMARKS[benchmark]
        for repeat in range(1, args.repeats + 1):
            run_index += 1
            print(f"[{run_index}/{total_runs}] {benchmark} repeat {repeat}/{args.repeats}", flush=True)
            output = run_modal_bench(
                workdir=workdir,
                python_bin=args.python,
                gpu_type=args.gpu_type,
                cuda_arch=args.cuda_arch,
                script_name=script_name,
                mode=mode,
                count=args.count,
                rounds=args.rounds,
                launches=args.launches,
                block_size=args.block_size,
            )
            result = parse_result(benchmark, mode, output)
            results.append(result)
            print(f"  gpu={result.gpu}", flush=True)
            for metric in result.metrics:
                print(
                    f"  {metric.name}: {metric.elapsed_ms:.3f} ms, "
                    f"{metric.calls_per_second:.3e} calls/s, {metric.ns_per_call:.3f} ns/call",
                    flush=True,
                )
            if result.run_url:
                print(f"  run={result.run_url}", flush=True)

    print_summary(results)

    if args.json_out:
        out_path = Path(args.json_out)
        out_path.write_text(json.dumps([asdict(result) for result in results], indent=2) + "\n")
        print(f"\nWrote {out_path}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
