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
from datetime import UTC, datetime


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
    target: str
    requested_gpu_type: str
    cuda_arch: str
    cuda_base_image: str
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

CUDA_BASE_IMAGE_DEFAULT = "nvidia/cuda:12.8.1-devel-ubuntu22.04"


@dataclass(frozen=True)
class TargetSpec:
    name: str
    gpu_type: str
    cuda_arch: str
    cuda_base_image: str


TARGETS = {
    "t4": TargetSpec(
        name="t4",
        gpu_type="T4",
        cuda_arch="sm_75",
        cuda_base_image=CUDA_BASE_IMAGE_DEFAULT,
    ),
    "a100": TargetSpec(
        name="a100",
        gpu_type="A100-80GB",
        cuda_arch="sm_80",
        cuda_base_image=CUDA_BASE_IMAGE_DEFAULT,
    ),
    "h100": TargetSpec(
        name="h100",
        gpu_type="H100!",
        cuda_arch="sm_90",
        cuda_base_image=CUDA_BASE_IMAGE_DEFAULT,
    ),
    "b200": TargetSpec(
        name="b200",
        gpu_type="B200",
        cuda_arch="sm_100",
        cuda_base_image=CUDA_BASE_IMAGE_DEFAULT,
    ),
}

WORKLOAD_TITLES = {
    "fp32_u24": "Random 24-bit inputs",
    "fp32_u32": "Random 32-bit inputs",
    "fp64_u53": "Random 53-bit inputs",
    "fp64_u64": "Random 64-bit inputs",
}


def strip_ansi(text: str) -> str:
    return ANSI_RE.sub("", text).replace("\r", "\n")


def run_modal_bench(
    workdir: Path,
    python_bin: str,
    target: str,
    gpu_type: str,
    cuda_arch: str,
    cuda_base_image: str,
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
    env["MODAL_CUDA_BASE_IMAGE"] = cuda_base_image

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
        raise RuntimeError(
            f"modal run failed for {script_name} {mode} target={target} "
            f"gpu={gpu_type} arch={cuda_arch}\n{combined}"
        )
    return combined


def parse_result(
    benchmark: str,
    mode: str,
    target: str,
    gpu_type: str,
    cuda_arch: str,
    cuda_base_image: str,
    text: str,
) -> RunResult:
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
        target=target,
        requested_gpu_type=gpu_type,
        cuda_arch=cuda_arch,
        cuda_base_image=cuda_base_image,
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


def median_metric(results: list[RunResult], benchmark: str, metric_name: str) -> Metric:
    metrics = [
        metric
        for result in results
        if result.benchmark == benchmark
        for metric in result.metrics
        if metric.name == metric_name
    ]
    if not metrics:
        raise RuntimeError(f"missing metric {metric_name} for {benchmark}")
    return Metric(
        name=metric_name,
        elapsed_ms=statistics.median(metric.elapsed_ms for metric in metrics),
        calls=int(statistics.median(metric.calls for metric in metrics)),
        calls_per_second=statistics.median(metric.calls_per_second for metric in metrics),
        ns_per_call=statistics.median(metric.ns_per_call for metric in metrics),
        checksum=metrics[0].checksum,
    )


def render_markdown(results: list[RunResult], args: argparse.Namespace) -> str:
    lines = [
        "# Benchmark Results",
        "",
        f"Generated from Modal runs on {datetime.now(UTC).strftime('%Y-%m-%d %H:%M UTC')}.",
        "",
        "Run parameters:",
        "",
        f"- `count={args.count}`",
        f"- `rounds={args.rounds}`",
        f"- `launches={args.launches}`",
        f"- `block_size={args.block_size}`",
        f"- `repeats={args.repeats}`",
        "",
        "Target configuration:",
        "",
    ]
    for target_name in args.targets:
        spec = TARGETS[target_name]
        lines.append(
            f"- `{target_name}`: `gpu={spec.gpu_type}`, `-arch={spec.cuda_arch}`, "
            f"`image={spec.cuda_base_image}`"
        )
    lines.append("")

    results_by_target: dict[str, list[RunResult]] = {}
    for result in results:
        results_by_target.setdefault(result.target, []).append(result)

    for target_name in args.targets:
        target_results = results_by_target.get(target_name, [])
        if not target_results:
            continue

        gpu_models: list[str] = []
        for result in target_results:
            if result.gpu_model not in gpu_models:
                gpu_models.append(result.gpu_model)

        for gpu_model in gpu_models:
            gpu_results = [result for result in target_results if result.gpu_model == gpu_model]
            sample = gpu_results[0]
            driver_set = sorted({result.gpu_driver for result in gpu_results})
            memory_set = sorted({result.gpu_memory_mib for result in gpu_results})

            lines.extend(
                [
                    f"## {sample.gpu_model}",
                    "",
                    f"- Modal request: `{sample.requested_gpu_type}`",
                    f"- CUDA arch: `{sample.cuda_arch}`",
                    f"- CUDA base image: `{sample.cuda_base_image}`",
                ]
            )
            if len(driver_set) == 1:
                lines.append(f"- Driver: `{driver_set[0]}`")
            else:
                lines.append(f"- Drivers seen: `{', '.join(driver_set)}`")
            if len(memory_set) == 1:
                lines.append(f"- Reported memory: `{memory_set[0]} MiB`")
            else:
                memory_text = ", ".join(f"{memory} MiB" for memory in memory_set)
                lines.append(f"- Reported memory seen: `{memory_text}`")
            if len(gpu_models) > 1:
                lines.append(
                    f"- Note: target `{target_name}` returned multiple exact GPU models; "
                    "this section uses only runs from this model."
                )
            lines.extend(
                [
                    "",
                    "| workload | fp/hybrid ns/call | Stein ns/call | speedup vs Stein |",
                    "| --- | ---: | ---: | ---: |",
                ]
            )
            for benchmark in ("fp32_u24", "fp32_u32", "fp64_u53", "fp64_u64"):
                bench_results = [result for result in gpu_results if result.benchmark == benchmark]
                if not bench_results:
                    continue
                fp_metric_name = next(
                    metric.name
                    for metric in bench_results[0].metrics
                    if not metric.name.startswith("stein_")
                )
                stein_metric_name = next(
                    metric.name
                    for metric in bench_results[0].metrics
                    if metric.name.startswith("stein_")
                )
                fp_metric = median_metric(gpu_results, benchmark, fp_metric_name)
                stein_metric = median_metric(gpu_results, benchmark, stein_metric_name)
                speedup = stein_metric.ns_per_call / fp_metric.ns_per_call
                lines.append(
                    f"| {WORKLOAD_TITLES[benchmark]} | {fp_metric.ns_per_call:.3f} | "
                    f"{stein_metric.ns_per_call:.3f} | {speedup:.2f}x |"
                )
            lines.append("")

    return "\n".join(lines).rstrip() + "\n"


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
        item.setdefault("target", "legacy")
        item.setdefault("requested_gpu_type", "")
        item.setdefault("cuda_arch", "")
        item.setdefault("cuda_base_image", "")
        results.append(RunResult(**item))
    return results


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--python", default=".venv/bin/python")
    parser.add_argument(
        "--targets",
        nargs="+",
        choices=sorted(TARGETS),
        default=["h100", "b200"],
    )
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
    parser.add_argument("--markdown-out", default="")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    workdir = Path(__file__).resolve().parent
    results: list[RunResult]

    if args.summary_from_json:
        results = load_results(Path(args.summary_from_json))
        print_summary(results)
        if args.markdown_out:
            out_path = Path(args.markdown_out)
            out_path.write_text(render_markdown(results, args))
            print(f"\nWrote {out_path}")
        return 0

    results = []

    total_runs = len(args.targets) * len(args.benchmarks) * args.repeats
    run_index = 0

    for target_name in args.targets:
        target = TARGETS[target_name]
        for benchmark in args.benchmarks:
            script_name, mode = BENCHMARKS[benchmark]
            for repeat in range(1, args.repeats + 1):
                run_index += 1
                print(
                    f"[{run_index}/{total_runs}] {target_name} {benchmark} "
                    f"repeat {repeat}/{args.repeats}",
                    flush=True,
                )
                output = run_modal_bench(
                    workdir=workdir,
                    python_bin=args.python,
                    target=target_name,
                    gpu_type=target.gpu_type,
                    cuda_arch=target.cuda_arch,
                    cuda_base_image=target.cuda_base_image,
                    script_name=script_name,
                    mode=mode,
                    count=args.count,
                    rounds=args.rounds,
                    launches=args.launches,
                    block_size=args.block_size,
                )
                result = parse_result(
                    benchmark,
                    mode,
                    target_name,
                    target.gpu_type,
                    target.cuda_arch,
                    target.cuda_base_image,
                    output,
                )
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

    if args.markdown_out:
        out_path = Path(args.markdown_out)
        out_path.write_text(render_markdown(results, args))
        print(f"Wrote {out_path}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
