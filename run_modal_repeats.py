#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import re
import statistics
import tempfile
import subprocess
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path
from datetime import UTC, datetime

from bench_config import (
    BENCHMARKS, TARGETS, DEFAULT_TARGETS, CUDA_BASE_IMAGE_DEFAULT,
    DEFAULT_COUNT, DEFAULT_ROUNDS, DEFAULT_LAUNCHES, DEFAULT_BLOCK_SIZE,
    DEFAULT_REPEATS, validate_parameters,
)


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


@dataclass(frozen=True)
class RunParameters:
    count: int | None = None
    rounds: int | None = None
    launches: int | None = None
    block_size: int | None = None
    fixed_pair: tuple[int, int] | None = None


CONFIG_RE = re.compile(
    r"^mode=(?P<mode>\w+) count=(?P<count>\d+) rounds=(?P<rounds>\d+) "
    r"launches=(?P<launches>\d+) block_size=(?P<block_size>\d+)"
    r"(?: fixed_pair=(?P<a>\d+),(?P<b>\d+))?$"
)


def parameters_from_output(text: str) -> tuple[str | None, RunParameters]:
    for line in text.splitlines():
        match = CONFIG_RE.fullmatch(line.strip())
        if match:
            return match["mode"], RunParameters(
                **{key: int(match[key]) for key in ("count", "rounds", "launches", "block_size")},
                fixed_pair=(int(match["a"]), int(match["b"])) if match["a"] else None,
            )
    return None, RunParameters()


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
    parameters: RunParameters = field(default_factory=RunParameters)
    executed_at: str | None = None
    repeat_index: int | None = None


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
    *,
    executed_at: str | None = None,
    repeat_index: int | None = None,
) -> RunResult:
    actual_mode, parameters = parameters_from_output(text)
    if actual_mode != mode:
        raise RuntimeError(f"expected mode={mode}, received {actual_mode}")
    validate_parameters(parameters.count, parameters.rounds, parameters.launches, parameters.block_size)
    gpu = None
    gpu_model = None
    gpu_memory_mib = 0
    gpu_driver = None
    run_url = ""
    metrics: list[Metric] = []
    validation_ok = False

    for line in text.splitlines():
        line = line.strip()
        if not line:
            continue
        if line.startswith(f"validation=ok workload={mode.removeprefix('both_')} "):
            validation_ok = True
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
    if not validation_ok:
        raise RuntimeError(f"benchmark validation did not run for {benchmark}\n{text}")

    if mode == "both" or mode.startswith("both_"):
        fp_metrics = [metric for metric in metrics if not metric.name.startswith("stein_")]
        stein_metrics = [metric for metric in metrics if metric.name.startswith("stein_")]
        if len(fp_metrics) != 1 or len(stein_metrics) != 1:
            raise RuntimeError(
                f"expected one FP/hybrid and one Stein metric for {benchmark}\n{text}"
            )
        if int(fp_metrics[0].checksum, 16) != int(stein_metrics[0].checksum, 16):
            raise RuntimeError(
                f"timed checksum mismatch for {benchmark}: "
                f"{fp_metrics[0].name}={fp_metrics[0].checksum} "
                f"{stein_metrics[0].name}={stein_metrics[0].checksum}\n{text}"
            )

    expected_names = {benchmark, "stein_" + benchmark.split("_", 1)[1]}
    if {metric.name for metric in metrics} != expected_names or len(metrics) != 2:
        raise RuntimeError(f"unexpected metric names for {benchmark}")
    expected_calls = parameters.count * parameters.rounds * parameters.launches
    if any(metric.calls != expected_calls for metric in metrics):
        raise RuntimeError(f"call count does not match invocation for {benchmark}")

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
        parameters=parameters,
        executed_at=executed_at,
        repeat_index=repeat_index,
    )


def result_groups(results: list[RunResult]):
    """Never pool runs from different targets, builds, or input parameters."""
    groups = {}
    for result in results:
        key = (
            result.target, result.gpu_model, result.requested_gpu_type,
            result.cuda_arch, result.cuda_base_image, result.parameters,
        )
        groups.setdefault(key, []).append(result)
    return groups.values()


def median_ns(results: list[RunResult], metric_name: str) -> float:
    values = [
        metric.ns_per_call for result in results
        for metric in result.metrics if metric.name == metric_name
    ]
    if not values:
        raise ValueError(f"missing metric {metric_name}")
    return statistics.median(values)


def workload_rows(results: list[RunResult]):
    for benchmark, spec in BENCHMARKS.items():
        runs = [result for result in results if result.benchmark == benchmark]
        if not runs:
            continue
        fp_ns = median_ns(runs, benchmark)
        stein_ns = median_ns(runs, "stein_" + benchmark.split("_", 1)[1])
        if fp_ns <= 0:
            raise ValueError(f"nonpositive FP timing for {benchmark}")
        title = spec.title
        pair = runs[0].parameters.fixed_pair
        if pair is not None:
            title = f"Fixed {benchmark.split('_', 1)[1]} inputs ({pair[0]}, {pair[1]})"
        yield title, fp_ns, stein_ns, stein_ns / fp_ns, len(runs)


def print_summary(results: list[RunResult]) -> None:
    for runs in result_groups(results):
        sample = runs[0]
        print(f"\n{sample.gpu_model} (target={sample.target}, arch={sample.cuda_arch})")
        print(f"  parameters={asdict(sample.parameters)}")
        for title, fp_ns, stein_ns, speedup, count in workload_rows(runs):
            print(f"  {title}: FP={fp_ns:.3f}, Stein={stein_ns:.3f} ns/call, "
                  f"{speedup:.2f}x ({count} runs)")


def report_targets(results: list[RunResult], requested_targets: list[str] | None) -> list[str]:
    return requested_targets if requested_targets is not None else list(dict.fromkeys(
        result.target for result in results
    ))


def render_markdown(results: list[RunResult], args: argparse.Namespace) -> str:
    target_names = report_targets(results, args.targets)
    selected = [result for target in target_names for result in results if result.target == target]
    lines = ["# Benchmark Results", "", "Aggregated from saved Modal results.", ""]
    for runs in result_groups(selected):
        sample = runs[0]
        lines.extend([
            f"## {sample.gpu_model}", "",
            f"- Target: `{sample.target}`",
            f"- Modal request: `{sample.requested_gpu_type or 'unknown'}`",
            f"- CUDA arch: `{sample.cuda_arch or 'unknown'}`",
            f"- CUDA base image: `{sample.cuda_base_image or 'unknown'}`",
            f"- Drivers seen: `{', '.join(sorted({r.gpu_driver for r in runs}))}`",
            f"- Reported memory: `{', '.join(str(m) for m in sorted({r.gpu_memory_mib for r in runs}))} MiB`",
        ])
        timestamps = sorted({r.executed_at for r in runs if r.executed_at})
        if timestamps:
            lines.append(f"- Run timestamps (UTC): `{timestamps[0]}` to `{timestamps[-1]}`")
        if any(r.executed_at is None for r in runs):
            lines.append("- Run timestamp: unknown for one or more legacy runs")
        params = sample.parameters
        for key in ("count", "rounds", "launches", "block_size"):
            value = getattr(params, key)
            lines.append(f"- `{key}={value if value is not None else 'unknown'}`")
        lines.extend([
            "", "| workload | fp/hybrid ns/call | Stein ns/call | speedup vs Stein | runs |",
            "| --- | ---: | ---: | ---: | ---: |",
        ])
        for title, fp_ns, stein_ns, speedup, count in workload_rows(runs):
            lines.append(f"| {title} | {fp_ns:.3f} | {stein_ns:.3f} | {speedup:.2f}x | {count} |")
        lines.append("")
    return "\n".join(lines).rstrip() + "\n"


def save_results(path: Path, results: list[RunResult]) -> None:
    """Checkpoint atomically so interruptions leave the preceding snapshot intact."""
    payload = json.dumps([asdict(result) for result in results], indent=2) + "\n"
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=path.parent,
                                         prefix=f".{path.name}.", delete=False) as output:
            temporary = Path(output.name)
            output.write(payload)
            output.flush()
            os.fsync(output.fileno())
        temporary.replace(path)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


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
        if "parameters" in item:
            parameters = dict(item["parameters"])
            if parameters.get("fixed_pair") is not None:
                parameters["fixed_pair"] = tuple(parameters["fixed_pair"])
            item["parameters"] = RunParameters(**parameters)
        else:
            _, item["parameters"] = parameters_from_output(item.get("raw_output", ""))
        results.append(RunResult(**item))
    return results


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--python", default=sys.executable)
    parser.add_argument(
        "--targets",
        nargs="+",
        choices=sorted(TARGETS),
        default=None,
    )
    parser.add_argument("--count", type=int, default=DEFAULT_COUNT)
    parser.add_argument("--rounds", type=int, default=DEFAULT_ROUNDS)
    parser.add_argument("--launches", type=int, default=DEFAULT_LAUNCHES)
    parser.add_argument("--block-size", type=int, default=DEFAULT_BLOCK_SIZE)
    parser.add_argument("--repeats", type=int, default=DEFAULT_REPEATS)
    parser.add_argument(
        "--benchmarks",
        nargs="+",
        choices=sorted(BENCHMARKS),
        default=list(BENCHMARKS),
    )
    parser.add_argument("--summary-from-json", default="")
    parser.add_argument("--json-out", default="")
    parser.add_argument("--markdown-out", default="")
    args = parser.parse_args()
    if not args.summary_from_json:
        try:
            validate_parameters(args.count, args.rounds, args.launches, args.block_size)
            if args.repeats < 1:
                raise ValueError("repeats must be positive")
        except ValueError as error:
            parser.error(str(error))
    return args


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

    if args.targets is None:
        args.targets = list(DEFAULT_TARGETS)

    results = []

    total_runs = len(args.targets) * len(args.benchmarks) * args.repeats
    run_index = 0

    for target_name in args.targets:
        target = TARGETS[target_name]
        for benchmark in args.benchmarks:
            spec = BENCHMARKS[benchmark]
            script_name, mode = spec.script, spec.mode
            for repeat in range(1, args.repeats + 1):
                run_index += 1
                print(
                    f"[{run_index}/{total_runs}] {target_name} {benchmark} "
                    f"repeat {repeat}/{args.repeats}",
                    flush=True,
                )
                executed_at = datetime.now(UTC).isoformat()
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
                    executed_at=executed_at,
                    repeat_index=repeat,
                )
                if result.parameters != RunParameters(args.count, args.rounds, args.launches, args.block_size):
                    raise RuntimeError("benchmark invocation did not match requested parameters")
                results.append(result)
                if args.json_out:
                    save_results(Path(args.json_out), results)
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
        save_results(out_path, results)
        print(f"\nWrote {out_path}")

    if args.markdown_out:
        out_path = Path(args.markdown_out)
        out_path.write_text(render_markdown(results, args))
        print(f"Wrote {out_path}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
