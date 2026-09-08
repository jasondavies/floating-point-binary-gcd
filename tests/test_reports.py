import argparse
import contextlib
import io
import json
import tempfile
import unittest
from dataclasses import asdict, replace
from pathlib import Path
from unittest.mock import patch

import run_modal_repeats as report


SAMPLE = """gpu=Example GPU, 81920 MiB, 580.95.05
mode=both_u24 count=64 rounds=2 launches=1 block_size=32
validation=ok workload=u24 inputs=64 regression_cases=10
fp32_u24: elapsed_ms=1.000 calls=128 calls_per_second=1.280e+05 ns_per_call=7812.500 checksum=00000000
stein_u24: elapsed_ms=2.000 calls=128 calls_per_second=6.400e+04 ns_per_call=15625.000 checksum=00000000
"""


def result(text=SAMPLE):
    return report.parse_result(
        "fp32_u24", "both_u24", "h100", "H100!", "sm_90",
        report.CUDA_BASE_IMAGE_DEFAULT, text,
        executed_at="2026-07-24T00:00:00+00:00", repeat_index=1,
    )


class ReportTests(unittest.TestCase):
    def test_saved_parameters_override_report_cli_defaults(self):
        args = argparse.Namespace(targets=None, count=1048576, rounds=1024, repeats=3)
        rendered = report.render_markdown([result()], args)
        self.assertIn("count=64", rendered)
        self.assertIn("rounds=2", rendered)
        self.assertNotIn("1048576", rendered)
        self.assertIn("2026-07-24T00:00:00+00:00", rendered)
        self.assertIn("| 2.00x | 1 |", rendered)

    def test_json_roundtrip_preserves_exact_fixed_pair_and_metadata(self):
        pair = (0, 18446744073709551614)
        item = replace(result(), parameters=report.RunParameters(64, 2, 1, 32, pair))
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "runs.json"
            report.save_results(path, [item])
            self.assertEqual(report.load_results(path), [item])

    def test_fixed_input_headers_preserve_zero_and_large_integers(self):
        mode, parameters = report.parameters_from_output(
            "mode=both_u64 count=1 rounds=1 launches=1 block_size=1 "
            "fixed_pair=18446744073709551615,0"
        )
        self.assertEqual(mode, "both_u64")
        self.assertEqual(parameters.fixed_pair, (18446744073709551615, 0))

    def test_legacy_metadata_recovered_or_reported_unknown(self):
        item = asdict(result())
        for field in ("parameters", "executed_at", "repeat_index"):
            item.pop(field)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "legacy.json"
            path.write_text(json.dumps([item]))
            recovered = report.load_results(path)[0]
            self.assertEqual(recovered.parameters.count, 64)
            self.assertIsNone(recovered.executed_at)
            item["raw_output"] = ""
            path.write_text(json.dumps([item]))
            unknown = report.load_results(path)
            rendered = report.render_markdown(unknown, argparse.Namespace(targets=None))
            self.assertIn("count=unknown", rendered)
            self.assertIn("timestamp: unknown", rendered)

    def test_distinct_run_configurations_are_not_pooled(self):
        first = result()
        second = replace(first, parameters=report.RunParameters(128, 2, 1, 32))
        third = replace(first, cuda_arch="sm_80")
        self.assertEqual(len(list(report.result_groups([first, second, third]))), 3)

    def test_exact_gpu_models_and_requested_targets_stay_separate(self):
        first = result()
        second = replace(first, gpu_model="Different GPU")
        third = replace(first, target="b200")
        self.assertEqual(len(list(report.result_groups([first, second, third]))), 3)
        rendered = report.render_markdown([first, second, third], argparse.Namespace(targets=["b200"]))
        self.assertIn("Target: `b200`", rendered)
        self.assertNotIn("Target: `h100`", rendered)

    def test_invalid_live_output_rejected(self):
        for text in (
            SAMPLE.replace("validation=ok", "validation=failed"),
            SAMPLE.replace("workload=u24", "workload=u32"),
            SAMPLE.replace("mode=both_u24", "mode=both_u32"),
            SAMPLE.replace("fp32_u24:", "fp32_u32:"),
            SAMPLE.replace("calls=128", "calls=129"),
            SAMPLE.replace("checksum=00000000", "checksum=00000001", 1),
        ):
            with self.subTest(text=text), self.assertRaises(RuntimeError):
                result(text)

    def test_completed_runs_checkpointed_before_later_failure(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "runs.json"
            args = argparse.Namespace(
                summary_from_json="", targets=["h100"], benchmarks=["fp32_u24"],
                repeats=2, python="python3", count=64, rounds=2, launches=1,
                block_size=32, json_out=str(path), markdown_out="",
            )
            with patch.object(report, "parse_args", return_value=args), patch.object(
                report, "run_modal_bench", side_effect=[SAMPLE, RuntimeError("second run failed")]
            ), contextlib.redirect_stdout(io.StringIO()), self.assertRaisesRegex(RuntimeError, "second run"):
                report.main()
            saved = report.load_results(path)
            self.assertEqual(len(saved), 1)
            self.assertEqual(saved[0].repeat_index, 1)
            self.assertIsNotNone(saved[0].executed_at)

    def test_failed_atomic_replace_preserves_existing_checkpoint(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "runs.json"
            report.save_results(path, [result()])
            before = path.read_bytes()
            with patch.object(Path, "replace", side_effect=OSError("interrupted")), self.assertRaises(OSError):
                report.save_results(path, [])
            self.assertEqual(path.read_bytes(), before)
            self.assertEqual(list(Path(directory).iterdir()), [path])
