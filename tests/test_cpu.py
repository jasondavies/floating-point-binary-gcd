import re
import subprocess
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def run(tool, *args):
    return subprocess.run(
        [str(ROOT / tool), *map(str, args)], text=True, capture_output=True, timeout=30,
    )


def steps(a, b):
    """Independent forward integer model for the reverse search."""
    count = 0
    a, b = max(a, b), min(a, b)
    while b:
        a = abs(a - (b << (a.bit_length() - b.bit_length())))
        a, b = max(a, b), min(a, b)
        count += 1
    return count


class CPUTests(unittest.TestCase):
    def test_fp32_exhaustive_small_box(self):
        completed = run("gcd_fp32", "--scan", 255)
        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertIn("scan ok", completed.stdout)

    def test_reverse_table_matches_forward_exhaustion(self):
        completed = run("exact_threshold_search", "table", 8, 4, 2, 1000000)
        self.assertEqual(completed.returncode, 0, completed.stderr)
        for line in completed.stdout.splitlines():
            k, maximum, a, b = map(int, re.fullmatch(
                r"k=(\d+) max_steps=(\d+) witness=(\d+),(\d+)", line,
            ).groups())
            limit = (1 << k) - 1
            forward = max(steps(x, y) for x in range(1, limit + 1) for y in range(1, x + 1))
            self.assertEqual(maximum, forward)
            self.assertEqual(steps(a, b), maximum)

    def test_threshold_and_pareto_modes(self):
        for mode in ("search", "parallel"):
            for target, found in ((12, 1), (13, 0)):
                args = (8, target, 1000000) if mode == "search" else (8, target, 3, 2, 1000000)
                completed = run("exact_threshold_search", mode, *args)
                self.assertEqual(completed.returncode, 0, completed.stderr)
                self.assertIn(f"found={found}", completed.stdout)
        completed = run("exact_threshold_search", "pareto", 8, 3, 2, 1000000)
        self.assertEqual(completed.returncode, 0, completed.stderr)
        pairs = re.findall(r"witness=(\d+),(\d+)", completed.stdout)
        self.assertTrue(pairs)
        for a, b in pairs:
            self.assertEqual(steps(int(a), int(b)), 12)

    def test_visit_budget_exhaustion_fails(self):
        for args in (("search", 8, 12, 0), ("parallel", 8, 12, 0, 1, 0),
                     ("max", 8, 3, 1, 0), ("table", 8, 3, 1, 0),
                     ("pareto", 8, 3, 1, 0), ("pareto_table", 8, 3, 1, 0)):
            with self.subTest(args=args):
                completed = run("exact_threshold_search", *args)
                self.assertEqual(completed.returncode, 1)
                self.assertIn("visit_limit_hit=1", completed.stdout)

    def test_invalid_arguments_rejected(self):
        for args in (
            ("frontier", "3x", 1), ("frontier", 3, "-1"),
            ("max", 4, 2, 1, "garbage"), ("max", 4, 2, 0),
            ("table", 129, 2), ("search", 8, 12, "18446744073709551616"),
            ("search", 8, 1, 100, 0, 1, 0, 2),
            ("search", 8, 2, 100, 0, 256, 1, 0),
            ("search", 8, 2, 100, 0, 1, 2, 0),
            ("search", 8, 2, 100, 0, 0, 0, 0),
        ):
            with self.subTest(args=args):
                self.assertEqual(run("exact_threshold_search", *args).returncode, 2)
        for value in ("+1", "-1", "1x", "16777216"):
            self.assertNotEqual(run("gcd_fp32", value, 1).returncode, 0)
