"""Optional local checks; these never start a Modal run."""

import contextlib
import importlib
import importlib.util
import io
import subprocess
import unittest
from unittest.mock import Mock, patch


@unittest.skipUnless(importlib.util.find_spec("modal"), "install requirements-modal.txt for Modal checks")
class ModalTests(unittest.TestCase):
    def test_both_entrypoints_load_and_preserve_fixed_pairs(self):
        for precision in ("fp32", "fp64"):
            with self.subTest(precision=precision):
                module = importlib.import_module(f"modal_{precision}_bench")
                replies = [
                    subprocess.CompletedProcess([], 0, "Example GPU, 1 MiB, driver\n", ""),
                    subprocess.CompletedProcess([], 0, "validation=ok\n", ""),
                ]
                with patch("modal_bench_common.subprocess.run", side_effect=replies) as call:
                    output = getattr(module, f"run_{precision}_bench").local(
                        count=1, rounds=1, launches=1, block_size=1,
                        use_fixed_pair=True, fixed_a=0, fixed_b=6,
                    )
                    self.assertEqual(call.call_args.args[0][-2:], ["0", "6"])
                    self.assertIn("validation=ok", output)

    def test_invalid_invocation_does_not_call_remote(self):
        from modal_bench_common import invoke
        for kwargs in (
            {"mode": "typo"}, {"mode": "both_u32", "count": 0},
            {"mode": "both_u24", "use_fixed_pair": True, "fixed_a": 16777216},
            {"mode": "both_u64", "use_fixed_pair": True, "fixed_b": -1},
        ):
            remote = Mock()
            precision = "fp64" if kwargs["mode"] == "both_u64" else "fp32"
            with self.subTest(kwargs=kwargs), self.assertRaises(ValueError):
                invoke(remote, precision, **kwargs)
            remote.remote.assert_not_called()

    def test_uint64_max_survives_local_entrypoint(self):
        from modal_bench_common import invoke
        remote = Mock()
        with contextlib.redirect_stdout(io.StringIO()):
            invoke(remote, "fp64", "both_u64", use_fixed_pair=True,
                   fixed_a=18446744073709551615, fixed_b=0)
        self.assertEqual(remote.remote.call_args.kwargs["fixed_a"], 18446744073709551615)
        self.assertEqual(remote.remote.call_args.kwargs["fixed_b"], 0)
