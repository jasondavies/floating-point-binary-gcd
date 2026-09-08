"""Modal entrypoint for fp64; shared build and execution live in modal_bench_common."""

from bench_config import DEFAULT_COUNT, DEFAULT_ROUNDS, DEFAULT_LAUNCHES, DEFAULT_BLOCK_SIZE
from modal_bench_common import create_app, invoke

app, run_fp64_bench = create_app("fp64")


@app.local_entrypoint()
def main(
    mode: str = "both_u53",
    count: int = DEFAULT_COUNT,
    rounds: int = DEFAULT_ROUNDS,
    launches: int = DEFAULT_LAUNCHES,
    block_size: int = DEFAULT_BLOCK_SIZE,
    use_fixed_pair: bool = False,
    fixed_a: int = 0,
    fixed_b: int = 0,
) -> None:
    invoke(run_fp64_bench, "fp64", **locals())
