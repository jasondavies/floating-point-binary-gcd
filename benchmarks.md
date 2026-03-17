# Benchmark Results

Generated from Modal runs on 2026-03-17 08:51 UTC.

Run parameters:

- `count=1048576`
- `rounds=1024`
- `launches=20`
- `block_size=256`
- `repeats=3`

Target configuration:

- `t4`: `gpu=T4`, `-arch=sm_75`, `image=nvidia/cuda:12.8.1-devel-ubuntu22.04`
- `h100`: `gpu=H100!`, `-arch=sm_90`, `image=nvidia/cuda:12.8.1-devel-ubuntu22.04`
- `b200`: `gpu=B200`, `-arch=sm_100`, `image=nvidia/cuda:12.8.1-devel-ubuntu22.04`

## Tesla T4

- Modal request: `T4`
- CUDA arch: `sm_75`
- CUDA base image: `nvidia/cuda:12.8.1-devel-ubuntu22.04`
- Driver: `580.95.05`
- Reported memory: `15360 MiB`

| workload | fp/hybrid ns/call | Stein ns/call | speedup vs Stein |
| --- | ---: | ---: | ---: |
| Random 24-bit inputs | 0.036 | 0.048 | 1.33x |
| Random 32-bit inputs | 0.050 | 0.062 | 1.24x |
| Random 53-bit inputs | 1.877 | 0.245 | 0.13x |
| Random 64-bit inputs | 1.751 | 0.297 | 0.17x |

## NVIDIA H100 80GB HBM3

- Modal request: `H100!`
- CUDA arch: `sm_90`
- CUDA base image: `nvidia/cuda:12.8.1-devel-ubuntu22.04`
- Driver: `580.95.05`
- Reported memory: `81559 MiB`

| workload | fp/hybrid ns/call | Stein ns/call | speedup vs Stein |
| --- | ---: | ---: | ---: |
| Random 24-bit inputs | 0.007 | 0.012 | 1.71x |
| Random 32-bit inputs | 0.010 | 0.015 | 1.50x |
| Random 53-bit inputs | 0.036 | 0.057 | 1.58x |
| Random 64-bit inputs | 0.048 | 0.067 | 1.40x |

## NVIDIA B200

- Modal request: `B200`
- CUDA arch: `sm_100`
- CUDA base image: `nvidia/cuda:12.8.1-devel-ubuntu22.04`
- Driver: `580.95.05`
- Reported memory: `183359 MiB`

| workload | fp/hybrid ns/call | Stein ns/call | speedup vs Stein |
| --- | ---: | ---: | ---: |
| Random 24-bit inputs | 0.006 | 0.011 | 1.83x |
| Random 32-bit inputs | 0.009 | 0.013 | 1.44x |
| Random 53-bit inputs | 0.033 | 0.051 | 1.55x |
| Random 64-bit inputs | 0.043 | 0.060 | 1.40x |
