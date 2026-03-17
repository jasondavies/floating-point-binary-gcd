# Benchmark Results

Generated from Modal runs on 2026-03-17 00:39 UTC.

Run parameters:

- `count=1048576`
- `rounds=1024`
- `launches=20`
- `block_size=256`
- `repeats=3`

Target configuration:

- `h100`: `gpu=H100!`, `-arch=sm_90`, `image=nvidia/cuda:12.8.1-devel-ubuntu22.04`
- `b200`: `gpu=B200`, `-arch=sm_100`, `image=nvidia/cuda:12.8.1-devel-ubuntu22.04`

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

Run URLs:

- `fp32_u24 run`: https://modal.com/apps/jasondavies/main/ap-l1PkW5CNDayCNtbjJCzmhx
- `fp32_u24 run`: https://modal.com/apps/jasondavies/main/ap-vRgYyLr17hgpp1GPXvWm3p
- `fp32_u24 run`: https://modal.com/apps/jasondavies/main/ap-mZP2PysWOZsDIJhgDYlCuZ
- `fp32_u32 run`: https://modal.com/apps/jasondavies/main/ap-9aRgdTkoIcd18YqAXCsFoF
- `fp32_u32 run`: https://modal.com/apps/jasondavies/main/ap-lDCX7raEtAaLQgRP8oqoEc
- `fp32_u32 run`: https://modal.com/apps/jasondavies/main/ap-ciO08Xdx7rj1JtOzCQX6YV
- `fp64_u53 run`: https://modal.com/apps/jasondavies/main/ap-32Gp7ilaX40hbKgPoOFDlL
- `fp64_u53 run`: https://modal.com/apps/jasondavies/main/ap-O2cOgmNZaRzOyxc3iCA2QK
- `fp64_u53 run`: https://modal.com/apps/jasondavies/main/ap-ydymJaCKYE85MtXJpqS1h4
- `fp64_u64 run`: https://modal.com/apps/jasondavies/main/ap-pCXUbSQp9GFmDh9UUcXKv3
- `fp64_u64 run`: https://modal.com/apps/jasondavies/main/ap-i7nclKiDGtGR1bztkuWZn3
- `fp64_u64 run`: https://modal.com/apps/jasondavies/main/ap-KPWFe9FT6NvvdGhAuzd1wb

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

Run URLs:

- `fp32_u24 run`: https://modal.com/apps/jasondavies/main/ap-GiSsJHFUpRTWQOVtP2lFs7
- `fp32_u24 run`: https://modal.com/apps/jasondavies/main/ap-j34t37IGauWVbaVNPXgmT9
- `fp32_u24 run`: https://modal.com/apps/jasondavies/main/ap-kNoCvaFyEcnmFXQBG9pyOM
- `fp32_u32 run`: https://modal.com/apps/jasondavies/main/ap-71p3UHAldEhXuufWW1kw41
- `fp32_u32 run`: https://modal.com/apps/jasondavies/main/ap-R8vh1c0JZEtSn0DTgiigsM
- `fp32_u32 run`: https://modal.com/apps/jasondavies/main/ap-53yIqSHpOPq3z9TF8xIh8M
- `fp64_u53 run`: https://modal.com/apps/jasondavies/main/ap-aIn6OW08b6imVzth3AEumz
- `fp64_u53 run`: https://modal.com/apps/jasondavies/main/ap-AwpcBON3frubB0Z4QhlMVP
- `fp64_u53 run`: https://modal.com/apps/jasondavies/main/ap-QYkh4HjlcmMABAm5GYSM4o
- `fp64_u64 run`: https://modal.com/apps/jasondavies/main/ap-796aR8LXulYopEWtoAt6rP
- `fp64_u64 run`: https://modal.com/apps/jasondavies/main/ap-KcMM9d7mgalTjI0KBSdLmB
- `fp64_u64 run`: https://modal.com/apps/jasondavies/main/ap-fpa8BY8Lsg6JVb3uIUnX2B
