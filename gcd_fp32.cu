#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <cuda_runtime.h>

#define U24_MASK 0x00ffffffu
#define HYBRID_STEIN_FRONTEND_ITERS 8

#define CUDA_CHECK(call)                                                          \
    do {                                                                          \
        cudaError_t err__ = (call);                                               \
        if (err__ != cudaSuccess) {                                               \
            fprintf(stderr, "%s failed: %s\n", #call, cudaGetErrorString(err__)); \
            return 1;                                                             \
        }                                                                         \
    } while (0)

__device__ __forceinline__ float fp32_splice_exponent(float mantissa_src, float exponent_src) {
    uint32_t mantissa_bits = __float_as_uint(mantissa_src);
    uint32_t exponent_bits = __float_as_uint(exponent_src);
    uint32_t out_bits;

    // Bit-select: choose mantissa bits from `mantissa_src` where the mask has 1s,
    // and exponent/sign bits from `exponent_src` everywhere else.
    asm("lop3.b32 %0, %1, %2, 0x007fffff, 0xE4;"
        : "=r"(out_bits)
        : "r"(mantissa_bits), "r"(exponent_bits));

    return __uint_as_float(out_bits);
}

__device__ __forceinline__ uint32_t gcd_fp32_u24(float a_in, float b_in) {
    float a_fp = fminf(a_in, b_in);
    float b_fp = fmaxf(a_in, b_in);

    while (a_fp != 0.0f) {
        float t_fp = fp32_splice_exponent(a_fp, b_fp);
        t_fp = fabsf(b_fp - t_fp);
        b_fp = fmaxf(a_fp, t_fp);
        a_fp = fminf(a_fp, t_fp);
    }

    return __float2uint_rn(b_fp);
}

__device__ __forceinline__ uint32_t gcd_stein_u32(uint32_t u, uint32_t v) {
    if (u == 0u) {
        return v;
    }
    if (v == 0u) {
        return u;
    }

    uint32_t shift = (uint32_t)__ffs(u | v) - 1u;
    u >>= (uint32_t)__ffs(u) - 1u;

    do {
        v >>= (uint32_t)__ffs(v) - 1u;
        if (u > v) {
            uint32_t tmp = u;
            u = v;
            v = tmp;
        }
        v -= u;
    } while (v != 0u);

    return u << shift;
}

__device__ __forceinline__ uint32_t gcd_fp32_u32_hybrid(uint32_t u, uint32_t v) {
    if (u == 0u) {
        return v;
    }
    if (v == 0u) {
        return u;
    }

    uint32_t shift = (uint32_t)__ffs(u | v) - 1u;
    u >>= (uint32_t)__ffs(u) - 1u;
    v >>= (uint32_t)__ffs(v) - 1u;

    if (u <= U24_MASK && v <= U24_MASK) {
        return gcd_fp32_u24((float)u, (float)v) << shift;
    }

    for (uint32_t i = 0; i < HYBRID_STEIN_FRONTEND_ITERS; ++i) {
        if (u > v) {
            uint32_t tmp = u;
            u = v;
            v = tmp;
        }
        v -= u;
        if (v == 0u) {
            return u << shift;
        }
        v >>= (uint32_t)__ffs(v) - 1u;
    }

    return gcd_fp32_u24((float)u, (float)v) << shift;
}

__host__ __device__ __forceinline__ uint32_t next_u24(uint32_t x, uint32_t mul, uint32_t add) {
    return ((x * mul + add) & U24_MASK) | 1u;
}

__host__ __device__ __forceinline__ uint32_t next_u32(uint32_t x, uint32_t mul, uint32_t add) {
    return (x * mul + add) | 1u;
}

extern "C" __global__ void gcd_fp32_u24_kernel(const uint32_t *a,
                                               const uint32_t *b,
                                               uint32_t *out,
                                               uint32_t count,
                                               uint32_t rounds,
                                               int use_fixed_pair) {
    uint32_t idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= count) {
        return;
    }

    uint32_t x = a[idx];
    uint32_t y = b[idx];
    uint32_t acc = 0;

    for (uint32_t i = 0; i < rounds; ++i) {
        acc ^= gcd_fp32_u24((float)x, (float)y);
        if (!use_fixed_pair) {
            x = next_u24(x, 1664525u, 1013904223u);
            y = next_u24(y, 22695477u, 1u);
        }
    }

    out[idx] = acc;
}

extern "C" __global__ void gcd_stein_u24_kernel(const uint32_t *a,
                                                const uint32_t *b,
                                                uint32_t *out,
                                                uint32_t count,
                                                uint32_t rounds,
                                                int use_fixed_pair) {
    uint32_t idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= count) {
        return;
    }

    uint32_t x = a[idx];
    uint32_t y = b[idx];
    uint32_t acc = 0;

    for (uint32_t i = 0; i < rounds; ++i) {
        acc ^= gcd_stein_u32(x, y);
        if (!use_fixed_pair) {
            x = next_u24(x, 1664525u, 1013904223u);
            y = next_u24(y, 22695477u, 1u);
        }
    }

    out[idx] = acc;
}

extern "C" __global__ void gcd_fp32_u32_kernel(const uint32_t *a,
                                               const uint32_t *b,
                                               uint32_t *out,
                                               uint32_t count,
                                               uint32_t rounds,
                                               int use_fixed_pair) {
    uint32_t idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= count) {
        return;
    }

    uint32_t x = a[idx];
    uint32_t y = b[idx];
    uint32_t acc = 0;

    for (uint32_t i = 0; i < rounds; ++i) {
        acc ^= gcd_fp32_u32_hybrid(x, y);
        if (!use_fixed_pair) {
            x = next_u32(x, 1664525u, 1013904223u);
            y = next_u32(y, 22695477u, 1u);
        }
    }

    out[idx] = acc;
}

extern "C" __global__ void gcd_stein_u32_kernel(const uint32_t *a,
                                                const uint32_t *b,
                                                uint32_t *out,
                                                uint32_t count,
                                                uint32_t rounds,
                                                int use_fixed_pair) {
    uint32_t idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= count) {
        return;
    }

    uint32_t x = a[idx];
    uint32_t y = b[idx];
    uint32_t acc = 0;

    for (uint32_t i = 0; i < rounds; ++i) {
        acc ^= gcd_stein_u32(x, y);
        if (!use_fixed_pair) {
            x = next_u32(x, 1664525u, 1013904223u);
            y = next_u32(y, 22695477u, 1u);
        }
    }

    out[idx] = acc;
}

static uint32_t parse_u32_or_default(const char *text, uint32_t fallback) {
    if (text == NULL) {
        return fallback;
    }

    char *end = NULL;
    unsigned long value = strtoul(text, &end, 10);
    if (end == text || *end != '\0') {
        return fallback;
    }
    return (uint32_t)value;
}

static void fill_inputs(uint32_t *a,
                        uint32_t *b,
                        uint32_t count,
                        int use_u32,
                        int use_fixed_pair,
                        uint32_t fixed_a,
                        uint32_t fixed_b) {
    if (use_fixed_pair) {
        for (uint32_t i = 0; i < count; ++i) {
            a[i] = fixed_a;
            b[i] = fixed_b;
        }
        return;
    }

    uint32_t x = 1u;
    uint32_t y = 2u;

    for (uint32_t i = 0; i < count; ++i) {
        if (use_u32) {
            x = next_u32(x, 1664525u, 1013904223u);
            y = next_u32(y, 22695477u, 1u);
        } else {
            x = next_u24(x, 1664525u, 1013904223u);
            y = next_u24(y, 22695477u, 1u);
        }
        a[i] = x;
        b[i] = y;
    }
}

typedef enum {
    MODE_BOTH_U24 = 0,
    MODE_FP32_U24,
    MODE_STEIN_U24,
    MODE_BOTH_U32,
    MODE_FP32_U32,
    MODE_STEIN_U32,
} bench_mode;

static bench_mode parse_mode_or_default(const char *text) {
    if (text == NULL || strcmp(text, "both") == 0 || strcmp(text, "both_u24") == 0) {
        return MODE_BOTH_U24;
    }
    if (strcmp(text, "fp32") == 0 || strcmp(text, "fp32_u24") == 0) {
        return MODE_FP32_U24;
    }
    if (strcmp(text, "stein") == 0 || strcmp(text, "stein_u24") == 0) {
        return MODE_STEIN_U24;
    }
    if (strcmp(text, "both_u32") == 0) {
        return MODE_BOTH_U32;
    }
    if (strcmp(text, "fp32_u32") == 0) {
        return MODE_FP32_U32;
    }
    if (strcmp(text, "stein_u32") == 0) {
        return MODE_STEIN_U32;
    }
    return MODE_BOTH_U24;
}

static int mode_is_u32(bench_mode mode) {
    return mode == MODE_BOTH_U32 || mode == MODE_FP32_U32 || mode == MODE_STEIN_U32;
}

static int mode_runs_fp32(bench_mode mode) {
    return mode == MODE_BOTH_U24 || mode == MODE_FP32_U24 ||
           mode == MODE_BOTH_U32 || mode == MODE_FP32_U32;
}

static int mode_runs_stein(bench_mode mode) {
    return mode == MODE_BOTH_U24 || mode == MODE_STEIN_U24 ||
           mode == MODE_BOTH_U32 || mode == MODE_STEIN_U32;
}

static const char *mode_name(bench_mode mode) {
    switch (mode) {
    case MODE_BOTH_U24:
        return "both_u24";
    case MODE_FP32_U24:
        return "fp32_u24";
    case MODE_STEIN_U24:
        return "stein_u24";
    case MODE_BOTH_U32:
        return "both_u32";
    case MODE_FP32_U32:
        return "fp32_u32";
    case MODE_STEIN_U32:
        return "stein_u32";
    }
    return "both_u24";
}

static int run_benchmark(const char *name,
                         int use_fp32,
                         int use_u32,
                         const uint32_t *d_a,
                         const uint32_t *d_b,
                         uint32_t *d_out,
                         uint32_t *h_out,
                         uint32_t count,
                         uint32_t rounds,
                         uint32_t launches,
                         uint32_t block_size,
                         int use_fixed_pair) {
    cudaEvent_t start;
    cudaEvent_t stop;
    const uint32_t grid_size = (count + block_size - 1u) / block_size;

    CUDA_CHECK(cudaEventCreate(&start));
    CUDA_CHECK(cudaEventCreate(&stop));

    if (use_fp32 && !use_u32) {
        gcd_fp32_u24_kernel<<<grid_size, block_size>>>(d_a, d_b, d_out, count, rounds, use_fixed_pair);
    } else if (!use_fp32 && !use_u32) {
        gcd_stein_u24_kernel<<<grid_size, block_size>>>(d_a, d_b, d_out, count, rounds, use_fixed_pair);
    } else if (use_fp32) {
        gcd_fp32_u32_kernel<<<grid_size, block_size>>>(d_a, d_b, d_out, count, rounds, use_fixed_pair);
    } else {
        gcd_stein_u32_kernel<<<grid_size, block_size>>>(d_a, d_b, d_out, count, rounds, use_fixed_pair);
    }
    CUDA_CHECK(cudaGetLastError());
    CUDA_CHECK(cudaDeviceSynchronize());

    CUDA_CHECK(cudaEventRecord(start));
    for (uint32_t i = 0; i < launches; ++i) {
        if (use_fp32 && !use_u32) {
            gcd_fp32_u24_kernel<<<grid_size, block_size>>>(d_a, d_b, d_out, count, rounds, use_fixed_pair);
        } else if (!use_fp32 && !use_u32) {
            gcd_stein_u24_kernel<<<grid_size, block_size>>>(d_a, d_b, d_out, count, rounds, use_fixed_pair);
        } else if (use_fp32) {
            gcd_fp32_u32_kernel<<<grid_size, block_size>>>(d_a, d_b, d_out, count, rounds, use_fixed_pair);
        } else {
            gcd_stein_u32_kernel<<<grid_size, block_size>>>(d_a, d_b, d_out, count, rounds, use_fixed_pair);
        }
    }
    CUDA_CHECK(cudaEventRecord(stop));
    CUDA_CHECK(cudaGetLastError());
    CUDA_CHECK(cudaEventSynchronize(stop));

    float elapsed_ms = 0.0f;
    CUDA_CHECK(cudaEventElapsedTime(&elapsed_ms, start, stop));
    CUDA_CHECK(cudaMemcpy(h_out, d_out, (size_t)count * sizeof(uint32_t), cudaMemcpyDeviceToHost));

    uint32_t checksum = 0;
    for (uint32_t i = 0; i < count; ++i) {
        checksum ^= h_out[i];
    }

    double total_calls = (double)count * (double)rounds * (double)launches;
    double calls_per_second = total_calls / (elapsed_ms * 1.0e-3);
    double ns_per_call = (elapsed_ms * 1.0e6) / total_calls;

    printf("%s: elapsed_ms=%.3f calls=%.0f calls_per_second=%.3e ns_per_call=%.3f checksum=%08x\n",
           name,
           elapsed_ms,
           total_calls,
           calls_per_second,
           ns_per_call,
           checksum);

    CUDA_CHECK(cudaEventDestroy(start));
    CUDA_CHECK(cudaEventDestroy(stop));
    return 0;
}

int main(int argc, char **argv) {
    const bench_mode mode = parse_mode_or_default(argc > 1 ? argv[1] : NULL);
    const int use_u32 = mode_is_u32(mode);
    const uint32_t count = parse_u32_or_default(argc > 2 ? argv[2] : NULL, 1u << 20);
    const uint32_t rounds = parse_u32_or_default(argc > 3 ? argv[3] : NULL, 1024);
    const uint32_t launches = parse_u32_or_default(argc > 4 ? argv[4] : NULL, 20);
    const uint32_t block_size = parse_u32_or_default(argc > 5 ? argv[5] : NULL, 256);
    const int use_fixed_pair = argc > 7;
    const uint32_t fixed_a = parse_u32_or_default(argc > 6 ? argv[6] : NULL, 0);
    const uint32_t fixed_b = parse_u32_or_default(argc > 7 ? argv[7] : NULL, 0);

    uint32_t *h_a = (uint32_t *)malloc((size_t)count * sizeof(uint32_t));
    uint32_t *h_b = (uint32_t *)malloc((size_t)count * sizeof(uint32_t));
    uint32_t *h_out = (uint32_t *)malloc((size_t)count * sizeof(uint32_t));
    uint32_t *d_a = NULL;
    uint32_t *d_b = NULL;
    uint32_t *d_out = NULL;

    if (h_a == NULL || h_b == NULL || h_out == NULL) {
        fprintf(stderr, "host allocation failed\n");
        free(h_a);
        free(h_b);
        free(h_out);
        return 1;
    }

    fill_inputs(h_a, h_b, count, use_u32, use_fixed_pair, fixed_a, fixed_b);

    CUDA_CHECK(cudaMalloc(&d_a, (size_t)count * sizeof(uint32_t)));
    CUDA_CHECK(cudaMalloc(&d_b, (size_t)count * sizeof(uint32_t)));
    CUDA_CHECK(cudaMalloc(&d_out, (size_t)count * sizeof(uint32_t)));
    CUDA_CHECK(cudaMemcpy(d_a, h_a, (size_t)count * sizeof(uint32_t), cudaMemcpyHostToDevice));
    CUDA_CHECK(cudaMemcpy(d_b, h_b, (size_t)count * sizeof(uint32_t), cudaMemcpyHostToDevice));

    printf("mode=%s count=%u rounds=%u launches=%u block_size=%u",
           mode_name(mode),
           count,
           rounds,
           launches,
           block_size);
    if (use_fixed_pair) {
        printf(" fixed_pair=%u,%u", fixed_a, fixed_b);
    }
    putchar('\n');

    if (mode_runs_fp32(mode) &&
        run_benchmark(use_u32 ? "fp32_u32" : "fp32_u24",
                      1,
                      use_u32,
                      d_a,
                      d_b,
                      d_out,
                      h_out,
                      count,
                      rounds,
                      launches,
                      block_size,
                      use_fixed_pair) != 0) {
        return 1;
    }
    if (mode_runs_stein(mode) &&
        run_benchmark(use_u32 ? "stein_u32" : "stein_u24",
                      0,
                      use_u32,
                      d_a,
                      d_b,
                      d_out,
                      h_out,
                      count,
                      rounds,
                      launches,
                      block_size,
                      use_fixed_pair) != 0) {
        return 1;
    }

    CUDA_CHECK(cudaFree(d_a));
    CUDA_CHECK(cudaFree(d_b));
    CUDA_CHECK(cudaFree(d_out));
    free(h_a);
    free(h_b);
    free(h_out);
    return 0;
}
