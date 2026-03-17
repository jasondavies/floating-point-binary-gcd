#include <inttypes.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <cuda_runtime.h>

#define U53_MASK ((1ull << 53) - 1ull)
#define HYBRID_STEIN_FRONTEND_ITERS_U64 11u

#define CUDA_CHECK(call)                                                          \
    do {                                                                          \
        cudaError_t err__ = (call);                                               \
        if (err__ != cudaSuccess) {                                               \
            fprintf(stderr, "%s failed: %s\n", #call, cudaGetErrorString(err__)); \
            return 1;                                                             \
        }                                                                         \
    } while (0)

typedef enum {
    MODE_BOTH_U53 = 0,
    MODE_FP64_U53,
    MODE_STEIN_U53,
    MODE_BOTH_U64,
    MODE_FP64_U64,
    MODE_STEIN_U64,
} bench_mode;

static bench_mode parse_mode_or_default(const char *text) {
    if (text == NULL || strcmp(text, "both") == 0 || strcmp(text, "both_u53") == 0) {
        return MODE_BOTH_U53;
    }
    if (strcmp(text, "fp64") == 0 || strcmp(text, "fp64_u53") == 0) {
        return MODE_FP64_U53;
    }
    if (strcmp(text, "stein") == 0 || strcmp(text, "stein_u53") == 0) {
        return MODE_STEIN_U53;
    }
    if (strcmp(text, "both_u64") == 0) {
        return MODE_BOTH_U64;
    }
    if (strcmp(text, "fp64_u64") == 0) {
        return MODE_FP64_U64;
    }
    if (strcmp(text, "stein_u64") == 0) {
        return MODE_STEIN_U64;
    }
    return MODE_BOTH_U53;
}

static int mode_is_u64(bench_mode mode) {
    return mode == MODE_BOTH_U64 || mode == MODE_FP64_U64 || mode == MODE_STEIN_U64;
}

static int mode_runs_fp64(bench_mode mode) {
    return mode == MODE_BOTH_U53 || mode == MODE_FP64_U53 ||
           mode == MODE_BOTH_U64 || mode == MODE_FP64_U64;
}

static int mode_runs_stein(bench_mode mode) {
    return mode == MODE_BOTH_U53 || mode == MODE_STEIN_U53 ||
           mode == MODE_BOTH_U64 || mode == MODE_STEIN_U64;
}

static const char *mode_name(bench_mode mode) {
    switch (mode) {
    case MODE_BOTH_U53:
        return "both_u53";
    case MODE_FP64_U53:
        return "fp64_u53";
    case MODE_STEIN_U53:
        return "stein_u53";
    case MODE_BOTH_U64:
        return "both_u64";
    case MODE_FP64_U64:
        return "fp64_u64";
    case MODE_STEIN_U64:
        return "stein_u64";
    }
    return "both_u53";
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

static uint64_t parse_u64_or_default(const char *text, uint64_t fallback) {
    if (text == NULL) {
        return fallback;
    }

    char *end = NULL;
    unsigned long long value = strtoull(text, &end, 10);
    if (end == text || *end != '\0') {
        return fallback;
    }
    return (uint64_t)value;
}

__host__ __device__ __forceinline__ uint64_t next_u53(uint64_t x, uint64_t mul, uint64_t add) {
    return ((x * mul + add) & U53_MASK) | 1ull;
}

__host__ __device__ __forceinline__ uint64_t next_u64(uint64_t x, uint64_t mul, uint64_t add) {
    return (x * mul + add) | 1ull;
}

static void fill_inputs(uint64_t *a,
                        uint64_t *b,
                        uint32_t count,
                        int use_u64,
                        int use_fixed_pair,
                        uint64_t fixed_a,
                        uint64_t fixed_b) {
    if (use_fixed_pair) {
        if (!use_u64) {
            fixed_a = (fixed_a & U53_MASK) | 1ull;
            fixed_b = (fixed_b & U53_MASK) | 1ull;
        }
        for (uint32_t i = 0; i < count; ++i) {
            a[i] = fixed_a;
            b[i] = fixed_b;
        }
        return;
    }

    uint64_t x = 1ull;
    uint64_t y = 2ull;

    for (uint32_t i = 0; i < count; ++i) {
        if (use_u64) {
            x = next_u64(x, 6364136223846793005ull, 1442695040888963407ull);
            y = next_u64(y, 2862933555777941757ull, 3037000493ull);
        } else {
            x = next_u53(x, 6364136223846793005ull, 1442695040888963407ull);
            y = next_u53(y, 2862933555777941757ull, 3037000493ull);
        }
        a[i] = x;
        b[i] = y;
    }
}

__device__ __forceinline__ double fp64_splice_exponent(double mantissa_src, double exponent_src) {
    unsigned long long a_bits = (unsigned long long)__double_as_longlong(mantissa_src);
    unsigned long long b_bits = (unsigned long long)__double_as_longlong(exponent_src);
    uint32_t a_lo = (uint32_t)a_bits;
    uint32_t a_hi = (uint32_t)(a_bits >> 32);
    uint32_t b_hi = (uint32_t)(b_bits >> 32);
    uint32_t out_hi;
    unsigned long long out_bits;

    // Low 32 mantissa bits come directly from `mantissa_src`.
    // High word keeps the low 20 mantissa bits from `mantissa_src`
    // and the top 12 sign/exponent bits from `exponent_src`.
    asm("lop3.b32 %0, %1, %2, 0x000fffff, 0xE4;"
        : "=r"(out_hi)
        : "r"(a_hi), "r"(b_hi));

    out_bits = ((unsigned long long)out_hi << 32) | (unsigned long long)a_lo;
    return __longlong_as_double((long long)out_bits);
}

__device__ __forceinline__ uint64_t gcd_fp64_u53(double a_in, double b_in) {
    double a_fp = fmin(a_in, b_in);
    double b_fp = fmax(a_in, b_in);

    while (a_fp != 0.0) {
        double t_fp = fp64_splice_exponent(a_fp, b_fp);
        t_fp = fabs(b_fp - t_fp);
        b_fp = fmax(a_fp, t_fp);
        a_fp = fmin(a_fp, t_fp);
    }

    return __double2ull_rn(b_fp);
}

__device__ __forceinline__ uint64_t gcd_stein_u64(uint64_t u, uint64_t v) {
    if (u == 0ull) {
        return v;
    }
    if (v == 0ull) {
        return u;
    }

    uint32_t shift = (uint32_t)__ffsll((long long)(u | v)) - 1u;
    u >>= (uint32_t)__ffsll((long long)u) - 1u;

    do {
        v >>= (uint32_t)__ffsll((long long)v) - 1u;
        if (u > v) {
            uint64_t tmp = u;
            u = v;
            v = tmp;
        }
        v -= u;
    } while (v != 0ull);

    return u << shift;
}

__device__ __forceinline__ uint64_t gcd_fp64_u64_hybrid(uint64_t u, uint64_t v) {
    if (u == 0ull) {
        return v;
    }
    if (v == 0ull) {
        return u;
    }

    uint32_t shift = (uint32_t)__ffsll((long long)(u | v)) - 1u;
    u >>= (uint32_t)__ffsll((long long)u) - 1u;
    v >>= (uint32_t)__ffsll((long long)v) - 1u;

    if (u <= U53_MASK && v <= U53_MASK) {
        return gcd_fp64_u53((double)u, (double)v) << shift;
    }

    for (uint32_t i = 0; i < HYBRID_STEIN_FRONTEND_ITERS_U64; ++i) {
        if (u > v) {
            uint64_t tmp = u;
            u = v;
            v = tmp;
        }
        v -= u;
        if (v == 0ull) {
            return u << shift;
        }
        v >>= (uint32_t)__ffsll((long long)v) - 1u;
    }

    return gcd_fp64_u53((double)u, (double)v) << shift;
}

extern "C" __global__ void gcd_fp64_u53_kernel(const uint64_t *a,
                                               const uint64_t *b,
                                               uint64_t *out,
                                               uint32_t count,
                                               uint32_t rounds,
                                               int use_fixed_pair) {
    uint32_t idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= count) {
        return;
    }

    uint64_t x = a[idx];
    uint64_t y = b[idx];
    uint64_t acc = 0ull;

    for (uint32_t i = 0; i < rounds; ++i) {
        acc ^= gcd_fp64_u53((double)x, (double)y);
        if (!use_fixed_pair) {
            x = next_u53(x, 6364136223846793005ull, 1442695040888963407ull);
            y = next_u53(y, 2862933555777941757ull, 3037000493ull);
        }
    }

    out[idx] = acc;
}

extern "C" __global__ void gcd_fp64_u64_kernel(const uint64_t *a,
                                               const uint64_t *b,
                                               uint64_t *out,
                                               uint32_t count,
                                               uint32_t rounds,
                                               int use_fixed_pair) {
    uint32_t idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= count) {
        return;
    }

    uint64_t x = a[idx];
    uint64_t y = b[idx];
    uint64_t acc = 0ull;

    for (uint32_t i = 0; i < rounds; ++i) {
        acc ^= gcd_fp64_u64_hybrid(x, y);
        if (!use_fixed_pair) {
            x = next_u64(x, 6364136223846793005ull, 1442695040888963407ull);
            y = next_u64(y, 2862933555777941757ull, 3037000493ull);
        }
    }

    out[idx] = acc;
}

extern "C" __global__ void gcd_stein_u53_kernel(const uint64_t *a,
                                                const uint64_t *b,
                                                uint64_t *out,
                                                uint32_t count,
                                                uint32_t rounds,
                                                int use_fixed_pair) {
    uint32_t idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= count) {
        return;
    }

    uint64_t x = a[idx];
    uint64_t y = b[idx];
    uint64_t acc = 0ull;

    for (uint32_t i = 0; i < rounds; ++i) {
        acc ^= gcd_stein_u64(x, y);
        if (!use_fixed_pair) {
            x = next_u53(x, 6364136223846793005ull, 1442695040888963407ull);
            y = next_u53(y, 2862933555777941757ull, 3037000493ull);
        }
    }

    out[idx] = acc;
}

extern "C" __global__ void gcd_stein_u64_kernel(const uint64_t *a,
                                                const uint64_t *b,
                                                uint64_t *out,
                                                uint32_t count,
                                                uint32_t rounds,
                                                int use_fixed_pair) {
    uint32_t idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= count) {
        return;
    }

    uint64_t x = a[idx];
    uint64_t y = b[idx];
    uint64_t acc = 0ull;

    for (uint32_t i = 0; i < rounds; ++i) {
        acc ^= gcd_stein_u64(x, y);
        if (!use_fixed_pair) {
            x = next_u64(x, 6364136223846793005ull, 1442695040888963407ull);
            y = next_u64(y, 2862933555777941757ull, 3037000493ull);
        }
    }

    out[idx] = acc;
}

static int run_benchmark(const char *name,
                         int use_fp64,
                         int use_u64,
                         const uint64_t *d_a,
                         const uint64_t *d_b,
                         uint64_t *d_out,
                         uint64_t *h_out,
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

    if (use_fp64 && !use_u64) {
        gcd_fp64_u53_kernel<<<grid_size, block_size>>>(d_a, d_b, d_out, count, rounds, use_fixed_pair);
    } else if (!use_fp64 && !use_u64) {
        gcd_stein_u53_kernel<<<grid_size, block_size>>>(d_a, d_b, d_out, count, rounds, use_fixed_pair);
    } else if (use_fp64) {
        gcd_fp64_u64_kernel<<<grid_size, block_size>>>(d_a, d_b, d_out, count, rounds, use_fixed_pair);
    } else {
        gcd_stein_u64_kernel<<<grid_size, block_size>>>(d_a, d_b, d_out, count, rounds, use_fixed_pair);
    }
    CUDA_CHECK(cudaGetLastError());
    CUDA_CHECK(cudaDeviceSynchronize());

    CUDA_CHECK(cudaEventRecord(start));
    for (uint32_t i = 0; i < launches; ++i) {
        if (use_fp64 && !use_u64) {
            gcd_fp64_u53_kernel<<<grid_size, block_size>>>(d_a, d_b, d_out, count, rounds, use_fixed_pair);
        } else if (!use_fp64 && !use_u64) {
            gcd_stein_u53_kernel<<<grid_size, block_size>>>(d_a, d_b, d_out, count, rounds, use_fixed_pair);
        } else if (use_fp64) {
            gcd_fp64_u64_kernel<<<grid_size, block_size>>>(d_a, d_b, d_out, count, rounds, use_fixed_pair);
        } else {
            gcd_stein_u64_kernel<<<grid_size, block_size>>>(d_a, d_b, d_out, count, rounds, use_fixed_pair);
        }
    }
    CUDA_CHECK(cudaEventRecord(stop));
    CUDA_CHECK(cudaGetLastError());
    CUDA_CHECK(cudaEventSynchronize(stop));

    float elapsed_ms = 0.0f;
    CUDA_CHECK(cudaEventElapsedTime(&elapsed_ms, start, stop));
    CUDA_CHECK(cudaMemcpy(h_out, d_out, (size_t)count * sizeof(uint64_t), cudaMemcpyDeviceToHost));

    uint64_t checksum = 0ull;
    for (uint32_t i = 0; i < count; ++i) {
        checksum ^= h_out[i];
    }

    double total_calls = (double)count * (double)rounds * (double)launches;
    double calls_per_second = total_calls / (elapsed_ms * 1.0e-3);
    double ns_per_call = (elapsed_ms * 1.0e6) / total_calls;

    printf("%s: elapsed_ms=%.3f calls=%.0f calls_per_second=%.3e ns_per_call=%.3f checksum=%016" PRIx64 "\n",
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
    const int use_u64 = mode_is_u64(mode);
    const uint32_t count = parse_u32_or_default(argc > 2 ? argv[2] : NULL, 1u << 20);
    const uint32_t rounds = parse_u32_or_default(argc > 3 ? argv[3] : NULL, 1024);
    const uint32_t launches = parse_u32_or_default(argc > 4 ? argv[4] : NULL, 20);
    const uint32_t block_size = parse_u32_or_default(argc > 5 ? argv[5] : NULL, 256);
    const int use_fixed_pair = argc > 7;
    const uint64_t fixed_a = parse_u64_or_default(argc > 6 ? argv[6] : NULL, 0ull);
    const uint64_t fixed_b = parse_u64_or_default(argc > 7 ? argv[7] : NULL, 0ull);

    uint64_t *h_a = (uint64_t *)malloc((size_t)count * sizeof(uint64_t));
    uint64_t *h_b = (uint64_t *)malloc((size_t)count * sizeof(uint64_t));
    uint64_t *h_out = (uint64_t *)malloc((size_t)count * sizeof(uint64_t));
    uint64_t *d_a = NULL;
    uint64_t *d_b = NULL;
    uint64_t *d_out = NULL;

    if (h_a == NULL || h_b == NULL || h_out == NULL) {
        fprintf(stderr, "host allocation failed\n");
        free(h_a);
        free(h_b);
        free(h_out);
        return 1;
    }

    fill_inputs(h_a, h_b, count, use_u64, use_fixed_pair, fixed_a, fixed_b);

    CUDA_CHECK(cudaMalloc(&d_a, (size_t)count * sizeof(uint64_t)));
    CUDA_CHECK(cudaMalloc(&d_b, (size_t)count * sizeof(uint64_t)));
    CUDA_CHECK(cudaMalloc(&d_out, (size_t)count * sizeof(uint64_t)));
    CUDA_CHECK(cudaMemcpy(d_a, h_a, (size_t)count * sizeof(uint64_t), cudaMemcpyHostToDevice));
    CUDA_CHECK(cudaMemcpy(d_b, h_b, (size_t)count * sizeof(uint64_t), cudaMemcpyHostToDevice));

    printf("mode=%s count=%u rounds=%u launches=%u block_size=%u",
           mode_name(mode),
           count,
           rounds,
           launches,
           block_size);
    if (use_fixed_pair) {
        printf(" fixed_pair=%" PRIu64 ",%" PRIu64, fixed_a, fixed_b);
    }
    putchar('\n');

    if (mode_runs_fp64(mode) &&
        run_benchmark(use_u64 ? "fp64_u64" : "fp64_u53",
                      1,
                      use_u64,
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
        run_benchmark(use_u64 ? "stein_u64" : "stein_u53",
                      0,
                      use_u64,
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
