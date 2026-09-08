#include <stdint.h>
#include <math.h>
#include <cuda_runtime.h>

#define U53_MASK ((1ull << 53) - 1ull)
// For odd 64-bit operands, each bundled Stein reduction at least halves their
// sum. Twelve reductions make the sum < 2^53, so both operands are exact in fp64.
#define HYBRID_STEIN_FRONTEND_ITERS_U64 12u

__host__ __device__ __forceinline__ uint64_t next_u53(uint64_t x, uint64_t mul, uint64_t add) {
    return ((x * mul + add) & U53_MASK) | 1ull;
}

__host__ __device__ __forceinline__ uint64_t next_u64(uint64_t x, uint64_t mul, uint64_t add) {
    return (x * mul + add) | 1ull;
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

struct BenchSpec {
    using Word = uint64_t;
    static constexpr const char *precision = "fp64";
    static constexpr unsigned exact_bits = 53;

    static void next(bool full, Word &x, Word &y) {
        if (full) {
            x = next_u64(x, 6364136223846793005ull, 1442695040888963407ull);
            y = next_u64(y, 2862933555777941757ull, 3037000493ull);
        } else {
            x = next_u53(x, 6364136223846793005ull, 1442695040888963407ull);
            y = next_u53(y, 2862933555777941757ull, 3037000493ull);
        }
    }

    static void launch(bool fp, bool full, uint32_t grid, uint32_t block,
                       const Word *a, const Word *b, Word *out,
                       uint32_t count, uint32_t rounds, bool fixed) {
        if (fp && !full) {
            gcd_fp64_u53_kernel<<<grid, block>>>(a, b, out, count, rounds, fixed);
        } else if (!fp && !full) {
            gcd_stein_u53_kernel<<<grid, block>>>(a, b, out, count, rounds, fixed);
        } else if (fp) {
            gcd_fp64_u64_kernel<<<grid, block>>>(a, b, out, count, rounds, fixed);
        } else {
            gcd_stein_u64_kernel<<<grid, block>>>(a, b, out, count, rounds, fixed);
        }
    }

    static void regressions(bool full, const Word *&a, const Word *&b, uint32_t &count) {
        static const uint64_t u53_a[] = {
            0ull, 0ull, 1ull, 25ull, U53_MASK, U53_MASK, 1ull << 52,
            1ull << 52, U53_MASK - 2ull, (1ull << 52) + 1ull,
        };
        static const uint64_t u53_b[] = {
            0ull, U53_MASK, U53_MASK, 18ull, U53_MASK - 2ull, 1ull,
            1ull << 51, (1ull << 52) - 1ull, 3ull, (1ull << 51) + 1ull,
        };
        static const uint64_t u64_a[] = {
            0ull,
            0ull,
            1ull,
            25ull,
            UINT64_MAX,
            UINT64_MAX,
            1ull << 63,
            1ull << 53,
            UINT64_C(17170434652806850245),
            UINT64_C(17000554516544968789),
            UINT64_C(0x8000000000000000),
            UINT64_C(0xfffffffffffffffe),
        };
        static const uint64_t u64_b[] = {
            0ull,
            UINT64_MAX,
            UINT64_MAX,
            18ull,
            UINT64_MAX - 2ull,
            1ull,
            1ull << 62,
            (1ull << 53) + 1ull,
            UINT64_C(11127183001224483315),
            UINT64_C(15683058166996929849),
            UINT64_C(0x4000000000000000),
            UINT64_C(0x7ffffffffffffffe),
        };
        static_assert(sizeof(u53_a) == sizeof(u53_b), "regression pair lengths differ");
        static_assert(sizeof(u64_a) == sizeof(u64_b), "regression pair lengths differ");
        a = full ? u64_a : u53_a;
        b = full ? u64_b : u53_b;
        count = full ? sizeof(u64_a) / sizeof(Word) : sizeof(u53_a) / sizeof(Word);
    }
};

#include "bench_host.cuh"
