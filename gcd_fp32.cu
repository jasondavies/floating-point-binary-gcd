#include <stdint.h>
#include <math.h>
#include <cuda_runtime.h>

#define U24_MASK 0x00ffffffu
// For odd 32-bit operands, each bundled Stein reduction at least halves their
// sum. Nine reductions make the sum < 2^24, so both operands are exact in fp32.
#define HYBRID_STEIN_FRONTEND_ITERS 9u

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

struct BenchSpec {
    using Word = uint32_t;
    static constexpr const char *precision = "fp32";
    static constexpr unsigned exact_bits = 24;

    static void next(bool full, Word &x, Word &y) {
        if (full) {
            x = next_u32(x, 1664525u, 1013904223u);
            y = next_u32(y, 22695477u, 1u);
        } else {
            x = next_u24(x, 1664525u, 1013904223u);
            y = next_u24(y, 22695477u, 1u);
        }
    }

    static void launch(bool fp, bool full, uint32_t grid, uint32_t block,
                       const Word *a, const Word *b, Word *out,
                       uint32_t count, uint32_t rounds, bool fixed) {
        if (fp && !full) {
            gcd_fp32_u24_kernel<<<grid, block>>>(a, b, out, count, rounds, fixed);
        } else if (!fp && !full) {
            gcd_stein_u24_kernel<<<grid, block>>>(a, b, out, count, rounds, fixed);
        } else if (fp) {
            gcd_fp32_u32_kernel<<<grid, block>>>(a, b, out, count, rounds, fixed);
        } else {
            gcd_stein_u32_kernel<<<grid, block>>>(a, b, out, count, rounds, fixed);
        }
    }

    static void regressions(bool full, const Word *&a, const Word *&b, uint32_t &count) {
        static const uint32_t u24_a[] = {
            0u, 0u, 1u, 25u, U24_MASK, U24_MASK, 1u << 23, 1u << 23,
            0x00fffffdu, 0x00800001u,
        };
        static const uint32_t u24_b[] = {
            0u, U24_MASK, U24_MASK, 18u, U24_MASK - 2u, 1u, 1u << 22,
            (1u << 23) - 1u, 3u, 0x007fffffu,
        };
        static const uint32_t u32_a[] = {
            0u, 0u, 1u, 25u, UINT32_MAX, UINT32_MAX, 1u << 31, 1u << 24,
            3937952157u, 4026625921u, 0x80000000u, 0xfffffffeu,
        };
        static const uint32_t u32_b[] = {
            0u, UINT32_MAX, UINT32_MAX, 18u, UINT32_MAX - 2u, 1u, 1u << 30,
            (1u << 24) + 1u, 3591134307u, 2667281535u, 0x40000000u,
            0x7ffffffeu,
        };
        static_assert(sizeof(u24_a) == sizeof(u24_b), "regression pair lengths differ");
        static_assert(sizeof(u32_a) == sizeof(u32_b), "regression pair lengths differ");
        a = full ? u32_a : u24_a;
        b = full ? u32_b : u24_b;
        count = full ? sizeof(u32_a) / sizeof(Word) : sizeof(u24_a) / sizeof(Word);
    }
};

#include "bench_host.cuh"
