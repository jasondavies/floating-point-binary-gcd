#include <inttypes.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
    uint32_t steps;
    uint32_t gcd;
} gcd_u24_run;

typedef enum {
    FP32_RUN_OK = 0,
    FP32_RUN_NOT_INTEGER,
    FP32_RUN_STEP_LIMIT,
} fp32_run_status;

typedef struct {
    fp32_run_status status;
    uint32_t steps;
    float a_fp;
    float b_fp;
    uint32_t gcd;
} fp32_run;

static uint32_t float_to_bits(float value) {
    uint32_t bits = 0;
    memcpy(&bits, &value, sizeof(bits));
    return bits;
}

static float bits_to_float(uint32_t bits) {
    float value = 0.0f;
    memcpy(&value, &bits, sizeof(value));
    return value;
}

static void swap_u32(uint32_t *lhs, uint32_t *rhs) {
    uint32_t tmp = *lhs;
    *lhs = *rhs;
    *rhs = tmp;
}

static void swap_f32(float *lhs, float *rhs) {
    float tmp = *lhs;
    *lhs = *rhs;
    *rhs = tmp;
}

static gcd_u24_run gcd_u24_reference(uint32_t a, uint32_t b) {
    gcd_u24_run out = {0, 0};

    if (a < b) {
        swap_u32(&a, &b);
    }

    while (b != 0) {
        uint32_t a_bits = 32u - (uint32_t)__builtin_clz(a);
        uint32_t b_bits = 32u - (uint32_t)__builtin_clz(b);
        uint32_t shift = a_bits - b_bits;
        uint32_t aligned = b << shift;
        a = (a >= aligned) ? (a - aligned) : (aligned - a);
        if (a < b) {
            swap_u32(&a, &b);
        }
        out.steps += 1;
    }

    out.gcd = a;
    return out;
}

static int u24_exact_in_float(float value, uint32_t *out) {
    if (!(value >= 0.0f) || value > 16777215.0f) {
        return 0;
    }

    uint32_t as_u32 = (uint32_t)value;
    if ((float)as_u32 != value) {
        return 0;
    }

    *out = as_u32;
    return 1;
}

static float fp32_repack_mantissa_with_exponent(float mantissa_src, float exponent_src) {
    uint32_t mantissa_bits = float_to_bits(mantissa_src);
    uint32_t exponent_bits = float_to_bits(exponent_src);
    uint32_t out_bits = (mantissa_bits & 0x007fffffu) | (exponent_bits & 0x7f800000u);
    return bits_to_float(out_bits);
}

static fp32_run gcd_u24_fp32_proposed(uint32_t a, uint32_t b, uint32_t step_limit) {
    fp32_run out = {FP32_RUN_OK, 0, 0.0f, 0.0f, 0};
    float a_fp = (float)a;
    float b_fp = (float)b;

    if (a_fp > b_fp) {
        swap_f32(&a_fp, &b_fp);
    }

    while (a_fp != 0.0f && b_fp != 0.0f) {
        float t_fp = fp32_repack_mantissa_with_exponent(a_fp, b_fp);

        b_fp -= t_fp;
        b_fp = fabsf(b_fp);

        if (a_fp >= b_fp) {
            swap_f32(&a_fp, &b_fp);
        }

        out.steps += 1;
        if (out.steps >= step_limit) {
            out.status = FP32_RUN_STEP_LIMIT;
            out.a_fp = a_fp;
            out.b_fp = b_fp;
            return out;
        }
    }

    out.a_fp = a_fp;
    out.b_fp = b_fp;

    if (!u24_exact_in_float((a_fp != 0.0f) ? a_fp : b_fp, &out.gcd)) {
        out.status = FP32_RUN_NOT_INTEGER;
        return out;
    }

    return out;
}

static const char *fp32_status_name(fp32_run_status status) {
    switch (status) {
    case FP32_RUN_OK:
        return "ok";
    case FP32_RUN_NOT_INTEGER:
        return "not-integer";
    case FP32_RUN_STEP_LIMIT:
        return "step-limit";
    }
    return "unknown";
}

static void usage(const char *prog) {
    fprintf(stderr,
            "usage:\n"
            "  %s <a> <b>\n"
            "  %s --scan <limit>\n",
            prog,
            prog);
}

static int parse_u24(const char *text, uint32_t *out) {
    char *end = NULL;
    unsigned long value = strtoul(text, &end, 10);
    if (end == text || *end != '\0' || value > 16777215ul) {
        return 0;
    }
    *out = (uint32_t)value;
    return 1;
}

static int run_single(uint32_t a, uint32_t b) {
    gcd_u24_run ref = gcd_u24_reference(a, b);
    fp32_run test = gcd_u24_fp32_proposed(a, b, 1000000);

    printf("input=%" PRIu32 ",%" PRIu32 "\n", a, b);
    printf("reference: steps=%" PRIu32 " gcd=%" PRIu32 "\n", ref.steps, ref.gcd);
    printf("fp32: status=%s steps=%" PRIu32 " final_a=%g final_b=%g",
           fp32_status_name(test.status),
           test.steps,
           test.a_fp,
           test.b_fp);
    if (test.status == FP32_RUN_OK) {
        printf(" gcd=%" PRIu32, test.gcd);
    }
    putchar('\n');

    if (test.status != FP32_RUN_OK ||
        test.gcd != ref.gcd ||
        test.steps != ref.steps) {
        return 1;
    }
    return 0;
}

static int run_scan(uint32_t limit) {
    for (uint32_t a = 1; a <= limit; ++a) {
        for (uint32_t b = 1; b <= limit; ++b) {
            gcd_u24_run ref = gcd_u24_reference(a, b);
            fp32_run test = gcd_u24_fp32_proposed(a, b, 1000000);
            if (test.status != FP32_RUN_OK ||
                test.gcd != ref.gcd ||
                test.steps != ref.steps) {
                printf("first mismatch at input=%" PRIu32 ",%" PRIu32 "\n", a, b);
                printf("reference: steps=%" PRIu32 " gcd=%" PRIu32 "\n", ref.steps, ref.gcd);
                printf("fp32: status=%s steps=%" PRIu32 " final_a=%g final_b=%g",
                       fp32_status_name(test.status),
                       test.steps,
                       test.a_fp,
                       test.b_fp);
                if (test.status == FP32_RUN_OK) {
                    printf(" gcd=%" PRIu32, test.gcd);
                }
                putchar('\n');
                return 1;
            }
        }
    }

    printf("scan ok through %" PRIu32 "\n", limit);
    return 0;
}

int main(int argc, char **argv) {
    uint32_t a = 0;
    uint32_t b = 0;

    if (argc == 3 && strcmp(argv[1], "--scan") == 0) {
        if (!parse_u24(argv[2], &a) || a == 0) {
            usage(argv[0]);
            return 1;
        }
        return run_scan(a);
    }

    if (argc != 3 || !parse_u24(argv[1], &a) || !parse_u24(argv[2], &b) || a == 0 || b == 0) {
        usage(argv[0]);
        return 1;
    }

    return run_single(a, b);
}
