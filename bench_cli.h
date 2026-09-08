#ifndef BENCH_CLI_H
#define BENCH_CLI_H

#include <stdio.h>
#include <string>
#include "parse_decimal.h"

struct BenchOptions {
    bool full_width = false;
    bool run_fp = true;
    bool run_stein = true;
    bool fixed = false;
    uint32_t count = 1u << 20;
    uint32_t rounds = 1024;
    uint32_t launches = 20;
    uint32_t block_size = 256;
    uint64_t fixed_a = 0;
    uint64_t fixed_b = 0;
    std::string mode, workload, fp_name, stein_name;
};

/* Returns 0 on success, 1 for --help, and 2 for invalid arguments.
   This parser runs before any CUDA calls and can be tested without a GPU. */
static int parse_bench_options(int argc, char **argv, const char *precision,
                               unsigned exact_bits, unsigned word_bits,
                               BenchOptions &options) {
    const std::string exact = "u" + std::to_string(exact_bits);
    const std::string full = "u" + std::to_string(word_bits);
    const std::string mode = argc > 1 ? argv[1] : "both";
    auto usage = [&]() {
        fprintf(stderr, "usage: %s [mode [count [rounds [launches [block_size [a b]]]]]]\n"
                        "modes: both_%s %s_%s stein_%s both_%s %s_%s stein_%s\n",
                argv[0], exact.c_str(), precision, exact.c_str(), exact.c_str(),
                full.c_str(), precision, full.c_str(), full.c_str());
    };
    if (argc == 2 && (mode == "--help" || mode == "-h")) {
        usage();
        return 1;
    }
    if (argc > 8 || argc == 7) {
        usage();
        return 2;
    }
    std::string canonical = mode;
    if (mode == "both" || mode == precision || mode == "stein") {
        canonical += "_" + exact;
    }
    const auto separator = canonical.find('_');
    const std::string kind = canonical.substr(0, separator);
    const std::string width = separator == std::string::npos ? "" : canonical.substr(separator + 1);
    if ((kind != "both" && kind != precision && kind != "stein") ||
        (width != exact && width != full)) {
        fprintf(stderr, "unknown mode: %s\n", mode.c_str());
        usage();
        return 2;
    }
    options.mode = canonical;
    options.workload = width;
    options.fp_name = std::string(precision) + "_" + width;
    options.stein_name = "stein_" + width;
    options.full_width = width == full;
    options.run_fp = kind != "stein";
    options.run_stein = kind != precision;
    uint32_t *parameters[] = {&options.count, &options.rounds, &options.launches, &options.block_size};
    const char *names[] = {"count", "rounds", "launches", "block_size"};
    for (int i = 2; i < argc && i <= 5; ++i) {
        uint64_t value;
        const uint64_t maximum = i == 5 ? 1024u : UINT32_MAX;
        if (!parse_decimal_u64(argv[i], maximum, &value) || value == 0) {
            fprintf(stderr, "invalid %s: %s (expected 1..%llu)\n",
                    names[i - 2], argv[i], (unsigned long long)maximum);
            return 2;
        }
        *parameters[i - 2] = (uint32_t)value;
    }
    const uint64_t grid = (options.count - 1u) / options.block_size + 1u;
    if (grid * options.block_size > (UINT64_C(1) << 32)) {
        fprintf(stderr, "count and block_size overflow the kernel index range\n");
        return 2;
    }
    options.fixed = argc == 8;
    if (options.fixed) {
        const unsigned bits = options.full_width ? word_bits : exact_bits;
        const uint64_t maximum = bits == 64 ? UINT64_MAX : (UINT64_C(1) << bits) - 1;
        if (!parse_decimal_u64(argv[6], maximum, &options.fixed_a) ||
            !parse_decimal_u64(argv[7], maximum, &options.fixed_b)) {
            fprintf(stderr, "invalid fixed pair; expected unsigned %u-bit integers\n", bits);
            return 2;
        }
    }
    return 0;
}

#endif
