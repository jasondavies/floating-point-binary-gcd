#include <cassert>
#include <vector>
#include "bench_cli.h"

static int parse(std::vector<std::string> arguments, BenchOptions &options, bool fp64 = false) {
    std::vector<char *> argv;
    for (auto &arg : arguments) argv.push_back(&arg[0]);
    return parse_bench_options(argv.size(), argv.data(), fp64 ? "fp64" : "fp32",
                               fp64 ? 53 : 24, fp64 ? 64 : 32, options);
}

int main() {
    uint64_t value = 0;
    assert(parse_decimal_u64("18446744073709551615", UINT64_MAX, &value));
    assert(value == UINT64_MAX);
    for (auto input : {"", "-1", "+1", " 1", "1 ", "3x", "18446744073709551616"}) {
        assert(!parse_decimal_u64(input, UINT64_MAX, &value));
    }
    BenchOptions defaults;
    assert(parse({"bench"}, defaults) == 0);
    assert(defaults.mode == "both_u24" && defaults.count == (1u << 20));
    BenchOptions fixed;
    assert(parse({"bench", "both_u32", "1", "1", "1", "1", "0", "4294967294"}, fixed) == 0);
    assert(fixed.fixed && fixed.fixed_a == 0 && fixed.fixed_b == 4294967294u);
    BenchOptions wide;
    assert(parse({"bench", "both_u64", "1", "1", "1", "1", "18446744073709551615", "0"}, wide, true) == 0);
    assert(wide.fixed_a == UINT64_MAX && wide.fixed_b == 0);
    BenchOptions alias;
    assert(parse({"bench", "stein"}, alias, true) == 0);
    assert(alias.mode == "stein_u53" && !alias.run_fp && alias.run_stein);
    for (const auto &args : std::vector<std::vector<std::string>>{
        {"bench", "typo"}, {"bench", "both_u64"}, {"bench", "both", "0"},
        {"bench", "both", "4294967296"}, {"bench", "both", "1", "0"},
        {"bench", "both", "1", "1", "0"}, {"bench", "both", "1", "1", "1", "0"},
        {"bench", "both", "1", "1", "1", "1025"},
        {"bench", "both", "1", "1", "1", "1", "1"},
        {"bench", "both", "1", "1", "1", "1", "1", "2", "3"},
        {"bench", "both", "1", "1", "1", "1", "16777216", "1"},
    }) {
        BenchOptions options;
        assert(parse(args, options) == 2);
    }
    puts("benchmark CLI checks passed");
}
