#ifndef BENCH_HOST_CUH
#define BENCH_HOST_CUH

// Included after the precision-specific BenchSpec and kernels.
#include <inttypes.h>
#include <stdexcept>
#include <vector>
#include "bench_cli.h"

namespace bench {
using Word = BenchSpec::Word;

static void check_cuda(cudaError_t error) {
    if (error != cudaSuccess) {
        throw std::runtime_error(cudaGetErrorString(error));
    }
}

class DeviceBuffer {
public:
    Word *data = nullptr;
    explicit DeviceBuffer(size_t count) {
        check_cuda(cudaMalloc(&data, count * sizeof(Word)));
    }
    ~DeviceBuffer() { if (data) cudaFree(data); }
    DeviceBuffer(const DeviceBuffer &) = delete;
    DeviceBuffer &operator=(const DeviceBuffer &) = delete;
};

class Event {
public:
    cudaEvent_t value;
    Event() { check_cuda(cudaEventCreate(&value)); }
    ~Event() { cudaEventDestroy(value); }
    Event(const Event &) = delete;
    Event &operator=(const Event &) = delete;
};

static Word host_gcd(Word a, Word b) {
    while (b != 0) {
        Word remainder = a % b;
        a = b;
        b = remainder;
    }
    return a;
}

static void validate_dataset(const BenchOptions &options, const Word *a, const Word *b,
                             const Word *d_a, const Word *d_b, Word *d_out,
                             Word *out, uint32_t count) {
    const uint32_t block = 256;
    const uint32_t grid = (count - 1u) / block + 1u;
    for (bool fp : {true, false}) {
        BenchSpec::launch(fp, options.full_width, grid, block, d_a, d_b, d_out, count, 1, true);
        check_cuda(cudaGetLastError());
        check_cuda(cudaMemcpy(out, d_out, (size_t)count * sizeof(Word), cudaMemcpyDeviceToHost));
        for (uint32_t i = 0; i < count; ++i) {
            Word expected = host_gcd(a[i], b[i]);
            if (out[i] != expected) {
                fprintf(stderr, "validation mismatch: implementation=%s index=%u "
                        "input=%" PRIu64 ",%" PRIu64 " expected=%" PRIu64 " actual=%" PRIu64 "\n",
                        (fp ? options.fp_name : options.stein_name).c_str(), i,
                        (uint64_t)a[i], (uint64_t)b[i], (uint64_t)expected, (uint64_t)out[i]);
                throw std::runtime_error("GCD validation failed");
            }
        }
    }
}

static void validate(const BenchOptions &options, const Word *a, const Word *b,
                     const Word *d_a, const Word *d_b, Word *d_out, Word *out) {
    validate_dataset(options, a, b, d_a, d_b, d_out, out, options.count);
    const Word *regression_a, *regression_b;
    uint32_t count;
    BenchSpec::regressions(options.full_width, regression_a, regression_b, count);
    std::vector<Word> regression_out(count);
    DeviceBuffer device_a(count), device_b(count), device_out(count);
    check_cuda(cudaMemcpy(device_a.data, regression_a, count * sizeof(Word), cudaMemcpyHostToDevice));
    check_cuda(cudaMemcpy(device_b.data, regression_b, count * sizeof(Word), cudaMemcpyHostToDevice));
    validate_dataset(options, regression_a, regression_b, device_a.data, device_b.data,
                     device_out.data, regression_out.data(), count);
    printf("validation=ok workload=%s inputs=%u regression_cases=%u\n",
           options.workload.c_str(), options.count, count);
}

static void time_implementation(const BenchOptions &options, bool fp,
                                const Word *a, const Word *b, Word *d_out, Word *out) {
    const uint32_t grid = (options.count - 1u) / options.block_size + 1u;
    auto launch = [&]() {
        BenchSpec::launch(fp, options.full_width, grid, options.block_size,
                          a, b, d_out, options.count, options.rounds, options.fixed);
    };
    Event start, stop;
    launch();
    check_cuda(cudaGetLastError());
    check_cuda(cudaDeviceSynchronize());
    check_cuda(cudaEventRecord(start.value));
    for (uint32_t i = 0; i < options.launches; ++i) {
        launch();
    }
    check_cuda(cudaEventRecord(stop.value));
    check_cuda(cudaGetLastError());
    check_cuda(cudaEventSynchronize(stop.value));
    float elapsed_ms = 0;
    check_cuda(cudaEventElapsedTime(&elapsed_ms, start.value, stop.value));
    check_cuda(cudaMemcpy(out, d_out, (size_t)options.count * sizeof(Word), cudaMemcpyDeviceToHost));
    Word checksum = 0;
    for (uint32_t i = 0; i < options.count; ++i) {
        checksum ^= out[i];
    }
    const double calls = (double)options.count * options.rounds * options.launches;
    printf("%s: elapsed_ms=%.3f calls=%.0f calls_per_second=%.3e ns_per_call=%.3f checksum=%0*" PRIx64 "\n",
           (fp ? options.fp_name : options.stein_name).c_str(), elapsed_ms, calls,
           calls / (elapsed_ms * 1e-3), elapsed_ms * 1e6 / calls,
           (int)(sizeof(Word) * 2), (uint64_t)checksum);
}

static int main(int argc, char **argv) {
    BenchOptions options;
    int parsed = parse_bench_options(argc, argv, BenchSpec::precision,
                                    BenchSpec::exact_bits, sizeof(Word) * 8, options);
    if (parsed != 0) {
        return parsed == 1 ? 0 : parsed;
    }
    try {
        std::vector<Word> a(options.count), b(options.count), out(options.count);
        Word x = 1, y = 2;
        for (uint32_t i = 0; i < options.count; ++i) {
            if (options.fixed) {
                a[i] = (Word)options.fixed_a;
                b[i] = (Word)options.fixed_b;
            } else {
                BenchSpec::next(options.full_width, x, y);
                a[i] = x;
                b[i] = y;
            }
        }
        DeviceBuffer device_a(options.count), device_b(options.count), device_out(options.count);
        check_cuda(cudaMemcpy(device_a.data, a.data(), a.size() * sizeof(Word), cudaMemcpyHostToDevice));
        check_cuda(cudaMemcpy(device_b.data, b.data(), b.size() * sizeof(Word), cudaMemcpyHostToDevice));
        printf("mode=%s count=%u rounds=%u launches=%u block_size=%u",
               options.mode.c_str(), options.count, options.rounds, options.launches, options.block_size);
        if (options.fixed) {
            printf(" fixed_pair=%" PRIu64 ",%" PRIu64, options.fixed_a, options.fixed_b);
        }
        putchar('\n');
        validate(options, a.data(), b.data(), device_a.data, device_b.data, device_out.data, out.data());
        if (options.run_fp) {
            time_implementation(options, true, device_a.data, device_b.data, device_out.data, out.data());
        }
        if (options.run_stein) {
            time_implementation(options, false, device_a.data, device_b.data, device_out.data, out.data());
        }
    } catch (const std::exception &error) {
        fprintf(stderr, "benchmark failed: %s\n", error.what());
        return 1;
    }
    return 0;
}
} // namespace bench

int main(int argc, char **argv) { return bench::main(argc, argv); }

#endif
