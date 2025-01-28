// Copyright 2019-2025 UnoDB contributors

//
// CAUTION: [global.hpp] MUST BE THE FIRST INCLUDE IN ALL SOURCE AND
// HEADER FILES !!!
//
// This header defines _GLIBCXX_DEBUG and _GLIBCXX_DEBUG_PEDANTIC for
// DEBUG builds.  If some standard headers are included before and
// after those symbols are defined, then that results in different
// container internal structure layouts and that is Not Good.
#include "global.hpp"  // IWYU pragma: keep

// IWYU pragma: no_include <string>

#include <thread>

#include <benchmark/benchmark.h>

#include "micro_benchmark_concurrency.hpp"
#include "micro_benchmark_utils.hpp"
#include "mutex_art.hpp"

namespace {

class [[nodiscard]] concurrent_benchmark_mutex final
    : public unodb::benchmark::concurrent_benchmark<unodb::benchmark::mutex_db,
                                                    std::thread> {};

concurrent_benchmark_mutex benchmark_fixture;

void parallel_get(benchmark::State &state) {
  benchmark_fixture.parallel_get(state);
}

void parallel_insert_disjoint_ranges(benchmark::State &state) {
  benchmark_fixture.parallel_insert_disjoint_ranges(state);
}

void parallel_delete_disjoint_ranges(benchmark::State &state) {
  benchmark_fixture.parallel_delete_disjoint_ranges(state);
}

}  // namespace

UNODB_START_BENCHMARKS()

BENCHMARK(parallel_get)
    ->Apply(unodb::benchmark::concurrency_ranges16)
    ->Unit(benchmark::kMillisecond)
    ->MeasureProcessCPUTime()
    ->UseRealTime();
BENCHMARK(parallel_insert_disjoint_ranges)
    ->Apply(unodb::benchmark::concurrency_ranges32)
    ->Unit(benchmark::kMillisecond)
    ->MeasureProcessCPUTime()
    ->UseRealTime();
BENCHMARK(parallel_delete_disjoint_ranges)
    ->Apply(unodb::benchmark::concurrency_ranges32)
    ->Unit(benchmark::kMillisecond)
    ->MeasureProcessCPUTime()
    ->UseRealTime();

UNODB_BENCHMARK_MAIN();
