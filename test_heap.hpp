// Copyright 2023 Laurynas Biveinis
#ifndef UNODB_DETAIL_TEST_HEAP_HPP
#define UNODB_DETAIL_TEST_HEAP_HPP

//
// CAUTION: [global.hpp] MUST BE THE FIRST INCLUDE IN ALL SOURCE AND
// HEADER FILES !!!
//
// This header defines _GLIBCXX_DEBUG and _GLIBCXX_DEBUG_PEDANTIC for
// DEBUG builds.  If some standard headers are included before and
// after those symbols are defined, then that results in different
// container internal structure layouts and that is Not Good.
#include "global.hpp"  // IWYU pragma: keep

#ifndef NDEBUG

#include <atomic>
#include <cstdint>
#include <iostream>
#include <new>

namespace unodb::test {

/// Test helper class may be used to inject memory allocation faults,
/// throwing std::bad_alloc once some number of allocations have been
/// made.
class allocation_failure_injector final {
  friend class pause_heap_faults;

 public:
  UNODB_DETAIL_DISABLE_MSVC_WARNING(4514)

  /// Reset the counters tracking the number of allocations and the
  /// allocation number at which allocation will throw std::bad_alloc
  /// to zero.
  static void reset() noexcept {
    fail_on_nth_allocation_.store(0, std::memory_order_relaxed);
    allocation_counter.store(0, std::memory_order_release);
  }

  /// Set the allocation number at which allocation will fail.
  static void fail_on_nth_allocation(
      std::uint64_t n UNODB_DETAIL_USED_IN_DEBUG) noexcept {
    fail_on_nth_allocation_.store(n, std::memory_order_release);
  }

  UNODB_DETAIL_DISABLE_GCC_WARNING("-Wanalyzer-malloc-leak")

  /// Invoked from the gtest harness allocator hooks to fail memory
  /// allocation by throwing std::bad_alloc iff (a) memory allocation
  /// tracking is enabled; and (b) the allocation fail counter is
  /// breached.
  static void maybe_fail() {
    // Inspects the fail counter.  If non-zero, then bumps the
    // allocation counter.  If that results in the allocation counter
    // reaching or exceeding the fail counter, then throw
    // std::bad_alloc.
    const auto fail_counter =
        fail_on_nth_allocation_.load(std::memory_order_acquire);
    if (UNODB_DETAIL_UNLIKELY(fail_counter != 0) &&
        (allocation_counter.fetch_add(1, std::memory_order_relaxed) >=
         fail_counter - 1)) {
      throw std::bad_alloc{};
    }
  }

  /// Debugging
  static void dump(std::string msg = "") {
    std::cerr << msg << "allocation_failure_injector"
              << "{fail_on_nth_allocation="
              << fail_on_nth_allocation_.load(std::memory_order_acquire)
              << ",allocation_counter="
              << allocation_counter.load(std::memory_order_relaxed) << "}\n";
  }

  UNODB_DETAIL_RESTORE_GCC_WARNINGS()
  UNODB_DETAIL_RESTORE_MSVC_WARNINGS()

 private:
  // NOLINTNEXTLINE(cppcoreguidelines-avoid-non-const-global-variables)
  inline static std::atomic<std::uint64_t> allocation_counter{0};
  // NOLINTNEXTLINE(cppcoreguidelines-avoid-non-const-global-variables)
  inline static std::atomic<std::uint64_t> fail_on_nth_allocation_{0};
};  // allocation_failure_injector

/// Lexically scoped guard to pause heap allocation tracking and
/// faulting.
///
/// Note: This class is NOT thread-safe since no suitable global
/// barrier exists when it is constructed and destructed!
class pause_heap_faults {
 public:
  /// Saves the state of the allocation_failure_injector and then
  /// resets it.
  explicit pause_heap_faults()
      :  // Same order and memory_order as maybe_fail().
        fail_on_nth_allocation(
            allocation_failure_injector::fail_on_nth_allocation_.load(
                std::memory_order_acquire)),
        allocation_counter(allocation_failure_injector::allocation_counter.load(
            std::memory_order_relaxed)) {
    // reset the allocation tracker.
    allocation_failure_injector::reset();
  }
  /// Restores the state of the allocation_failure_injector.
  ~pause_heap_faults() {
    // Same order and memory_order as reset().
    allocation_failure_injector::fail_on_nth_allocation_.store(
        fail_on_nth_allocation, std::memory_order_relaxed);
    allocation_failure_injector::allocation_counter.store(
        allocation_counter, std::memory_order_release);
  }

 private:
  const std::uint64_t fail_on_nth_allocation;
  const std::uint64_t allocation_counter;
};  // class pause_heap_faults

}  // namespace unodb::test

#define UNODB_DETAIL_RESET_ALLOCATION_FAILURE_INJECTOR() \
  unodb::test::allocation_failure_injector::reset()
#define UNODB_DETAIL_FAIL_ON_NTH_ALLOCATION(n) \
  unodb::test::allocation_failure_injector::fail_on_nth_allocation(n)

#else  // !NDEBUG

#define UNODB_DETAIL_RESET_ALLOCATION_FAILURE_INJECTOR()
#define UNODB_DETAIL_FAIL_ON_NTH_ALLOCATION(n)

#endif  // !NDEBUG

#endif  // UNODB_DETAIL_TEST_HEAP_HPP
