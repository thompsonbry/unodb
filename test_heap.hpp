// Copyright 2023-2026 UnoDB contributors
#ifndef UNODB_DETAIL_TEST_HEAP_HPP
#define UNODB_DETAIL_TEST_HEAP_HPP

/// \file
/// Heap memory fault injection infrastructure.
///
/// \ingroup test-internals
///
/// Allows testing for OOM conditions without actually exhausting heap memory.

// Should be the first include
#include "global.hpp"  // IWYU pragma: keep

// IWYU pragma: no_include <__new/exceptions.h>
// IWYU pragma: no_include <__ostream/basic_ostream.h>

#ifndef NDEBUG

#include <atomic>
#include <cassert>  // Avoid cyclical dependency with assert.hpp
#include <cstdint>
#include <iostream>
#include <new>  // IWYU pragma: keep
#include <string_view>

namespace unodb::test {

/// Test helper class for deterministically injecting memory allocation faults.
///
/// Allows tests to verify exception safety by throwing `std::bad_alloc`
/// exceptions at predetermined points, once some specific number of allocations
/// has been made.
class allocation_failure_injector final {
  friend struct pause_heap_faults;

 public:
  /// Reset fault injection state.
  ///
  /// Resets both allocation counter and fail-on-nth-allocation counter.
  ///
  /// \note Do not call directly: use
  /// UNODB_DETAIL_RESET_ALLOCATION_FAILURE_INJECTOR() instead.
  static void reset() noexcept {
    fail_on_nth_allocation_.store(0, std::memory_order_relaxed);
    allocation_counter.store(0, std::memory_order_release);
  }

  /// Configure allocation failure to occur on allocation number \a n.
  ///
  /// \note Do not call directly: use UNODB_DETAIL_FAIL_ON_NTH_ALLOCATION()
  /// instead.
  static void fail_on_nth_allocation(std::uint64_t n
                                     UNODB_DETAIL_USED_IN_DEBUG) noexcept {
    fail_on_nth_allocation_.store(n, std::memory_order_release);
  }

  UNODB_DETAIL_DISABLE_GCC_WARNING("-Wanalyzer-malloc-leak")

  /// Potentially fail current allocation.
  ///
  /// Called from the test allocation functions.
  ///
  /// \throws std::bad_alloc if the allocation counter matches the configured
  /// failure point.
  static void maybe_fail() {
    // Inspects the fail counter.  If non-zero, then bumps the allocation
    // counter.  If that results in the allocation counter reaching or exceeding
    // the fail counter, then throw std::bad_alloc.
    if (UNODB_DETAIL_UNLIKELY(paused)) return;
    const auto fail_counter =
        fail_on_nth_allocation_.load(std::memory_order_acquire);
    if (UNODB_DETAIL_UNLIKELY(fail_counter != 0) &&
        (allocation_counter.fetch_add(1, std::memory_order_relaxed) >=
         fail_counter - 1)) {
      throw std::bad_alloc{};
    }
  }

  /// Output debug information about injector state.
  ///
  /// \param msg Optional message prefix for the debug output
  [[gnu::cold]] static void dump(std::string_view msg = "") {
    std::cerr << msg << "allocation_failure_injector"
              << "{fail_on_nth_allocation = "
              << fail_on_nth_allocation_.load(std::memory_order_acquire)
              << ", allocation_counter = "
              << allocation_counter.load(std::memory_order_relaxed)
              << ", paused = " << paused << "}\n";
  }

  UNODB_DETAIL_RESTORE_GCC_WARNINGS()

 private:
  /// Count of allocations made iff heap tracking is enabled.
  // NOLINTNEXTLINE(cppcoreguidelines-avoid-non-const-global-variables)
  inline static std::atomic<std::uint64_t> allocation_counter{0};

  /// Allocation number that should fail (0 means no failure).
  // NOLINTNEXTLINE(cppcoreguidelines-avoid-non-const-global-variables)
  inline static std::atomic<std::uint64_t> fail_on_nth_allocation_{0};

  /// When true, failure injection is suspended for this thread.
  // NOLINTNEXTLINE(cppcoreguidelines-avoid-non-const-global-variables)
  inline static thread_local bool paused{};
};  // allocation_failure_injector

/// Lexically scoped guard to pause heap allocation tracking and faulting for
/// this thread.
///
/// To be used for specific allocations that are outside of the tested code,
/// such as constructing test diagnostic messages.
///
/// \note Do not instantiate directly: use
/// UNODB_DETAIL_PAUSE_HEAP_TRACKING_GUARD() instead.
struct [[nodiscard]] pause_heap_faults final {
 public:
  /// Pause heap faults for this thread.
  pause_heap_faults() noexcept { allocation_failure_injector::paused = true; }

  /// Resume heap faults for this thread.
  ~pause_heap_faults() { allocation_failure_injector::paused = false; }

  /// Copy construction is disabled.
  pause_heap_faults(const pause_heap_faults&) = delete;

  /// Move construction is disabled.
  pause_heap_faults(pause_heap_faults&&) = delete;

  /// Copy assignment is disabled.
  pause_heap_faults& operator=(const pause_heap_faults&) = delete;

  /// Move assignment is disabled.
  pause_heap_faults& operator=(pause_heap_faults&&) = delete;
};

/// Lexically scoped guard that fails the nth heap allocation and resets the
/// injector on every exit from the scope, including the injected failure
/// itself and a fatal test assertion.
///
/// Only one guard may be active in the process, which a debug atomic asserts.
///
/// A violated pin is reported by throwing `std::bad_alloc`, so any `noexcept`
/// frame inside the armed scope turns the violation into `std::terminate`
/// rather than an observable exception.  That includes a destructor run at
/// scope exit, which is why pinning one is a deliberate choice and not a free
/// extra check.
///
/// The injector state is process-wide, so a concurrent guard aborts rather than
/// resetting another guard's arming. Other threads still must not allocate: a
/// foreign allocation either consumes the pin, which passes the check
/// vacuously, or trips it on the wrong thread. Other threads may run as long as
/// they do not allocate.
///
/// This guard cannot restore an enclosing scope's state on exit: the arming is
/// a counting policy, and the enclosing scope's allocation count cannot
/// meaningfully account for what the inner scope allocated.
///
/// Past the trip point every allocation fails, so a test assertion inside the
/// armed scope loses its diagnostic to an escaping `std::bad_alloc`.  Evaluate
/// assertions outside the scope, or pause across them.
///
/// \note Do not instantiate directly: use
/// UNODB_DETAIL_FAIL_ON_NTH_ALLOCATION_GUARD(n) instead.
struct [[nodiscard]] fail_on_nth_allocation_guard final {
 public:
  /// Arm the injector to fail allocation number \a n for this process.
  explicit fail_on_nth_allocation_guard(std::uint64_t n) noexcept {
    assert(n != 0 &&
           "fail_on_nth_allocation_guard is 1-based; 0 disarms the injector");
    const auto was_active = active.exchange(true, std::memory_order_acquire);
    assert(!was_active &&
           "must_not_allocate/throws_bad_alloc scopes must not nest; guards "
           "must not overlap");
    allocation_failure_injector::reset();
    allocation_failure_injector::fail_on_nth_allocation(n);
  }

  /// Disarm the injector.
  ~fail_on_nth_allocation_guard() noexcept {
    allocation_failure_injector::reset();
    active.store(false, std::memory_order_release);
  }

  /// Copy construction is disabled.
  fail_on_nth_allocation_guard(const fail_on_nth_allocation_guard&) = delete;

  /// Move construction is disabled.
  fail_on_nth_allocation_guard(fail_on_nth_allocation_guard&&) = delete;

  /// Copy assignment is disabled.
  fail_on_nth_allocation_guard& operator=(const fail_on_nth_allocation_guard&) =
      delete;

  /// Move assignment is disabled.
  fail_on_nth_allocation_guard& operator=(fail_on_nth_allocation_guard&&) =
      delete;

 private:
  /// Whether a guard is active in this process.
  // NOLINTNEXTLINE(cppcoreguidelines-avoid-non-const-global-variables)
  inline static std::atomic<bool> active{false};
};

}  // namespace unodb::test

/// \addtogroup test-internals
/// \{

/// \name Heap allocation failure injection macros
/// \{

/// Reset heap allocation failure injector state.
/// \hideinitializer
/// Should be called at the start of each failure-injecting test.
#define UNODB_DETAIL_RESET_ALLOCATION_FAILURE_INJECTOR() \
  unodb::test::allocation_failure_injector::reset()

/// Configure heap allocation to fail on given allocation number.
/// \hideinitializer
/// \param n The 1-based number of the allocation that should fail.
#define UNODB_DETAIL_FAIL_ON_NTH_ALLOCATION(n) \
  unodb::test::allocation_failure_injector::fail_on_nth_allocation(n)

/// Disable heap failure injection for current thread in the current scope.
/// \hideinitializer
/// To be used for specific allocations that are outside of the tested code,
/// such as constructing test diagnostic messages.
#define UNODB_DETAIL_PAUSE_HEAP_TRACKING_GUARD() \
  const unodb::test::pause_heap_faults guard {}

/// Fail the nth heap allocation in the current scope, disarming the injector
/// on every exit from it.
/// \hideinitializer
/// \param n The 1-based number of the allocation that should fail.
#define UNODB_DETAIL_FAIL_ON_NTH_ALLOCATION_GUARD(n) \
  const unodb::test::fail_on_nth_allocation_guard heap_fault_guard { n }

/// \}

/// \}

#else  // !NDEBUG

#define UNODB_DETAIL_RESET_ALLOCATION_FAILURE_INJECTOR()
#define UNODB_DETAIL_FAIL_ON_NTH_ALLOCATION(n)
#define UNODB_DETAIL_PAUSE_HEAP_TRACKING_GUARD()
#define UNODB_DETAIL_FAIL_ON_NTH_ALLOCATION_GUARD(n)

#endif  // !NDEBUG

#endif  // UNODB_DETAIL_TEST_HEAP_HPP
