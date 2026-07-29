// Copyright 2026 UnoDB contributors

#ifndef NDEBUG

// Should be the first include
#include "global.hpp"  // IWYU pragma: keep

// IWYU pragma: no_include <__new/exceptions.h>
// IWYU pragma: no_include <gtest/gtest.h>
// IWYU pragma: no_include <string>

#include <atomic>
#include <new>  // IWYU pragma: keep
#include <stdexcept>
#include <thread>
#include <tuple>
#include <type_traits>

#include "gtest_utils.hpp"
#include "heap.hpp"
#include "test_heap.hpp"
#include "test_utils.hpp"

// Pins the allocation failure injector's scope discipline. Deliberately drives
// unodb::detail::allocate_aligned rather than the replaced global operator new,
// which this target does not link: nothing else in the process then perturbs
// the allocation counter, so the armed windows below are deterministic.
namespace {

static_assert(noexcept(unodb::test::throws_bad_alloc(
    1, static_cast<void (*)() noexcept>(nullptr))));

/// Exercise one deterministic allocation through the failure injector.
void allocate_and_free() {
  unodb::detail::free_aligned(unodb::detail::allocate_aligned(8));
}

UNODB_TEST(HeapFaultInjection, MustNotAllocateVoidDisarmsOnNormalReturn) {
  const auto test_action = [thread = std::thread{}]() noexcept {
    static_cast<void>(thread);
  };
  static_assert(!std::is_copy_constructible_v<decltype(test_action)>);

  UNODB_ASSERT_NO_THROW(unodb::test::must_not_allocate(test_action));
  UNODB_ASSERT_NO_THROW(allocate_and_free());
}

// The injector must be disarmed once must_not_allocate's action has violated
// its pin, so that the failure does not spread to everything after it.
// Asserting directly on the injected throw, and on the trailing allocation
// surviving, is safe here only because this target does not link the replaced
// global operator new, so Google Test's own allocations are not injected;
// elsewhere use throws_bad_alloc.
UNODB_TEST(HeapFaultInjection, MustNotAllocateResetsOnViolation) {
  UNODB_ASSERT_THROW(
      unodb::test::must_not_allocate([] { allocate_and_free(); }),
      std::bad_alloc);

  UNODB_ASSERT_NO_THROW(allocate_and_free());
}

// The non-void instantiation, which the rewrite collapsed into the void one's
// single armed return: it must pin, disarm and forward the value alike.
UNODB_TEST(HeapFaultInjection, MustNotAllocateNonVoidPinsAndForwards) {
  const auto test_action = [thread = std::thread{}]() noexcept {
    static_cast<void>(thread);
    return 42;
  };
  static_assert(!std::is_copy_constructible_v<decltype(test_action)>);

  UNODB_ASSERT_EQ(unodb::test::must_not_allocate(test_action), 42);

  UNODB_ASSERT_THROW(std::ignore = unodb::test::must_not_allocate([] {
                       allocate_and_free();
                       return 42;
                     }),
                     std::bad_alloc);

  UNODB_ASSERT_NO_THROW(allocate_and_free());
}

// Same for a guard the injected failure unwinds out of. Passing the armed scope
// as the asserted statement keeps the handler outside it by construction: the
// guard is destroyed as the injected failure unwinds, before Google Test's
// handler runs.
UNODB_TEST(HeapFaultInjection, GuardResetsWhenInjectedFailureEscapes) {
  UNODB_ASSERT_THROW(
      {
        UNODB_DETAIL_FAIL_ON_NTH_ALLOCATION_GUARD(1);
        allocate_and_free();
      },
      std::bad_alloc);

  UNODB_ASSERT_NO_THROW(allocate_and_free());
}

// The nth allocation is counted from the guard's scope entry, not from whatever
// the counter happened to hold. The raw arm below is what makes a stale count
// reachable at all: maybe_fail() advances the counter only while armed, so an
// allocation made with the injector disarmed cannot dirty it.
UNODB_TEST(HeapFaultInjection, GuardCountsFromScopeEntry) {
  UNODB_DETAIL_FAIL_ON_NTH_ALLOCATION(100);
  allocate_and_free();

  {
    UNODB_DETAIL_FAIL_ON_NTH_ALLOCATION_GUARD(2);
    // Distinguishes counting from scope entry from counting from the stale
    // value: without the guard constructor's reset, the stale count trips the
    // injector one allocation early.
    UNODB_ASSERT_NO_THROW(allocate_and_free());
    UNODB_ASSERT_THROW(allocate_and_free(), std::bad_alloc);
  }

  UNODB_ASSERT_NO_THROW(allocate_and_free());
}

// throws_bad_alloc reports both outcomes and leaves the injector disarmed on
// each: the trailing allocation would fault if the guard had not reset.
UNODB_TEST(HeapFaultInjection, ThrowsBadAllocReportsOutcomeAndDisarms) {
  const auto test_action = [thread = std::thread{}] {
    static_cast<void>(thread);
    allocate_and_free();
  };
  static_assert(!std::is_copy_constructible_v<decltype(test_action)>);

  UNODB_ASSERT_TRUE(unodb::test::throws_bad_alloc(1, test_action));
  UNODB_ASSERT_NO_THROW(allocate_and_free());

  UNODB_ASSERT_FALSE(unodb::test::throws_bad_alloc(2, allocate_and_free));
  UNODB_ASSERT_NO_THROW(allocate_and_free());
}

/// Throw an exception that throws_bad_alloc() must propagate.
[[noreturn]] void throw_not_bad_alloc() {
  throw std::runtime_error{"not bad_alloc"};
}
static_assert(!noexcept(unodb::test::throws_bad_alloc(1, throw_not_bad_alloc)));

// An exception that is not std::bad_alloc is neither swallowed nor reported as
// completion; on that path only the guard destructor disarms. Throwing here is
// safe because this target does not link the replaced global operator new, so
// building the exception cannot consume the pin.
UNODB_TEST(HeapFaultInjection, ThrowsBadAllocDisarmsOnOtherException) {
  UNODB_ASSERT_THROW(
      std::ignore = unodb::test::throws_bad_alloc(1, throw_not_bad_alloc),
      std::runtime_error);

  UNODB_ASSERT_NO_THROW(allocate_and_free());
}

// The guard cannot nest: it cannot restore an enclosing armed scope's
// allocation count, so an inner guard would silently cancel the outer pin. A
// same-scope nest is already a compile error, the macro hardcoding its variable
// name, so separate functions are what reach the cross-call nest the assert
// actually catches. Both guards live in the death test's child process, leaving
// this process's injector state untouched.
// LCOV_EXCL_START
/// Enter an armed scope from the nesting death-test helper.
void armed_scope() noexcept { UNODB_DETAIL_FAIL_ON_NTH_ALLOCATION_GUARD(1); }

/// Trigger the cross-call nested-scope assertion.
void nested_armed_scopes() noexcept {
  UNODB_DETAIL_FAIL_ON_NTH_ALLOCATION_GUARD(1);
  armed_scope();
}
static_assert(noexcept(nested_armed_scopes()));
// LCOV_EXCL_STOP

UNODB_TEST(HeapFaultInjectionDeathTest, NestedGuardAborts) {
  UNODB_ASSERT_DEATH({ nested_armed_scopes(); }, "must not nest");
}

// LCOV_EXCL_START
/// Trigger the process-wide overlapping-scope assertion across two threads.
void concurrently_armed_scopes() {
  std::atomic<bool> first_armed{false};
  std::atomic<bool> first_may_exit{false};
  std::thread first{[&first_armed, &first_may_exit]() noexcept {
    UNODB_DETAIL_FAIL_ON_NTH_ALLOCATION_GUARD(1);
    first_armed.store(true, std::memory_order_release);
    while (!first_may_exit.load(std::memory_order_acquire))
      std::this_thread::yield();
  }};
  while (!first_armed.load(std::memory_order_acquire))
    std::this_thread::yield();

  {
    UNODB_DETAIL_FAIL_ON_NTH_ALLOCATION_GUARD(1);
  }

  first_may_exit.store(true, std::memory_order_release);
  first.join();
}
// LCOV_EXCL_STOP

UNODB_TEST(HeapFaultInjectionDeathTest, ConcurrentGuardAborts) {
  UNODB_ASSERT_DEATH({ concurrently_armed_scopes(); }, "must not overlap");
}

// The guard is 1-based because 0 is the injector's disarmed value: a zero-armed
// scope would pin nothing while every helper built on it reported the
// reassuring answer - must_not_allocate returning normally, throws_bad_alloc
// returning false. That is a wrong answer rather than a skipped check, which is
// what the assert exists to prevent.
// LCOV_EXCL_START
/// Trigger the assertion that rejects the disarmed value as a failure point.
void zero_armed_scope() noexcept {
  UNODB_DETAIL_FAIL_ON_NTH_ALLOCATION_GUARD(0);
}
static_assert(noexcept(zero_armed_scope()));
// LCOV_EXCL_STOP

UNODB_TEST(HeapFaultInjectionDeathTest, ZeroFailNAborts) {
  UNODB_ASSERT_DEATH({ zero_armed_scope(); }, "1-based");
}

}  // namespace

#endif  // #ifndef NDEBUG
