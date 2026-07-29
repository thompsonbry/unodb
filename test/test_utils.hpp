// Copyright 2022-2026 UnoDB contributors
#ifndef UNODB_DETAIL_TEST_UTILS_HPP
#define UNODB_DETAIL_TEST_UTILS_HPP

/// \file
/// Test API for verifying heap allocation behavior.
///
/// \ingroup test-internals
///
/// Utilities for tests to verify heap allocation behavior.

// Should be the first include
#include "global.hpp"

#include <type_traits>

#ifndef NDEBUG
#include <cstdint>
#include <new>
#endif

#include "test_heap.hpp"

namespace unodb::test {

/// Test that given action does not allocate heap memory.
///
/// This function configures the allocation failure injector to fail on the
/// first allocation and executes the provided test action. If the action tries
/// to allocate memory, it will throw `std::bad_alloc`. If it completes
/// successfully, we know it didn't allocate. The injector is reset on every
/// exit from the pinned scope: a normal return, a fatal Google Test assertion
/// inside \a test_action, and the injected `std::bad_alloc` alike. Under
/// `NDEBUG` the injector compiles away, so the pin is not enforced and
/// \a test_action simply runs: the check is skipped rather than answered
/// wrongly.
///
/// \warning Armed scopes must not nest on one thread: doing so trips
/// unodb::test::fail_on_nth_allocation_guard's debug assert, which aborts the
/// process instead of reporting a test failure.
///
/// \warning A `noexcept` \a test_action does not unwind: the injected
/// `std::bad_alloc` crosses its own `noexcept` boundary, so a violated pin
/// terminates the process instead of producing an observable `std::bad_alloc`.
/// The QSBR accessors pass such actions deliberately, as CONTRIBUTING.md asks
/// for `noexcept` on anything that cannot throw in a release build, which is
/// what these are once this guard compiles away.
///
/// \warning An assertion inside \a test_action runs armed: its failure escapes
/// as `std::bad_alloc`, losing the diagnostic. Assert on the result instead.
///
/// \warning This function affects global state. No other threads should
/// allocate memory during execution of this function, as the allocation
/// failure injector is global.
///
/// \tparam TestAction Type of the test action callable
/// \param test_action Test function or callable that must not allocate during
/// its execution.
/// \return The result of test_action (if non-void)
template <typename TestAction>
  requires(!std::is_void_v<std::invoke_result_t<const TestAction&>>)
[[nodiscard]]
std::invoke_result_t<const TestAction&> must_not_allocate(
    const TestAction& test_action) noexcept(noexcept(test_action())) {
  UNODB_DETAIL_FAIL_ON_NTH_ALLOCATION_GUARD(1);
  return test_action();
}

/// \overload
template <typename TestAction>
  requires std::is_void_v<std::invoke_result_t<const TestAction&>>
void must_not_allocate(const TestAction& test_action) noexcept(
    noexcept(test_action())) {
  UNODB_DETAIL_FAIL_ON_NTH_ALLOCATION_GUARD(1);
  test_action();
}

#ifndef NDEBUG

// C26440 overlooks the deliberately propagated non-bad_alloc path.
UNODB_DETAIL_DISABLE_MSVC_WARNING(26440)

/// Run \a action with the allocation failure injector armed to fail allocation
/// number \a fail_n, and report whether it threw `std::bad_alloc`.
///
/// Keeps the armed scope around \a action alone: the guard is destroyed while
/// the injected failure unwinds, so the handler below, and the caller's
/// assertion on the result, both run disarmed. Asserting on the result
/// afterwards, rather than wrapping \a action in an assertion, matters: a
/// failing assertion builds its message with the injector still armed at its
/// trip point, so the diagnostic would be replaced by an escaping
/// `std::bad_alloc`.
///
/// Declared in debug builds only. Under `NDEBUG` the injector compiles away,
/// where this would arm nothing and report `false` for every \a fail_n --- a
/// wrong answer rather than a skipped check, unlike must_not_allocate(). Every
/// call site must therefore sit inside `#ifndef NDEBUG`, which the absent
/// declaration enforces at compile time.
///
/// \warning An assertion inside \a action runs armed past the trip point, so
/// its failure escapes as `std::bad_alloc` and is reported here as the expected
/// outcome, leaving the check unmade. Pause across such assertions.
///
/// \warning Arms a process-wide injector; concurrent allocations can interfere.
///
/// \warning Must not call must_not_allocate() or be called from it.
///
/// \tparam Action Type of the action callable
/// \param fail_n The 1-based number of the allocation that should fail
/// \param action Operation under test
/// \return Whether \a action threw `std::bad_alloc`
template <typename Action>
[[nodiscard]] bool throws_bad_alloc(
    std::uint64_t fail_n, const Action& action) noexcept(noexcept(action())) {
  try {
    UNODB_DETAIL_FAIL_ON_NTH_ALLOCATION_GUARD(fail_n);
    action();
  } catch (const std::bad_alloc&) {
    return true;
  }
  return false;
}

UNODB_DETAIL_RESTORE_MSVC_WARNINGS()

#endif  // !NDEBUG

}  // namespace unodb::test

#endif  // UNODB_DETAIL_TEST_UTILS_HPP
