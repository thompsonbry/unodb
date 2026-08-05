// Copyright 2022-2026 UnoDB contributors

#ifndef NDEBUG

// Should be the first include
#include "global.hpp"  // IWYU pragma: keep

// IWYU pragma: no_include <gtest/gtest.h>
// IWYU pragma: no_include <array>
// IWYU pragma: no_include <string>

#include "gtest_utils.hpp"
#include "qsbr.hpp"
#include "qsbr_gtest_utils.hpp"
#include "test_heap.hpp"
#include "test_utils.hpp"
#include "thread_sync.hpp"

namespace {

#ifdef __GLIBCXX__
constexpr auto std_thread_thread_alloc_count = 1;
#elif defined(__APPLE__)
constexpr auto std_thread_thread_alloc_count = 3;
#else
#error Needs porting
#endif

template <typename Test, typename AfterOOM>
void oom_test(unsigned fail_limit, Test test, AfterOOM after_oom) {
  unsigned fail_n;
  for (fail_n = 1; fail_n < fail_limit; ++fail_n) {
    UNODB_ASSERT_TRUE(unodb::test::throws_bad_alloc(fail_n, test));
    after_oom();
  }
  UNODB_ASSERT_FALSE(unodb::test::throws_bad_alloc(fail_n, test));
}

using QSBROOMTest = unodb::test::QSBRTestBase;

UNODB_TEST_F(QSBROOMTest, Resume) {
  qsbr_pause();
  UNODB_ASSERT_EQ(get_qsbr_thread_count(), 0);
  oom_test(
      3, [] { unodb::this_thread().qsbr_resume(); },
      []() noexcept { UNODB_ASSERT_EQ(get_qsbr_thread_count(), 0); });
  UNODB_ASSERT_EQ(get_qsbr_thread_count(), 1);
}

UNODB_TEST_F(QSBROOMTest, StartThread) {
  unodb::qsbr_thread second_thread;
  UNODB_ASSERT_EQ(get_qsbr_thread_count(), 1);
  oom_test(
      4 + std_thread_thread_alloc_count,
      [&second_thread] {
        // The operation under test is the thread creation itself, so the child
        // necessarily runs inside the armed window. It must therefore not arm a
        // guard of its own: read the state directly rather than through
        // get_qsbr_thread_count(), which pins with must_not_allocate. The read
        // runs armed, but the comparison must not: Google Test allocates while
        // building a failure message, and this frame is noexcept, so an armed
        // injector would turn the diagnostic into std::terminate. Pausing is
        // thread-local, so it neither disturbs the parent's arming nor exempts
        // the child's exit path. The child blocks after the comparison until
        // the parent releases it from inside the join pin, so teardown cannot
        // fall between the two armed scopes.
        second_thread = unodb::qsbr_thread{[]() noexcept {
          const auto thread_count = unodb::qsbr_state::get_thread_count(
              unodb::qsbr::instance().get_state());
          {
            UNODB_DETAIL_PAUSE_HEAP_TRACKING_GUARD();
            UNODB_EXPECT_EQ(thread_count, 2);
          }
          unodb::detail::thread_syncs[0].notify();
          unodb::detail::thread_syncs[1].wait();
        }};
      },
      []() noexcept { UNODB_ASSERT_EQ(get_qsbr_thread_count(), 1); });
  UNODB_ASSERT_TRUE(second_thread.joinable());
  unodb::detail::thread_syncs[0].wait();
  unodb::test::must_not_allocate([&second_thread] {
    unodb::detail::thread_syncs[1].notify();
    second_thread.join();
  });
}

UNODB_TEST_F(QSBROOMTest, DeferredDeallocation) {
  auto* ptr = static_cast<char*>(allocate());
  unodb::qsbr_thread second_thread{[] {
    unodb::detail::thread_syncs[0].notify();
    unodb::detail::thread_syncs[1].wait();

    quiescent();
  }};
  unodb::detail::thread_syncs[0].wait();
  oom_test(
      2, [ptr] { qsbr_deallocate(ptr); },
      [ptr]() noexcept { touch_memory(ptr); });
  unodb::detail::thread_syncs[1].notify();
  join(second_thread);
}

}  // namespace

#endif  // #ifndef NDEBUG
