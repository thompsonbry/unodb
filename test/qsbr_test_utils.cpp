// Copyright 2021 Laurynas Biveinis

#include "global.hpp"  // IWYU pragma: keep

#include "qsbr_test_utils.hpp"

#include <gtest/gtest.h>  // IWYU pragma: keep

#include "qsbr.hpp"

namespace unodb::test {

void expect_idle_qsbr() {
  const auto state = unodb::qsbr::instance().get_state();
  EXPECT_TRUE(qsbr_state::single_thread_mode(state));
  EXPECT_EQ(unodb::qsbr::instance().get_previous_interval_dealloc_count(), 0);
  EXPECT_EQ(unodb::qsbr::instance().get_current_interval_dealloc_count(), 0);
  const auto thread_count = qsbr_state::get_thread_count(state);
  const auto threads_in_previous_epoch =
      qsbr_state::get_threads_in_previous_epoch(state);
  EXPECT_EQ(thread_count, 1);
  EXPECT_EQ(threads_in_previous_epoch, 1);
}

}  // namespace unodb::test
