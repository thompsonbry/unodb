// Copyright 2026 UnoDB contributors
#ifndef UNODB_DETAIL_SYNC_POINT_TEST_UTILS_HPP
#define UNODB_DETAIL_SYNC_POINT_TEST_UTILS_HPP

/// \file
/// RAII guard for arming/disarming sync points in tests.
///
/// \ingroup test-internals

// Should be the first include
#include "global.hpp"  // IWYU pragma: keep

#ifndef NDEBUG

#include "sync.hpp"

namespace unodb::test {

/// RAII guard that disarms a sync_point on destruction.
struct sync_point_guard {
  /// The sync point being guarded.
  unodb::detail::sync_point& pt_;

  /// Construct from a sync point reference.
  explicit sync_point_guard(unodb::detail::sync_point& pt) noexcept : pt_{pt} {}

  /// Disarm the sync point on destruction.
  ~sync_point_guard() { pt_.disarm(); }

  sync_point_guard(const sync_point_guard&) = delete;
  sync_point_guard& operator=(const sync_point_guard&) = delete;
  sync_point_guard(sync_point_guard&&) = delete;
  sync_point_guard& operator=(sync_point_guard&&) = delete;
};

}  // namespace unodb::test

#endif  // NDEBUG

#endif  // UNODB_DETAIL_SYNC_POINT_TEST_UTILS_HPP
