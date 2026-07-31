// Copyright 2026 UnoDB contributors
#ifndef UNODB_DETAIL_SYNC_HPP
#define UNODB_DETAIL_SYNC_HPP

/// \file
/// Debug-only synchronization points for concurrent algorithm testing.
///
/// In Debug builds, sync points allow tests to pause a thread at a
/// specific point in an algorithm and let another thread act before
/// continuing.  In Release builds, everything compiles away.

#include "global.hpp"

#ifndef NDEBUG
#include <functional>
#include <type_traits>
#endif

namespace unodb::detail {

#ifndef NDEBUG

/// A named synchronization point that tests can arm with a callback.
/// Tests call arm() before the parallel phase and disarm() after.
struct sync_point {
  std::function<void()> hook_;
  UNODB_DETAIL_DISABLE_MSVC_WARNING(26440)
  void arm(std::function<void()> fn) { hook_ = std::move(fn); }
  void disarm() noexcept { hook_ = nullptr; }
  void hit() {
    if (hook_) hook_();
  }
  UNODB_DETAIL_RESTORE_MSVC_WARNINGS()
};

/// Fire a sync point (calls hook if armed).
///
/// The `std::is_constant_evaluated()` guard keeps `constexpr` callers
/// constant-evaluable; there is nothing to fire during constant evaluation.
constexpr void sync(sync_point& pt) noexcept {
  if (!std::is_constant_evaluated()) pt.hit();
}

#else  // NDEBUG

struct sync_point {};

constexpr void sync(sync_point&) noexcept {}

#endif  // NDEBUG

}  // namespace unodb::detail

#endif  // UNODB_DETAIL_SYNC_HPP
