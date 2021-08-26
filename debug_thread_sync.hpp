// Copyright 2020-2021 Laurynas Biveinis
#ifndef UNODB_DETAIL_DEBUG_THREAD_SYNC_HPP
#define UNODB_DETAIL_DEBUG_THREAD_SYNC_HPP

#include "global.hpp"

#include <cassert>
#include <condition_variable>
#include <mutex>

namespace unodb::debug {

class thread_wait final {
 public:
  thread_wait() noexcept = default;
  ~thread_wait() noexcept { assert(is_reset()); }

  [[nodiscard]] bool is_reset() const noexcept {
    std::lock_guard lock{sync_mutex};
    return !flag;
  }

  void notify() {
    {
      std::lock_guard<std::mutex> lock{sync_mutex};
      flag = true;
    }
    thread_sync.notify_one();
  }

  void wait() {
    std::unique_lock lock{sync_mutex};
    // cppcheck-suppress assignBoolToPointer
    thread_sync.wait(lock, [&flag = flag] { return flag; });
    flag = false;
    lock.unlock();
  }

  thread_wait(const thread_wait &) = delete;
  thread_wait(thread_wait &&) = delete;
  thread_wait &operator=(const thread_wait &) = delete;
  thread_wait &operator=(thread_wait &&) = delete;

 private:
  // Replace with a C++20 latch when that's available
  std::condition_variable thread_sync;
  mutable std::mutex sync_mutex;
  bool flag{false};
};

}  // namespace unodb::debug

#endif  // UNODB_DETAIL_DEBUG_THREAD_SYNC_HPP
