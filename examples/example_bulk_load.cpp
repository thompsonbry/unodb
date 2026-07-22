// Copyright 2026 UnoDB contributors

// Example: bulk_load with sequential and parallel execution.

#include "global.hpp"

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <future>
#include <iostream>
#include <utility>
#include <vector>

#include "art.hpp"
#include "art_common.hpp"
#include "olc_art.hpp"

namespace {

constexpr std::size_t key_count = 100'000;

/// Build sorted key-value pairs. The caller is responsible for
/// pre-encoding and pre-sorting keys before calling bulk_load.
[[nodiscard]] auto make_sorted_data() {
  constexpr std::array<std::byte, 8> val{};
  const auto value = unodb::value_view{val};
  std::vector<std::pair<std::uint64_t, unodb::value_view>> kv;
  kv.reserve(key_count);
  for (std::size_t i = 0; i < key_count; ++i)
    kv.emplace_back(static_cast<std::uint64_t>(i), value);
  return kv;
}

}  // namespace

int main() {
  const auto data = make_sorted_data();

  // ─── Sequential bulk_load (default) ────────────────────────────────────────
  {
    unodb::db<std::uint64_t, unodb::value_view> tree;
    tree.bulk_load(data.begin(), data.end());  // sequential (default)
    std::cerr << "Sequential bulk_load: " << key_count << " keys loaded\n";
    std::cerr << "  get(42) found: " << tree.get(42).has_value() << '\n';
    tree.clear();
  }

  // ─── Parallel bulk_load ────────────────────────────────────────────────────
  // The caller provides a fork callable to submit parallel tasks.
  // The implementation partitions at the root level and builds each
  // subtree via the fork callable. Safe for all tree modes because
  // bulk_load operates on an unpublished tree (no concurrent readers).
  auto async_fork = [](auto&& f) {
    return std::async(std::launch::async, std::forward<decltype(f)>(f));
  };
  {
    unodb::db<std::uint64_t, unodb::value_view> tree;
    tree.bulk_load(async_fork, 8, data.begin(), data.end());
    std::cerr << "Parallel bulk_load: " << key_count << " keys loaded\n";
    std::cerr << "  get(99999) found: " << tree.get(99999).has_value() << '\n';
    tree.clear();
  }

  // ─── olc_db: same API ──────────────────────────────────────────────────────
  {
    unodb::olc_db<std::uint64_t, unodb::value_view> tree;
    tree.bulk_load(async_fork, 8, data.begin(), data.end());
    std::cerr << "olc_db parallel bulk_load: " << key_count << " keys loaded\n";
    tree.clear();
  }

  std::cerr << "Done.\n";
}
