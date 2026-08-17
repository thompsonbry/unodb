// Copyright 2026 UnoDB contributors

// Should be the first include
#include "global.hpp"  // IWYU pragma: keep

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <future>
#include <random>
#include <stdexcept>
#include <utility>
#include <vector>

#include <gtest/gtest.h>  // NOLINT(misc-include-cleaner)

#include "art_common.hpp"
#include "art_test_data.hpp"
#include "db_test_utils.hpp"
#include "gtest_utils.hpp"
#include "node_type.hpp"
#include "qsbr.hpp"
#include "qsbr_test_utils.hpp"

UNODB_DETAIL_DISABLE_MSVC_WARNING(6326)
UNODB_DETAIL_DISABLE_MSVC_WARNING(26818)
UNODB_DETAIL_DISABLE_MSVC_WARNING(26445)

namespace {

#ifdef UNODB_DETAIL_WITH_STATS
using unodb::as_i;
using unodb::node_type;
using unodb::test_data::decode;
#endif
using unodb::key_view;
using unodb::value_view;
using unodb::test::u64_db;
using unodb::test::u64_mutex_db;
using unodb::test::u64_olc_db;

constexpr auto val_bytes =
    std::array<std::byte, 5>{std::byte{0x68}, std::byte{0x65}, std::byte{0x6C},
                             std::byte{0x6C}, std::byte{0x6F}};
constexpr auto val = value_view{val_bytes};

#ifdef UNODB_DETAIL_WITH_STATS

constexpr auto val16 = std::array<std::byte, 16>{};
constexpr auto large_val = value_view{val16};

/// Generate N keys that differ at byte 0 (big-endian uint64_t).
/// For N <= 256, all keys differ only at byte 0 (single root node).
/// For N > 256, extra keys share byte 0 with key 0 but differ at byte 1.
[[nodiscard]] std::vector<std::pair<std::uint64_t, value_view>> make_keys(
    std::size_t n) {
  std::vector<std::pair<std::uint64_t, value_view>> kv;
  kv.reserve(n);
  for (std::uint64_t i = 0; i < n && i < 256; ++i) {
    const auto key = i << 56U;
    kv.emplace_back(key, val);
  }
  // Overflow keys: share byte 0 == 0x00, differ at byte 1
  for (std::uint64_t i = 256; i < n; ++i) {
    const auto key = (i - 255) << 48U;
    kv.emplace_back(key, val);
  }
  std::ranges::sort(kv, {}, &decltype(kv)::value_type::first);
  return kv;
}

// ─── Node Count Tests ────────────────────────────────────────────────────────

UNODB_TEST(BulkLoad, Empty) {
  u64_db db;
  std::vector<std::pair<std::uint64_t, value_view>> kv;
  db.bulk_load(kv.begin(), kv.end());
  UNODB_ASSERT_TRUE(db.empty());
  const auto counts = db.get_node_counts();
  for (const auto c : counts) {
    UNODB_ASSERT_EQ(c, 0U);
  }
}

UNODB_TEST(BulkLoad, Single) {
  u64_db db;
  constexpr std::uint64_t key = 1;
  std::vector<std::pair<std::uint64_t, value_view>> kv{{key, val}};
  db.bulk_load(kv.begin(), kv.end());
  const auto result = db.get(key);
  UNODB_ASSERT_TRUE(result.has_value());
  UNODB_ASSERT_EQ(  // NOLINT(bugprone-unchecked-optional-access)
      result.value().size(), val.size());
  const auto counts = db.get_node_counts();
  UNODB_ASSERT_EQ(counts[as_i<node_type::LEAF>], 1U);
  UNODB_ASSERT_EQ(counts[as_i<node_type::I4>], 0U);
}

UNODB_TEST(BulkLoad, Small4Keys) {
  u64_db db;
  auto kv = make_keys(4);
  db.bulk_load(kv.begin(), kv.end());
  for (const auto& [k, v] : kv) {
    UNODB_ASSERT_TRUE(db.get(k).has_value());
  }
  const auto counts = db.get_node_counts();
  UNODB_ASSERT_EQ(counts[as_i<node_type::LEAF>], 4U);
  UNODB_ASSERT_EQ(counts[as_i<node_type::I4>], 1U);
}

UNODB_TEST(BulkLoad, Boundary4) {
  u64_db db;
  auto kv = make_keys(4);
  db.bulk_load(kv.begin(), kv.end());
  const auto counts = db.get_node_counts();
  UNODB_ASSERT_EQ(counts[as_i<node_type::I4>], 1U);
  UNODB_ASSERT_EQ(counts[as_i<node_type::I16>], 0U);
  UNODB_ASSERT_EQ(counts[as_i<node_type::I48>], 0U);
  UNODB_ASSERT_EQ(counts[as_i<node_type::I256>], 0U);
}

UNODB_TEST(BulkLoad, Boundary5) {
  u64_db db;
  auto kv = make_keys(5);
  db.bulk_load(kv.begin(), kv.end());
  const auto counts = db.get_node_counts();
  UNODB_ASSERT_EQ(counts[as_i<node_type::I16>], 1U);
  UNODB_ASSERT_EQ(counts[as_i<node_type::I4>], 0U);
}

UNODB_TEST(BulkLoad, Boundary16) {
  u64_db db;
  auto kv = make_keys(16);
  db.bulk_load(kv.begin(), kv.end());
  const auto counts = db.get_node_counts();
  UNODB_ASSERT_EQ(counts[as_i<node_type::I16>], 1U);
  UNODB_ASSERT_EQ(counts[as_i<node_type::I48>], 0U);
}

UNODB_TEST(BulkLoad, Boundary17) {
  u64_db db;
  auto kv = make_keys(17);
  db.bulk_load(kv.begin(), kv.end());
  const auto counts = db.get_node_counts();
  UNODB_ASSERT_EQ(counts[as_i<node_type::I48>], 1U);
  UNODB_ASSERT_EQ(counts[as_i<node_type::I16>], 0U);
}

UNODB_TEST(BulkLoad, Boundary48) {
  u64_db db;
  auto kv = make_keys(48);
  db.bulk_load(kv.begin(), kv.end());
  const auto counts = db.get_node_counts();
  UNODB_ASSERT_EQ(counts[as_i<node_type::I48>], 1U);
  UNODB_ASSERT_EQ(counts[as_i<node_type::I256>], 0U);
}

UNODB_TEST(BulkLoad, Boundary49) {
  u64_db db;
  auto kv = make_keys(49);
  db.bulk_load(kv.begin(), kv.end());
  const auto counts = db.get_node_counts();
  UNODB_ASSERT_EQ(counts[as_i<node_type::I256>], 1U);
  UNODB_ASSERT_EQ(counts[as_i<node_type::I48>], 0U);
}

UNODB_TEST(BulkLoad, Growth260) {
  u64_db db;
  auto kv = make_keys(260);
  db.bulk_load(kv.begin(), kv.end());
  for (const auto& [k, v] : kv) {
    UNODB_ASSERT_TRUE(db.get(k).has_value());
  }
  const auto counts = db.get_node_counts();
  UNODB_ASSERT_EQ(counts[as_i<node_type::I256>], 1U);
  UNODB_ASSERT_EQ(counts[as_i<node_type::LEAF>], 260U);
}

UNODB_TEST(BulkLoad, SharedPrefix) {
  u64_db db;
  std::vector<std::pair<std::uint64_t, value_view>> kv;
  kv.reserve(20);
  // All keys share byte 0 = 0x01, differ at byte 1.
  for (std::uint64_t i = 0; i < 20; ++i) {
    kv.emplace_back((1ULL << 56U) | (i << 48U), val);
  }
  std::ranges::sort(kv, {}, &decltype(kv)::value_type::first);
  db.bulk_load(kv.begin(), kv.end());
  for (const auto& [k, v] : kv) {
    UNODB_ASSERT_TRUE(db.get(k).has_value());
  }
}

UNODB_TEST(BulkLoad, DeepPrefixChain) {
  using unodb::test::key_view_db;
  key_view_db db;
  std::vector<std::pair<std::vector<std::byte>, value_view>> raw_keys;
  raw_keys.reserve(10);
  for (int i = 0; i < 10; ++i) {
    std::vector<std::byte> k(13);
    for (int j = 0; j < 10; ++j) {
      k[static_cast<std::size_t>(j)] = static_cast<std::byte>(j + 1);
    }
    k[10] = static_cast<std::byte>(i);
    k[11] = std::byte{0xAA};
    k[12] = std::byte{0xBB};
    raw_keys.emplace_back(std::move(k), val);
  }
  std::vector<std::pair<unodb::key_view, value_view>> kv;
  kv.reserve(raw_keys.size());
  for (auto& [k, v] : raw_keys) {
    kv.emplace_back(unodb::key_view{k.data(), k.size()}, v);
  }
  db.bulk_load(kv.begin(), kv.end());
  for (const auto& [k, v] : kv) {
    UNODB_ASSERT_TRUE(db.get(k).has_value());
  }
}

// ─── Structural Tests ────────────────────────────────────────────────────────

UNODB_TEST(BulkLoadStructural, BulkLoadPrefix7) {
  u64_db db;
  std::vector<std::pair<std::uint64_t, value_view>> kv{
      {0x0102030405060700ULL, val}, {0x0102030405060701ULL, val}};
  db.bulk_load(kv.begin(), kv.end());
  const auto c = db.get_node_counts();
  UNODB_ASSERT_EQ(c[as_i<node_type::I4>], 1U);
  UNODB_ASSERT_EQ(c[as_i<node_type::LEAF>], 2U);
}

UNODB_TEST(BulkLoadStructural, BulkLoadPrefix8) {
  using unodb::test::key_view_db;
  std::vector<std::vector<std::byte>> s{
      {std::byte{1}, std::byte{2}, std::byte{3}, std::byte{4}, std::byte{5},
       std::byte{6}, std::byte{7}, std::byte{8}, std::byte{0}},
      {std::byte{1}, std::byte{2}, std::byte{3}, std::byte{4}, std::byte{5},
       std::byte{6}, std::byte{7}, std::byte{8}, std::byte{1}}};
  std::vector<std::pair<key_view, value_view>> kv;
  for (auto& v : s)
    kv.emplace_back(  // NOLINT(performance-inefficient-vector-operation)
        key_view{v}, large_val);
  key_view_db db;
  db.bulk_load(kv.begin(), kv.end());
  const auto c = db.get_node_counts();
  UNODB_ASSERT_EQ(c[as_i<node_type::I4>], 2U);
  UNODB_ASSERT_EQ(c[as_i<node_type::LEAF>], 2U);
}

UNODB_TEST(BulkLoadStructural, BulkLoadPrefix15) {
  using unodb::test::key_view_db;
  std::vector<std::vector<std::byte>> s(
      2, std::vector<std::byte>(16, std::byte{0xAA}));
  s[0][15] = std::byte{0};
  s[1][15] = std::byte{1};
  std::vector<std::pair<key_view, value_view>> kv;
  for (auto& v : s)
    kv.emplace_back(  // NOLINT(performance-inefficient-vector-operation)
        key_view{v}, large_val);
  key_view_db db;
  db.bulk_load(kv.begin(), kv.end());
  const auto c = db.get_node_counts();
  UNODB_ASSERT_EQ(c[as_i<node_type::I4>], 2U);
  UNODB_ASSERT_EQ(c[as_i<node_type::LEAF>], 2U);
}

UNODB_TEST(BulkLoadStructural, BulkLoadPrefix16) {
  using unodb::test::key_view_db;
  std::vector<std::vector<std::byte>> s(
      2, std::vector<std::byte>(17, std::byte{0xBB}));
  s[0][16] = std::byte{0};
  s[1][16] = std::byte{1};
  std::vector<std::pair<key_view, value_view>> kv;
  for (auto& v : s)
    kv.emplace_back(  // NOLINT(performance-inefficient-vector-operation)
        key_view{v}, large_val);
  key_view_db db;
  db.bulk_load(kv.begin(), kv.end());
  const auto c = db.get_node_counts();
  UNODB_ASSERT_EQ(c[as_i<node_type::I4>], 3U);
  UNODB_ASSERT_EQ(c[as_i<node_type::LEAF>], 2U);
}

UNODB_TEST(BulkLoadStructural, BulkLoadVIS) {
  using unodb::test::key_view_u64val_db;
  std::vector<std::vector<std::byte>> s{{std::byte{1}}, {std::byte{2}}};
  std::vector<std::pair<key_view, std::uint64_t>> kv;
  kv.reserve(s.size());
  for (auto& v : s)
    kv.emplace_back(  // NOLINT(performance-inefficient-vector-operation)
        key_view{v}, 42ULL);
  key_view_u64val_db db;
  db.bulk_load(kv.begin(), kv.end());
  const auto c = db.get_node_counts();
  UNODB_ASSERT_EQ(c[as_i<node_type::I4>], 1U);
  UNODB_ASSERT_EQ(c[as_i<node_type::LEAF>], 0U);
}

UNODB_TEST(BulkLoadStructural, BulkLoadVISWithChain) {
  using unodb::test::key_view_u64val_db;
  std::vector<std::vector<std::byte>> s{{std::byte{1}, std::byte{0xAA}},
                                        {std::byte{1}, std::byte{0xBB}}};
  std::vector<std::pair<key_view, std::uint64_t>> kv;
  kv.reserve(s.size());
  for (auto& v : s)
    kv.emplace_back(  // NOLINT(performance-inefficient-vector-operation)
        key_view{v}, 99ULL);
  key_view_u64val_db db;
  db.bulk_load(kv.begin(), kv.end());
  const auto c = db.get_node_counts();
  UNODB_ASSERT_EQ(c[as_i<node_type::I4>], 1U);
  UNODB_ASSERT_EQ(c[as_i<node_type::LEAF>], 0U);
}

UNODB_TEST(BulkLoadStructural, BulkLoadVISLongPrefix) {
  using unodb::test::key_view_u64val_db;
  std::vector<std::vector<std::byte>> s(
      2, std::vector<std::byte>(9, std::byte{0xCC}));
  s[0][8] = std::byte{0};
  s[1][8] = std::byte{1};
  std::vector<std::pair<key_view, std::uint64_t>> kv;
  kv.reserve(s.size());
  for (auto& v : s)
    kv.emplace_back(  // NOLINT(performance-inefficient-vector-operation)
        key_view{v}, 77ULL);
  key_view_u64val_db db;
  db.bulk_load(kv.begin(), kv.end());
  const auto c = db.get_node_counts();
  UNODB_ASSERT_EQ(c[as_i<node_type::I4>], 2U);
  UNODB_ASSERT_EQ(c[as_i<node_type::LEAF>], 0U);
}

UNODB_TEST(BulkLoadStructural, BulkLoadKeylessLeaf) {
  using unodb::test::key_view_db;
  std::vector<std::vector<std::byte>> s{
      {std::byte{1}, std::byte{2}, std::byte{3}},
      {std::byte{4}, std::byte{5}, std::byte{6}}};
  std::vector<std::pair<key_view, value_view>> kv;
  for (auto& v : s)
    kv.emplace_back(  // NOLINT(performance-inefficient-vector-operation)
        key_view{v}, large_val);
  key_view_db db;
  db.bulk_load(kv.begin(), kv.end());
  const auto c = db.get_node_counts();
  UNODB_ASSERT_EQ(c[as_i<node_type::I4>], 3U);
  UNODB_ASSERT_EQ(c[as_i<node_type::LEAF>], 2U);
}

UNODB_TEST(BulkLoadStructural, BulkLoadKeylessLeafWithChain) {
  using unodb::test::key_view_db;
  std::vector<std::vector<std::byte>> s{
      {std::byte{1}, std::byte{0xAA}, std::byte{0xFF}},
      {std::byte{1}, std::byte{0xBB}, std::byte{0xFF}}};
  std::vector<std::pair<key_view, value_view>> kv;
  for (auto& v : s)
    kv.emplace_back(  // NOLINT(performance-inefficient-vector-operation)
        key_view{v}, large_val);
  key_view_db db;
  db.bulk_load(kv.begin(), kv.end());
  const auto c = db.get_node_counts();
  UNODB_ASSERT_EQ(c[as_i<node_type::I4>], 3U);
  UNODB_ASSERT_EQ(c[as_i<node_type::LEAF>], 2U);
}

UNODB_TEST(BulkLoadStructural, BulkLoadLarge) {
  std::mt19937 rng(42);  // NOLINT(cert-msc32-c,cert-msc51-cpp)
  std::vector<std::pair<std::uint64_t, value_view>> kv;
  kv.reserve(100000);
  UNODB_DETAIL_DISABLE_GCC_WARNING("-Wuseless-cast")
  for (int i = 0; i < 100000; ++i)
    kv.emplace_back(  // NOLINT(performance-inefficient-vector-operation)
        (static_cast<std::uint64_t>(rng()) << 32U) | rng(), val);
  UNODB_DETAIL_RESTORE_GCC_WARNINGS()
  std::ranges::sort(kv, {}, &decltype(kv)::value_type::first);
  kv.erase(std::unique(  // NOLINT(modernize-use-ranges)
               kv.begin(), kv.end(),
               [](const auto& a, const auto& b) { return a.first == b.first; }),
           kv.end());
  u64_db db;
  db.bulk_load(kv.begin(), kv.end());
  for (const auto& [k, v] : kv) UNODB_ASSERT_TRUE(db.get(k).has_value());
  std::uint64_t prev = 0;
  bool first = true;
  UNODB_DETAIL_DISABLE_MSVC_WARNING(26440)
  db.scan([&](auto& visitor) {
    const auto k = decode(visitor.get_key());
    if (!first) {
      UNODB_DETAIL_DISABLE_MSVC_WARNING(6326)
      UNODB_DETAIL_DISABLE_MSVC_WARNING(26818)
      EXPECT_GE(k, prev);
      UNODB_DETAIL_RESTORE_MSVC_WARNINGS()
      UNODB_DETAIL_RESTORE_MSVC_WARNINGS()
    }
    prev = k;
    first = false;
    return false;
  });
  UNODB_DETAIL_RESTORE_MSVC_WARNINGS()
}

UNODB_TEST(BulkLoadStructural, BulkLoadKeyView) {
  using unodb::test::key_view_db;
  constexpr std::size_t key_len = 10;
  std::mt19937 rng(123);  // NOLINT(cert-msc32-c,cert-msc51-cpp)
  std::vector<std::vector<std::byte>> storage;
  for (int i = 0; i < 1000; ++i) {
    std::vector<std::byte> k(key_len);
    for (auto& b : k) b = static_cast<std::byte>(rng() & 0xFFU);
    storage.push_back(std::move(k));
  }
  std::ranges::sort(storage);
  // NOLINTNEXTLINE(modernize-use-ranges)
  storage.erase(std::unique(storage.begin(), storage.end()), storage.end());
  std::vector<std::pair<key_view, value_view>> kv;
  kv.reserve(storage.size());
  for (auto& v : storage)
    kv.emplace_back(  // NOLINT(performance-inefficient-vector-operation)
        key_view{v}, large_val);
  key_view_db db;
  db.bulk_load(kv.begin(), kv.end());
  for (const auto& [k, v] : kv) UNODB_ASSERT_TRUE(db.get(k).has_value());
}

UNODB_TEST(BulkLoadStructural, BulkLoadVISRootSingle) {
  using unodb::test::key_view_u64val_db;
  std::vector<std::vector<std::byte>> s{{std::byte{1}, std::byte{2}}};
  std::vector<std::pair<key_view, std::uint64_t>> kv;
  kv.emplace_back(  // NOLINT(performance-inefficient-vector-operation)
      key_view{s[0]}, 55ULL);
  key_view_u64val_db db;
  db.bulk_load(kv.begin(), kv.end());
  const auto c = db.get_node_counts();
  UNODB_ASSERT_EQ(c[as_i<node_type::I4>], 1U);
  UNODB_ASSERT_EQ(c[as_i<node_type::LEAF>], 0U);
  UNODB_ASSERT_TRUE(db.get(key_view{s[0]}).has_value());
}

UNODB_TEST(BulkLoadStructural, BulkLoadKeylessLeafRootSingle) {
  using unodb::test::key_view_db;
  std::vector<std::vector<std::byte>> s{
      {std::byte{1}, std::byte{2}, std::byte{3}}};
  std::vector<std::pair<key_view, value_view>> kv;
  kv.emplace_back(  // NOLINT(performance-inefficient-vector-operation)
      key_view{s[0]}, large_val);
  key_view_db db;
  db.bulk_load(kv.begin(), kv.end());
  UNODB_ASSERT_TRUE(db.get(key_view{s[0]}).has_value());
}

UNODB_TEST(BulkLoadStructural, BulkLoadFullLeafRootSingle) {
  u64_db db;
  std::vector<std::pair<std::uint64_t, value_view>> kv{{0xDEADBEEFULL, val}};
  db.bulk_load(kv.begin(), kv.end());
  const auto c = db.get_node_counts();
  UNODB_ASSERT_EQ(c[as_i<node_type::LEAF>], 1U);
  UNODB_ASSERT_EQ(c[as_i<node_type::I4>], 0U);
}

UNODB_TEST(BulkLoadStructural, BulkLoadScanOrder) {
  std::vector<std::pair<std::uint64_t, value_view>> kv;
  for (std::uint64_t i = 0; i < 256; ++i)
    kv.emplace_back(  // NOLINT(performance-inefficient-vector-operation)
        i << 56U, val);
  u64_db db;
  db.bulk_load(kv.begin(), kv.end());
  std::uint64_t prev = 0;
  std::size_t count = 0;
  UNODB_DETAIL_DISABLE_MSVC_WARNING(26440)
  db.scan([&](auto& visitor) {
    const auto k = decode(visitor.get_key());
    if (count > 0) {
      UNODB_EXPECT_GT(k, prev);
    }
    prev = k;
    ++count;
    return false;
  });
  UNODB_DETAIL_RESTORE_MSVC_WARNINGS()
  UNODB_ASSERT_EQ(count, 256U);
}

UNODB_TEST(BulkLoadStructural, BulkLoadVISNode16) {
  using unodb::test::key_view_u64val_db;
  std::vector<std::vector<std::byte>> s;
  s.reserve(8);
  for (int i = 0; i < 8; ++i) {
    s.push_back({static_cast<std::byte>(i)});
  }
  std::vector<std::pair<key_view, std::uint64_t>> kv;
  kv.reserve(s.size());
  for (auto& v : s) kv.emplace_back(key_view{v}, 42ULL);
  key_view_u64val_db db;
  db.bulk_load(kv.begin(), kv.end());
  const auto c = db.get_node_counts();
  UNODB_ASSERT_EQ(c[as_i<node_type::I16>], 1U);
  UNODB_ASSERT_EQ(c[as_i<node_type::LEAF>], 0U);
  for (const auto& [k, v] : kv) {
    UNODB_ASSERT_TRUE(db.get(k).has_value());
  }
}

UNODB_TEST(BulkLoadStructural, BulkLoadVISNode48) {
  using unodb::test::key_view_u64val_db;
  std::vector<std::vector<std::byte>> s;
  s.reserve(20);
  for (int i = 0; i < 20; ++i) {
    s.push_back({static_cast<std::byte>(i)});
  }
  std::vector<std::pair<key_view, std::uint64_t>> kv;
  kv.reserve(s.size());
  for (auto& v : s) kv.emplace_back(key_view{v}, 42ULL);
  key_view_u64val_db db;
  db.bulk_load(kv.begin(), kv.end());
  const auto c = db.get_node_counts();
  UNODB_ASSERT_EQ(c[as_i<node_type::I48>], 1U);
  UNODB_ASSERT_EQ(c[as_i<node_type::LEAF>], 0U);
  for (const auto& [k, v] : kv) {
    UNODB_ASSERT_TRUE(db.get(k).has_value());
  }
}

UNODB_TEST(BulkLoadStructural, BulkLoadVISNode256) {
  using unodb::test::key_view_u64val_db;
  std::vector<std::vector<std::byte>> s;
  s.reserve(60);
  for (int i = 0; i < 60; ++i) {
    s.push_back({static_cast<std::byte>(i)});
  }
  std::vector<std::pair<key_view, std::uint64_t>> kv;
  kv.reserve(s.size());
  for (auto& v : s) kv.emplace_back(key_view{v}, 42ULL);
  key_view_u64val_db db;
  db.bulk_load(kv.begin(), kv.end());
  const auto c = db.get_node_counts();
  UNODB_ASSERT_EQ(c[as_i<node_type::I256>], 1U);
  UNODB_ASSERT_EQ(c[as_i<node_type::LEAF>], 0U);
  for (const auto& [k, v] : kv) {
    UNODB_ASSERT_TRUE(db.get(k).has_value());
  }
}

// ─── Stats-dependent Operational Tests ───────────────────────────────────────

UNODB_TEST(BulkLoadOps, Stats) {
  u64_db db;
  std::vector<std::pair<std::uint64_t, value_view>> kv;
  kv.reserve(17);
  for (std::uint64_t i = 0; i < 17; ++i) {
    kv.emplace_back(i << 56U, val);
  }
  std::ranges::sort(kv, {}, &decltype(kv)::value_type::first);
  db.bulk_load(kv.begin(), kv.end());
  const auto counts = db.get_node_counts();
  UNODB_ASSERT_EQ(counts[as_i<node_type::LEAF>], 17U);
  UNODB_ASSERT_EQ(counts[as_i<node_type::I4>], 0U);
  UNODB_ASSERT_EQ(counts[as_i<node_type::I16>], 0U);
  UNODB_ASSERT_EQ(counts[as_i<node_type::I48>], 1U);
  UNODB_ASSERT_EQ(counts[as_i<node_type::I256>], 0U);
}

#endif  // UNODB_DETAIL_WITH_STATS

// ─── Error Tests (no stats dependency) ───────────────────────────────────────

UNODB_TEST(BulkLoadError, NonEmpty) {
  u64_db db;
  constexpr std::uint64_t key = 42;
  UNODB_ASSERT_TRUE(db.insert(key, val));
  std::vector<std::pair<std::uint64_t, value_view>> kv{{100, val}};
  UNODB_DETAIL_DISABLE_MSVC_WARNING(6326)
  UNODB_DETAIL_DISABLE_MSVC_WARNING(26818)
  EXPECT_THROW(db.bulk_load(kv.begin(), kv.end()), std::invalid_argument);
  UNODB_DETAIL_RESTORE_MSVC_WARNINGS()
  UNODB_DETAIL_RESTORE_MSVC_WARNINGS()
  const auto result = db.get(key);
  UNODB_ASSERT_TRUE(result.has_value());
}

UNODB_TEST(BulkLoadError, OlcNonEmpty) {
  u64_olc_db db;
  constexpr std::uint64_t key = 42;
  ASSERT_TRUE(db.insert(key, val));
  unodb::this_thread().quiescent();
  std::vector<std::pair<std::uint64_t, value_view>> kv{{100, val}};
  EXPECT_THROW(db.bulk_load(kv.begin(), kv.end()), std::invalid_argument);
  const auto result = db.get(key);
  ASSERT_TRUE(result.has_value());
}

UNODB_TEST(BulkLoadError, DbIgnoresParallelism) {
  u64_db db;
  std::vector<std::pair<std::uint64_t, value_view>> kv;
  kv.reserve(100);
  for (std::uint64_t i = 0; i < 100; ++i) {
    const auto key = i << 56U;
    kv.emplace_back(key, val);
  }
  std::ranges::sort(kv, {}, &decltype(kv)::value_type::first);
  db.bulk_load(
      [](auto&& f) {
        return std::async(std::launch::async, std::forward<decltype(f)>(f));
      },
      256, kv.begin(), kv.end());
  for (const auto& [k, v] : kv) {
    const auto result = db.get(k);
    ASSERT_TRUE(result.has_value()) << "key " << k << " not found";
  }
}

// ─── Operational Tests (no stats dependency) ─────────────────────────────────

UNODB_TEST(BulkLoadOps, ThenOperations) {
  u64_db db;
  std::vector<std::pair<std::uint64_t, value_view>> kv;
  kv.reserve(10);
  for (std::uint64_t i = 0; i < 10; ++i) {
    kv.emplace_back(i << 56U, val);
  }
  std::ranges::sort(kv, {}, &decltype(kv)::value_type::first);
  db.bulk_load(kv.begin(), kv.end());

  for (const auto& [k, v] : kv) {
    UNODB_ASSERT_TRUE(db.get(k).has_value());
  }
  constexpr std::uint64_t new_key = 0xFFULL << 56U;
  UNODB_ASSERT_TRUE(db.insert(new_key, val));
  UNODB_ASSERT_TRUE(db.get(new_key).has_value());
  UNODB_ASSERT_FALSE(db.insert(kv[0].first, val));
  UNODB_ASSERT_TRUE(db.remove(kv[0].first));
  UNODB_ASSERT_FALSE(db.get(kv[0].first).has_value());

  std::size_t count = 0;
  db.scan([&count](auto&) {
    ++count;
    return false;
  });
  UNODB_ASSERT_EQ(count, 10U);  // 10 - 1 removed + 1 new = 10
}

UNODB_TEST(BulkLoadOps, NoGrowthEvents) {
  u64_db db;
  std::vector<std::pair<std::uint64_t, value_view>> kv;
  kv.reserve(100);
  for (std::uint64_t i = 0; i < 100; ++i) {
    kv.emplace_back(i << 56U, val);
  }
  std::ranges::sort(kv, {}, &decltype(kv)::value_type::first);
  db.bulk_load(kv.begin(), kv.end());
  for (const auto& [k, v] : kv) {
    ASSERT_TRUE(db.get(k).has_value()) << "key " << k << " not found";
  }
}

UNODB_TEST(BulkLoadOps, MutexDb) {
  u64_mutex_db db;
  std::vector<std::pair<std::uint64_t, value_view>> kv;
  kv.reserve(100);
  for (std::uint64_t i = 0; i < 100; ++i) {
    kv.emplace_back(i << 56U, val);
  }
  std::ranges::sort(kv, {}, &decltype(kv)::value_type::first);
  db.bulk_load(kv.begin(), kv.end());
  for (const auto& [k, v] : kv) {
    const auto result = db.get(k);
    ASSERT_TRUE(result.first.has_value()) << "key " << k << " not found";
  }
}

UNODB_TEST(BulkLoadOps, ClearAndReload) {
  u64_db db;
  std::vector<std::pair<std::uint64_t, value_view>> kv;
  kv.reserve(10);
  for (std::uint64_t i = 0; i < 10; ++i) {
    kv.emplace_back(i << 56U, val);
  }
  std::ranges::sort(kv, {}, &decltype(kv)::value_type::first);
  db.bulk_load(kv.begin(), kv.end());
  db.clear();
  UNODB_ASSERT_TRUE(db.empty());
  std::vector<std::pair<std::uint64_t, value_view>> kv2;
  kv2.reserve(10);
  for (std::uint64_t i = 100; i < 110; ++i) {
    kv2.emplace_back(i << 56U, val);
  }
  std::ranges::sort(kv2, {}, &decltype(kv2)::value_type::first);
  db.bulk_load(kv2.begin(), kv2.end());
  for (const auto& [k, v] : kv2) {
    UNODB_ASSERT_TRUE(db.get(k).has_value());
  }
}

UNODB_TEST(BulkLoadOps, OlcDbParallel) {
  u64_olc_db db;
  std::vector<std::pair<std::uint64_t, value_view>> kv;
  kv.reserve(1000);
  for (std::uint64_t i = 0; i < 1000; ++i) {
    kv.emplace_back(i << 48U, val);
  }
  std::ranges::sort(kv, {}, &decltype(kv)::value_type::first);
  db.bulk_load(
      [](auto&& f) {
        return std::async(std::launch::async, std::forward<decltype(f)>(f));
      },
      256, kv.begin(), kv.end());
  for (const auto& [k, v] : kv) {
    const auto result = db.get(k);
    ASSERT_TRUE(result.has_value()) << "key " << k << " not found";
  }
}

UNODB_TEST(BulkLoadOps, OlcDbConcurrentReaders) {
  u64_olc_db db;
  constexpr std::size_t n_keys = 10000;
  std::vector<std::pair<std::uint64_t, value_view>> kv;
  kv.reserve(n_keys);
  for (std::uint64_t i = 0; i < n_keys; ++i) {
    kv.emplace_back(i << 40U, val);
  }
  std::ranges::sort(kv, {}, &decltype(kv)::value_type::first);
  db.bulk_load(
      [](auto&& f) {
        return std::async(std::launch::async, std::forward<decltype(f)>(f));
      },
      256, kv.begin(), kv.end());

  unodb::this_thread().qsbr_pause();

  constexpr std::size_t n_threads = 4;
  std::array<unodb::qsbr_thread, n_threads> threads;
  for (std::size_t t = 0; t < n_threads; ++t) {
    threads[t] = unodb::qsbr_thread([&kv, &db] {
      for (const auto& [k, v] : kv) {
        const unodb::quiescent_state_on_scope_exit qsbr{};
        const auto result = db.get(k);
        EXPECT_TRUE(result.has_value()) << "key " << k << " not found";
      }
      unodb::this_thread().quiescent();
    });
  }
  for (auto& t : threads) t.join();

  unodb::this_thread().qsbr_resume();
  unodb::this_thread().quiescent();
  unodb::test::expect_idle_qsbr();
}

// ─── Parallel Path Coverage ──────────────────────────────────────────────────

UNODB_TEST(BulkLoadOps, ParallelInlineRemainder) {
  u64_db db;
  std::vector<std::pair<std::uint64_t, value_view>> kv;
  kv.reserve(100);
  for (std::uint64_t i = 0; i < 100; ++i) {
    kv.emplace_back(i << 56U, val);
  }
  std::ranges::sort(kv, {}, &decltype(kv)::value_type::first);
  db.bulk_load(
      [](auto&& f) {
        return std::async(std::launch::async, std::forward<decltype(f)>(f));
      },
      4, kv.begin(), kv.end());
  for (const auto& [k, v] : kv) {
    ASSERT_TRUE(db.get(k).has_value()) << "key " << k << " not found";
  }
}

UNODB_TEST(BulkLoadOps, ParallelSingleElement) {
  u64_db db;
  std::vector<std::pair<std::uint64_t, value_view>> kv;
  kv.emplace_back(42ULL << 56U, val);
  db.bulk_load(
      [](auto&& f) {
        return std::async(std::launch::async, std::forward<decltype(f)>(f));
      },
      4, kv.begin(), kv.end());
  ASSERT_TRUE(db.get(42ULL << 56U).has_value());
}

UNODB_TEST(BulkLoadOps, ParallelPrefixChain) {
  using unodb::test::key_view_db;
  key_view_db db;
  std::vector<std::vector<std::byte>> raw_keys;
  raw_keys.reserve(20);
  for (int i = 0; i < 20; ++i) {
    std::vector<std::byte> k(13);
    for (int j = 0; j < 10; ++j) {
      k[static_cast<std::size_t>(j)] = static_cast<std::byte>(j + 1);
    }
    k[10] = static_cast<std::byte>(i);
    k[11] = std::byte{0xAA};
    k[12] = std::byte{0xBB};
    raw_keys.push_back(std::move(k));
  }
  std::vector<std::pair<unodb::key_view, value_view>> kv;
  kv.reserve(raw_keys.size());
  for (auto& k : raw_keys) {
    kv.emplace_back(unodb::key_view{k.data(), k.size()}, val);
  }
  db.bulk_load(
      [](auto&& f) {
        return std::async(std::launch::async, std::forward<decltype(f)>(f));
      },
      4, kv.begin(), kv.end());
  for (const auto& [k, v] : kv) {
    ASSERT_TRUE(db.get(k).has_value());
  }
}

UNODB_TEST(BulkLoadOps, OlcDbParallelInline) {
  u64_olc_db db;
  std::vector<std::pair<std::uint64_t, value_view>> kv;
  kv.reserve(50);
  for (std::uint64_t i = 0; i < 50; ++i) {
    kv.emplace_back(i << 56U, val);
  }
  std::ranges::sort(kv, {}, &decltype(kv)::value_type::first);
  db.bulk_load(
      [](auto&& f) {
        return std::async(std::launch::async, std::forward<decltype(f)>(f));
      },
      4, kv.begin(), kv.end());
  for (const auto& [k, v] : kv) {
    const auto result = db.get(k);
    ASSERT_TRUE(result.has_value()) << "key " << k << " not found";
  }
}

UNODB_TEST(BulkLoadOps, OlcDbParallelSharedPrefix) {
  u64_olc_db db;
  std::vector<std::pair<std::uint64_t, value_view>> kv;
  kv.reserve(20);
  for (std::uint64_t i = 0; i < 20; ++i) {
    kv.emplace_back((1ULL << 56U) | (i << 48U), val);
  }
  std::ranges::sort(kv, {}, &decltype(kv)::value_type::first);
  db.bulk_load(
      [](auto&& f) {
        return std::async(std::launch::async, std::forward<decltype(f)>(f));
      },
      4, kv.begin(), kv.end());
  for (const auto& [k, v] : kv) {
    const auto result = db.get(k);
    ASSERT_TRUE(result.has_value()) << "key " << k << " not found";
  }
}

}  // namespace

UNODB_DETAIL_RESTORE_MSVC_WARNINGS()
UNODB_DETAIL_RESTORE_MSVC_WARNINGS()
UNODB_DETAIL_RESTORE_MSVC_WARNINGS()
