// Copyright 2026 UnoDB contributors

// Should be the first include
#include "global.hpp"  // IWYU pragma: keep

#include <array>
#include <cstddef>
#include <cstdint>

#include "art_allocator.hpp"
#include "art_common.hpp"
#include "gtest_utils.hpp"
#include "mutex_art.hpp"
#include "olc_art.hpp"
#include "qsbr.hpp"

namespace {

// Exercise the custom allocator constructor and get_allocator() for each db
// type. Also exercises default_defer_dealloc and default_destroy by using
// olc_db with the default (non-QSBR) allocator and performing insert+remove.

UNODB_TEST(ArtAllocator, DbCustomAllocatorConstructor) {
  const unodb::allocator_type alloc{unodb::detail::default_allocator};
  const unodb::db<std::uint64_t, unodb::value_view> db{alloc};
  UNODB_EXPECT_TRUE(db.empty());
  UNODB_EXPECT_EQ(db.get_allocator().alloc,
                  unodb::detail::default_allocator.alloc);
}

UNODB_TEST(ArtAllocator, MutexDbCustomAllocatorConstructor) {
  const unodb::allocator_type alloc{unodb::detail::default_allocator};
  const unodb::mutex_db<std::uint64_t, unodb::value_view> db{alloc};
  UNODB_EXPECT_TRUE(db.empty());
  UNODB_EXPECT_EQ(db.get_allocator().alloc,
                  unodb::detail::default_allocator.alloc);
}

UNODB_TEST(ArtAllocator, OlcDbDefaultAllocatorInsertRemove) {
  const unodb::quiescent_state_on_scope_exit qsbr{};
  const unodb::allocator_type alloc{unodb::detail::olc_default_allocator};
  unodb::olc_db<std::uint64_t, unodb::value_view> db{alloc};
  UNODB_EXPECT_TRUE(db.empty());

  constexpr std::uint64_t key = 42;
  const auto val_data = std::array{std::byte{0xAB}};
  const unodb::value_view val{val_data};
  UNODB_ASSERT_TRUE(db.insert(key, val));
  UNODB_ASSERT_FALSE(db.empty());

  UNODB_ASSERT_TRUE(db.remove(key));
  UNODB_EXPECT_TRUE(db.empty());
}

}  // namespace
