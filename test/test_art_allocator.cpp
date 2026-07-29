// Copyright 2026 UnoDB contributors

// Should be the first include
#include "global.hpp"  // IWYU pragma: keep

#include <array>
#include <cstddef>
#include <cstdint>
#include <type_traits>

#include "art_allocator.hpp"
#include "art_common.hpp"
#include "gtest_utils.hpp"
#include "heap.hpp"
#include "mutex_art.hpp"
#include "olc_art.hpp"
#include "qsbr.hpp"

namespace {

static_assert(std::is_nothrow_invocable_v<unodb::destroy_callback_type, void*,
                                          std::size_t, void*>);
static_assert(
    std::is_nothrow_invocable_v<decltype(unodb::allocator_type::dealloc), void*,
                                std::size_t, void*>);

// Exercise the custom allocator constructor and get_allocator() for each db
// type. Also exercises deferred reclamation through the QSBR-based
// olc_default_allocator by performing insert+remove on olc_db.

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

// A deferred node must be reclaimed through the allocator's own dealloc, not
// through the built-in heap: an allocator serving memory from a private heap
// would otherwise have its removed nodes freed by the wrong deallocator.

/// Counts allocator callbacks for one test allocator.
struct counting_arena final {
  /// Number of allocation callbacks.
  std::size_t allocs{0};
  /// Number of deallocation callbacks.
  std::size_t deallocs{0};
};

/// Allocate through the counting allocator.
[[nodiscard]] void* counting_alloc(std::size_t size, std::size_t alignment,
                                   void* ctx) {
  ++static_cast<counting_arena*>(ctx)->allocs;
  return unodb::detail::allocate_aligned(size, alignment);
}

/// Deallocate through the counting allocator.
void counting_dealloc(void* ptr, std::size_t /*size*/, void* ctx) noexcept {
  ++static_cast<counting_arena*>(ctx)->deallocs;
  unodb::detail::free_aligned(ptr);
}

/// Execute a deferred deallocation immediately.
void immediate_defer(void* ptr, std::size_t size,
                     unodb::destroy_callback_type destroy_callback,
                     void* ctx) noexcept {
  destroy_callback(ptr, size, ctx);
}

UNODB_TEST(ArtAllocator, OlcDbDeferredFreeUsesAllocatorDealloc) {
  counting_arena arena{};
  const unodb::allocator_type alloc{.alloc = &counting_alloc,
                                    .dealloc = &counting_dealloc,
                                    .defer_dealloc = &immediate_defer,
                                    .ctx = &arena};
  {
    unodb::olc_db<std::uint64_t, unodb::value_view> db{alloc};

    constexpr std::uint64_t first_key = 42;
    constexpr std::uint64_t second_key = 43;
    const auto val_data = std::array{std::byte{0xAB}};
    UNODB_ASSERT_TRUE(db.insert(first_key, unodb::value_view{val_data}));
    UNODB_ASSERT_TRUE(db.insert(second_key, unodb::value_view{val_data}));
    UNODB_ASSERT_EQ(arena.allocs, 3);

    UNODB_ASSERT_TRUE(db.remove(first_key));
    UNODB_ASSERT_EQ(arena.deallocs, 2);
  }
  UNODB_ASSERT_EQ(arena.deallocs, arena.allocs);
}

}  // namespace
