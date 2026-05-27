// Copyright 2026 UnoDB contributors

/// \file
/// Regression test: olc_db with a custom allocator must not require
/// libunodb_qsbr.  This executable is intentionally linked without
/// unodb_qsbr to verify the QSBR link decoupling.

// Should be the first include
#include "global.hpp"  // IWYU pragma: keep

#include <cstddef>
#include <cstdint>
#include <cstdlib>

#include "art_allocator.hpp"
#include "olc_art.hpp"

namespace {

void* test_alloc(std::size_t size, std::size_t alignment, void* /*ctx*/) {
  return unodb::detail::allocate_aligned(size, alignment);
}

void test_dealloc(void* ptr, std::size_t /*size*/, void* /*ctx*/) noexcept {
  unodb::detail::free_aligned(ptr);
}

// Immediate destroy -- no true deferral (verifies link decoupling, not GC).
void test_defer(void* ptr, std::size_t size, unodb::destroy_callback_type cb,
                void* ctx) noexcept {
  cb(ptr, size, ctx);
}

}  // namespace

int main() {
  const unodb::allocator_type alloc{&test_alloc, &test_dealloc, &test_defer,
                                    nullptr};
  unodb::olc_db<std::uint64_t, std::uint64_t> db{alloc};

  if (!db.empty()) return EXIT_FAILURE;

  // Exercise alloc (insert) and defer_dealloc (remove).
  if (!db.insert(42, 100)) return EXIT_FAILURE;
  if (db.empty()) return EXIT_FAILURE;
  if (!db.remove(42)) return EXIT_FAILURE;
  if (!db.empty()) return EXIT_FAILURE;

  return EXIT_SUCCESS;
}
