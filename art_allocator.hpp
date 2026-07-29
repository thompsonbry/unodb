// Copyright 2026 UnoDB contributors
#ifndef UNODB_DETAIL_ART_ALLOCATOR_HPP
#define UNODB_DETAIL_ART_ALLOCATOR_HPP

/// \file
/// Pluggable allocator for ART trees (header-only, no QSBR dependency).
///
/// Defines allocation, deallocation, and optional deferred-deallocation
/// callbacks.  The default uses the built-in aligned heap (heap.hpp) and does
/// not provide deferred deallocation.
///
/// \see https://github.com/unodb-dev/unodb/issues/837

// Should be the first include
#include "global.hpp"

#include <cstddef>

#include "heap.hpp"

namespace unodb {

/// Callback invoked when a deferred deallocation is safe to execute.
using destroy_callback_type = void (*)(void* ptr, std::size_t size, void* ctx);

/// Pluggable allocator for ART trees.
///
/// \a alloc and \a dealloc must be non-null.  \a defer_dealloc must be
/// non-null when deferred deallocation is used and may otherwise be null.
/// \a ctx is forwarded to every callback and may be nullptr.
///
/// \a defer_dealloc schedules \a destroy_callback for an allocation that
/// cannot be reclaimed immediately.
struct allocator_type {
  /// Allocate `size` bytes with the given `alignment`. May throw on failure.
  void* (*alloc)(std::size_t size, std::size_t alignment, void* ctx);
  /// Free a previously allocated block of `size` bytes at `ptr`.
  void (*dealloc)(void* ptr, std::size_t size, void* ctx);
  /// Schedule deferred deallocation of `ptr` (`size` bytes). Calls
  /// `destroy_callback` when reclamation is safe.
  void (*defer_dealloc)(void* ptr, std::size_t size,
                        destroy_callback_type destroy_callback, void* ctx);
  /// Opaque context forwarded to all callbacks.
  void* ctx;
};

namespace detail {

/// Default alloc: delegates to allocate_aligned (heap.hpp).
inline void* default_alloc(std::size_t size, std::size_t alignment,
                           void* /*ctx*/) {
  return allocate_aligned(size, alignment);
}

/// Default dealloc: delegates to free_aligned (heap.hpp).
inline void default_dealloc(void* ptr, std::size_t /*size*/,
                            void* /*ctx*/) noexcept {
  free_aligned(ptr);
}

/// Default destroy callback: frees via default_dealloc.
/// Passed as the destroy_callback argument to defer_dealloc.
inline void default_destroy(void* ptr, std::size_t size, void* ctx) noexcept {
  default_dealloc(ptr, size, ctx);
}

/// The default allocator instance without deferred deallocation.
inline constexpr allocator_type default_allocator{
    &default_alloc, &default_dealloc, nullptr, nullptr};

}  // namespace detail

}  // namespace unodb

#endif  // UNODB_DETAIL_ART_ALLOCATOR_HPP
