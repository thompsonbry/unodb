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

/// Non-throwing callback invoked when deferred deallocation is safe to execute.
using destroy_callback_type = void (*)(void* ptr, std::size_t size,
                                       void* ctx) noexcept;

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
  /// Free a previously allocated block of `size` bytes at `ptr` without
  /// throwing.
  void (*dealloc)(void* ptr, std::size_t size, void* ctx) noexcept;
  /// Schedule deferred deallocation of `ptr` (`size` bytes). Calls
  /// `destroy_callback` when reclamation is safe. `destroy_callback` is
  /// \a dealloc, so the allocation is reclaimed through the same allocator;
  /// it may run on another thread and after the deferring one has exited, so
  /// \a dealloc and \a ctx must outlive all pending deferrals.
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

/// The default allocator instance without deferred deallocation.
inline constexpr allocator_type default_allocator{
    &default_alloc, &default_dealloc, nullptr, nullptr};

}  // namespace detail

}  // namespace unodb

#endif  // UNODB_DETAIL_ART_ALLOCATOR_HPP
