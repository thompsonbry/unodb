// Copyright 2026 UnoDB contributors
#ifndef UNODB_DETAIL_ART_ALLOCATOR_HPP
#define UNODB_DETAIL_ART_ALLOCATOR_HPP

/// \file
/// Pluggable allocator for ART trees (header-only, no QSBR dependency).
///
/// Trees accept an allocator_type at construction time.  The default
/// allocator uses the built-in aligned heap (heap.hpp) with immediate
/// deferred free.  OLC trees override defer_dealloc with a QSBR-based
/// implementation.  External integrators can supply their own allocator
/// to route allocations through a custom heap and deferred free through
/// an external epoch-based GC system.
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
/// All three function pointers must be non-null.  \a ctx is forwarded
/// to every callback and may be nullptr.
///
/// \a defer_dealloc is called when a node is removed and cannot be freed
/// immediately (concurrent readers may hold pointers).  For single-threaded
/// trees the default calls \a destroy_callback immediately.  OLC trees
/// replace this with QSBR-based deferred reclamation.
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

/// Default defer_dealloc: immediate free via destroy_callback.
/// Safe for db and mutex_db where no concurrent readers exist.
inline void default_defer_dealloc(void* ptr, std::size_t size,
                                  destroy_callback_type destroy_callback,
                                  void* ctx) noexcept {
  destroy_callback(ptr, size, ctx);
}

/// Default destroy callback: frees via default_dealloc.
/// Passed as the destroy_callback argument to defer_dealloc.
inline void default_destroy(void* ptr, std::size_t size, void* ctx) noexcept {
  default_dealloc(ptr, size, ctx);
}

/// The default allocator instance (no QSBR, immediate free).
inline constexpr allocator_type default_allocator{
    &default_alloc, &default_dealloc, &default_defer_dealloc, nullptr};

}  // namespace detail

}  // namespace unodb

#endif  // UNODB_DETAIL_ART_ALLOCATOR_HPP
