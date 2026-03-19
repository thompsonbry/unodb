// Copyright 2026 UnoDB contributors
#ifndef UNODB_DETAIL_ART_ALLOCATOR_HPP
#define UNODB_DETAIL_ART_ALLOCATOR_HPP

/// \file
/// Pluggable allocator for ART trees.
///
/// Trees accept an allocator_type at construction time.  The default
/// allocator uses the built-in aligned heap (heap.hpp) and QSBR for
/// deferred deallocation.  External integrators can supply their own
/// allocator to route allocations through a custom heap and deferred
/// free through an external epoch-based GC system.
///
/// Inspired by https://nullprogram.com/blog/2023/12/17/ with the
/// addition of a deferred-free callback.
///
/// \see https://github.com/unodb-dev/unodb/issues/837

// Should be the first include
#include "global.hpp"

#include <cstddef>

namespace unodb {

/// Callback invoked when a deferred deallocation is safe to execute.
/// \param ptr   Pointer to the memory to free.
/// \param size  Size of the allocation in bytes.
/// \param ctx   Opaque context from allocator_type::ctx.
using destroy_callback_type = void (*)(void* ptr, std::size_t size, void* ctx);

/// Pluggable allocator for ART trees.
///
/// Passed at tree construction time.  All three function pointers must
/// be non-null.  \a ctx is forwarded to every callback and may be
/// nullptr if the callbacks do not need external state.
///
/// \a defer_dealloc is called when a node is removed from a concurrent
/// tree and cannot be freed immediately because readers may still hold
/// pointers.  The implementation must ensure the memory is freed only
/// after all concurrent readers have finished.  The \a destroy_callback
/// parameter is the function that should ultimately free the memory;
/// the \a defer_dealloc implementation may call it immediately (for
/// single-threaded trees) or queue it for later execution.
struct allocator_type {
  void* (*alloc)(std::size_t size, std::size_t alignment, void* ctx);
  void (*dealloc)(void* ptr, std::size_t size, void* ctx);
  void (*defer_dealloc)(void* ptr, std::size_t size,
                        destroy_callback_type destroy_callback, void* ctx);
  void* ctx;
};

namespace detail {

/// Default alloc: delegates to allocate_aligned (heap.hpp).
void* default_alloc(std::size_t size, std::size_t alignment,
                    void* ctx) noexcept(false);

/// Default dealloc: delegates to free_aligned (heap.hpp).
void default_dealloc(void* ptr, std::size_t size, void* ctx) noexcept;

/// Default defer_dealloc: queues through QSBR (qsbr_per_thread::
/// on_next_epoch_deallocate).  Used by olc_db when no custom allocator
/// is provided.
void default_defer_dealloc(void* ptr, std::size_t size,
                           destroy_callback_type destroy_callback,
                           void* ctx) noexcept(false);

/// Default destroy callback: calls default_dealloc.
void default_destroy(void* ptr, std::size_t size, void* ctx) noexcept;

/// The default allocator instance.
inline constexpr allocator_type default_allocator{
    &default_alloc, &default_dealloc, &default_defer_dealloc, nullptr};

}  // namespace detail

}  // namespace unodb

#endif  // UNODB_DETAIL_ART_ALLOCATOR_HPP
