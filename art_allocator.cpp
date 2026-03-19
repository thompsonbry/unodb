// Copyright 2026 UnoDB contributors

// Should be the first include
#include "global.hpp"

#include "art_allocator.hpp"

#include <cstddef>

#include "heap.hpp"
#include "qsbr.hpp"

namespace unodb::detail {

void* default_alloc(std::size_t size, std::size_t alignment,
                    void* /*ctx*/) noexcept(false) {
  return allocate_aligned(size, alignment);
}

void default_dealloc(void* ptr, std::size_t /*size*/,
                     void* /*ctx*/) noexcept {
  free_aligned(ptr);
}

void default_destroy(void* ptr, std::size_t size, void* ctx) noexcept {
  default_dealloc(ptr, size, ctx);
}

void default_defer_dealloc(void* ptr, std::size_t size,
                           destroy_callback_type /*destroy_callback*/,
                           void* /*ctx*/) noexcept(false) {
  this_thread().on_next_epoch_deallocate(ptr
#ifdef UNODB_DETAIL_WITH_STATS
                                         ,
                                         size
#endif
#ifndef NDEBUG
                                         ,
                                         nullptr
#endif
  );
  (void)size;
}

}  // namespace unodb::detail
