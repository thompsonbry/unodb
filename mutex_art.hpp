// Copyright 2019-2024 Laurynas Biveinis
#ifndef UNODB_DETAIL_MUTEX_ART_HPP
#define UNODB_DETAIL_MUTEX_ART_HPP

#include "global.hpp"

#include <mutex>
#include <utility>

#include "art.hpp"
#include "node_type.hpp"

namespace unodb {

class mutex_db final {
 public:
  // If the search key was found, that is, the first pair member has a value,
  // then the second member is a locked tree mutex which must be released ASAP
  // after reading the first pair member. Otherwise, the second member is
  // undefined.
  using get_result = std::pair<db::get_result, std::unique_lock<std::mutex>>;

  // Creation and destruction
  mutex_db() noexcept = default;

  // Querying
  [[nodiscard]] auto get(key k) const {
    std::unique_lock guard{mutex};
    const auto db_get_result{db_.get(k)};
    if (!db_get_result) {
      guard.unlock();
      return std::make_pair(db_get_result, std::unique_lock<std::mutex>{});
    }
    return std::make_pair(db_get_result, std::move(guard));
  }

  [[nodiscard]] auto empty() const {
    const std::lock_guard guard{mutex};
    return db_.empty();
  }

  // Modifying
  // Cannot be called during stack unwinding with std::uncaught_exceptions() > 0
  [[nodiscard]] auto insert(key k, value_view v) {
    const std::lock_guard guard{mutex};
    return db_.insert(k, v);
  }

  [[nodiscard]] auto remove(key k) {
    const std::lock_guard guard{mutex};
    return db_.remove(k);
  }

  void clear() {
    const std::lock_guard guard{mutex};
    db_.clear();
  }

  // visitor typedef for the scan() API
  using visitor = unodb::db::visitor;
  
  // Scan the tree, applying the caller's lambda to each visited leaf.
  //
  // @param fn A function f(visitor&) returning [bool::halt].  The
  // traversal will halt if the function returns [true].
  //
  // @param fwd When [true] perform a forward scan, otherwise perform
  // a reverse scan.
  template <typename FN>
  inline void scan(FN fn, bool fwd = true) noexcept {
    const std::lock_guard guard{mutex};
    db_.scan( fn, fwd );
  }
  
  // Scan in the indicated direction, applying the caller's lambda to
  // each visited leaf.
  //
  // @param fromKey is an inclusive bound for the starting point of
  // the scan.
  //
  // @param fn A function f(visitor&) returning [bool::halt].  The
  // traversal will halt if the function returns [true].
  //
  // @param fwd When [true] perform a forward scan, otherwise perform
  // a reverse scan.
  template <typename FN>
  inline void scan(const key fromKey, FN fn, bool fwd = true) noexcept {
    const std::lock_guard guard{mutex};
    db_.scan( fromKey, fn, fwd );
  }
  
  // Scan the key range, applying the caller's lambda to each visited
  // leaf.  The scan will proceed in lexicographic order iff fromKey
  // is less than toKey and in reverse lexicographic order iff toKey
  // is less than fromKey.
  //
  // @param fromKey is an inclusive bound for the starting point of
  // the scan.
  //
  // @param toKey is an exclusive bound for the ending point of the
  // scan.
  //
  // @param fn A function f(visitor&) returning [bool::halt].  The
  // traversal will halt if the function returns [true].
  template <typename FN>
  inline void scan(const key fromKey, const key toKey, FN fn) noexcept {
    const std::lock_guard guard{mutex};
    db_.scan( fromKey, toKey, fn );
  }
  
  //
  // TEST ONLY METHODS
  //

  // Used to write the iterator tests.
  auto __test_only_iterator__() noexcept {return db_.__test_only_iterator__();}
  
  // Stats
#ifdef UNODB_DETAIL_WITH_STATS

  [[nodiscard]] auto get_current_memory_use() const {
    const std::lock_guard guard{mutex};
    return db_.get_current_memory_use();
  }

  template <node_type NodeType>
  [[nodiscard]] auto get_node_count() const {
    const std::lock_guard guard{mutex};
    return db_.get_node_count<NodeType>();
  }

  [[nodiscard]] auto get_node_counts() const {
    const std::lock_guard guard{mutex};
    return db_.get_node_counts();
  }

  template <node_type NodeType>
  [[nodiscard]] auto get_growing_inode_count() const {
    const std::lock_guard guard{mutex};
    return db_.get_growing_inode_count<NodeType>();
  }

  [[nodiscard]] auto get_growing_inode_counts() const {
    const std::lock_guard guard{mutex};
    return db_.get_growing_inode_counts();
  }

  template <node_type NodeType>
  [[nodiscard]] auto get_shrinking_inode_count() const {
    const std::lock_guard guard{mutex};
    return db_.get_shrinking_inode_count<NodeType>();
  }

  [[nodiscard]] auto get_shrinking_inode_counts() const {
    const std::lock_guard guard{mutex};
    return db_.get_shrinking_inode_counts();
  }

  [[nodiscard]] auto get_key_prefix_splits() const {
    const std::lock_guard guard{mutex};
    return db_.get_key_prefix_splits();
  }

#endif  // UNODB_DETAIL_WITH_STATS

  // Public utils

  // Releases the mutex in the case key was not found, keeps it locked
  // otherwise.
  [[nodiscard]] static auto key_found(const get_result &result) noexcept {
#ifndef NDEBUG
    const auto &lock{result.second};
    // NOLINTNEXTLINE(readability-simplify-boolean-expr)
    assert(!result.first || lock.owns_lock());
#endif

    return static_cast<bool>(result.first);
  }

  // Debugging
  [[gnu::cold]] UNODB_DETAIL_NOINLINE void dump(std::ostream &os) const {
    const std::lock_guard guard{mutex};
    db_.dump(os);
  }

 private:
  db db_;
  mutable std::mutex mutex;
};

}  // namespace unodb

#endif  // UNODB_DETAIL_MUTEX_ART_HPP
