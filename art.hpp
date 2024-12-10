// Copyright 2019-2024 Laurynas Biveinis
#ifndef UNODB_DETAIL_ART_HPP
#define UNODB_DETAIL_ART_HPP

#include "global.hpp"

// IWYU pragma: no_include <__fwd/ostream.h>

#include <cstddef>
#include <cstdint>
#include <iosfwd>  // IWYU pragma: keep
#include <optional>
#include <stack>

#include "art_common.hpp"
#include "art_internal.hpp"
#include "assert.hpp"
#include "node_type.hpp"

namespace unodb {

namespace detail {

struct node_header;

template <class, template <class> class, class, class, template <class> class,
          template <class, class> class>
struct basic_art_policy;  // IWYU pragma: keep

using node_ptr = basic_node_ptr<node_header>;

template <class Header, class Db>
[[nodiscard]] auto make_db_leaf_ptr(art_key, value_view, Db &);

struct impl_helpers;

}  // namespace detail

// Basic iterator for the non-thread-safe ART implementation.
class db; // forward declaration
template <typename Db>
class it_t {   
public:

    // Construct an iterator which is not positioned on any leaf in the index.
    it_t(const Db& db):db_(db) {}
    
    // Return true iff the iterator is positioned on some entry and false otherwise.
    bool valid() const noexcept {
        // Note: The assumption here is that the stack is either empty
        // or is a valid path to a leaf.  Intermediate states exist
        // when traversing the tree to a leaf, but should not be
        // exposed to the caller.  (That is, the iterator should never
        // have a partial path on the stack when control is returned
        // to the caller.)
        return ! stack_.empty();
    }
    
    // Advance the iterator to next entry in the index and return
    // true.  Return false if the iterator is not positioned on a leaf
    // or if there is no next entry.  An attempt to position the
    // iterator after the last leaf does not change the state of the
    // iterator.
    bool next() noexcept;
    
    // Advance the iterator to next entry in the index and returns
    // true.  Returns false if the iterator is not positioned on a
    // leaf or if there is no next entry.  
    bool first() noexcept;

    // Position the iterator on the least leaf in the index.
    bool last() noexcept;

    // Position the iterator on the previous leaf in the index and return
    // false if the iterator is not positioned on a leaf or if there is no
    // previous leaf.  An attempt to position the iterator before the first
    // leaf does not change the state of the iterator.
    //
    bool prior() noexcept;
    
    // Position the iterator on the first entry which orders GTE the
    // search_key. Returns true iff the search_key exists (exact
    // match) or if the iterator was positioned to an entry in the
    // index (!exact) and returns false otherwise.  If the iterator is
    // not positioned by this method, then the iterator is invalidated
    // (as if it were newly constructed).
    bool find(key search_key, bool exact = false) noexcept;
    
    // Iff the iterator is positioned on an index entry, then returns
    // a const pointer to a decoded copy of the key associated with
    // that index entry.  Otherwise returns nullptr.
    //
    // Note: std::optional does not allow reference types, hence going
    // with pointer to buffer return semantics.
    const key* get_key() noexcept;

    // Iff the iterator is positioned on an index entry, then returns
    // the value associated with that index entry.
    std::optional<const value_view> get_val() const noexcept;
    
private:

    // invalidate the iterator.
    void invalidate() noexcept {
        while(!stack_.empty()) stack_.pop(); // clear the stack
    }
    
    const Db& db_;                    // tree to be visited : TODO Assumes iterator can not modify the tree (simplying assumption).
    std::stack<detail::node_ptr> stack_ {}; // a stack reflecting the parent path from the root of the tree to the current leaf.
    key key_ {};                      // a buffer into which visited keys are materialized by get_key()
    
}; // class it_t<>
    
class db final {
 friend class it_t<db>; // iterator is a friend.
 public:
  using get_result = std::optional<value_view>;

  // Creation and destruction
  db() noexcept = default;

  ~db() noexcept;

  // TODO(laurynas): implement copy and move operations
  db(const db &) = delete;
  db(db &&) = delete;
  db &operator=(const db &) = delete;
  db &operator=(db &&) = delete;

  // Querying
  [[nodiscard, gnu::pure]] get_result get(key search_key) const noexcept;

  [[nodiscard, gnu::pure]] auto empty() const noexcept {
    return root == nullptr;
  }

  // Modifying
  // Cannot be called during stack unwinding with std::uncaught_exceptions() > 0
  [[nodiscard]] bool insert(key insert_key, value_view v);

  [[nodiscard]] bool remove(key remove_key);

  // return an iterator for the tree.
  [[nodiscard]] it_t<db> iterator() const {return it_t(*this);}

  void clear() noexcept;

  // Stats

#ifdef UNODB_DETAIL_WITH_STATS

  // Return current memory use by tree nodes in bytes.
  [[nodiscard, gnu::pure]] constexpr auto get_current_memory_use()
      const noexcept {
    return current_memory_use;
  }

  template <node_type NodeType>
  [[nodiscard, gnu::pure]] constexpr auto get_node_count() const noexcept {
    return node_counts[as_i<NodeType>];
  }

  // cppcheck-suppress returnByReference
  [[nodiscard, gnu::pure]] constexpr auto get_node_counts() const noexcept {
    return node_counts;
  }

  template <node_type NodeType>
  [[nodiscard, gnu::pure]] constexpr auto get_growing_inode_count()
      const noexcept {
    return growing_inode_counts[internal_as_i<NodeType>];
  }

  // cppcheck-suppress returnByReference
  [[nodiscard, gnu::pure]] constexpr auto get_growing_inode_counts()
      const noexcept {
    return growing_inode_counts;
  }

  template <node_type NodeType>
  [[nodiscard, gnu::pure]] constexpr auto get_shrinking_inode_count()
      const noexcept {
    return shrinking_inode_counts[internal_as_i<NodeType>];
  }

  // cppcheck-suppress returnByReference
  [[nodiscard, gnu::pure]] constexpr auto get_shrinking_inode_counts()
      const noexcept {
    return shrinking_inode_counts;
  }

  [[nodiscard, gnu::pure]] constexpr auto get_key_prefix_splits()
      const noexcept {
    return key_prefix_splits;
  }

#endif  // UNODB_DETAIL_WITH_STATS

  // Public utils
  [[nodiscard, gnu::const]] static constexpr auto key_found(
      const get_result &result) noexcept {
    return static_cast<bool>(result);
  }

  // Debugging
  [[gnu::cold]] UNODB_DETAIL_NOINLINE void dump(std::ostream &os) const;

 private:
  void delete_root_subtree() noexcept;

#ifdef UNODB_DETAIL_WITH_STATS

  constexpr void increase_memory_use(std::size_t delta) noexcept {
    UNODB_DETAIL_ASSERT(delta > 0);
    UNODB_DETAIL_ASSERT(
        std::numeric_limits<decltype(current_memory_use)>::max() - delta >=
        current_memory_use);

    current_memory_use += delta;
  }

  constexpr void decrease_memory_use(std::size_t delta) noexcept {
    UNODB_DETAIL_ASSERT(delta > 0);
    UNODB_DETAIL_ASSERT(delta <= current_memory_use);

    current_memory_use -= delta;
  }

  constexpr void increment_leaf_count(std::size_t leaf_size) noexcept {
    increase_memory_use(leaf_size);
    ++node_counts[as_i<node_type::LEAF>];
  }

  constexpr void decrement_leaf_count(std::size_t leaf_size) noexcept {
    decrease_memory_use(leaf_size);

    UNODB_DETAIL_ASSERT(node_counts[as_i<node_type::LEAF>] > 0);
    --node_counts[as_i<node_type::LEAF>];
  }

  template <class INode>
  constexpr void increment_inode_count() noexcept;

  template <class INode>
  constexpr void decrement_inode_count() noexcept;

  template <node_type NodeType>
  constexpr void account_growing_inode() noexcept;

  template <node_type NodeType>
  constexpr void account_shrinking_inode() noexcept;

#endif  // UNODB_DETAIL_WITH_STATS

  detail::node_ptr root{nullptr};

#ifdef UNODB_DETAIL_WITH_STATS

  std::size_t current_memory_use{0};

  node_type_counter_array node_counts{};
  inode_type_counter_array growing_inode_counts{};
  inode_type_counter_array shrinking_inode_counts{};

  std::uint64_t key_prefix_splits{0};

#endif  // UNODB_DETAIL_WITH_STATS

  friend auto detail::make_db_leaf_ptr<detail::node_header, db>(detail::art_key,
                                                                value_view,
                                                                db &);

  template <class, class>
  friend class detail::basic_db_leaf_deleter;

  template <class, template <class> class, class, class, template <class> class,
            template <class, class> class>
  friend struct detail::basic_art_policy;

  template <class, class>
  friend class detail::basic_db_inode_deleter;

  friend struct detail::impl_helpers;
};

}  // namespace unodb

#endif  // UNODB_DETAIL_ART_HPP
