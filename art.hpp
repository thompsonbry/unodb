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

// A typesafe enumeration for how the iterator will match keys during
// search. You can use these enumerations to setup for a forward or
// reverse scan.
enum find_enum {
  EQ,  // the search must position the iterator on an exact match for the search key in the tree.
  GTE, // the search must position the iterator on the first key GTE to the search key in the tree.
  LTE  // the search must position the iterator on the first key LTE to the search key in the tree.
};

//#define RECURSIVE_SCAN
#ifdef RECURSIVE_SCAN
// iterator callback function typedef.
//
// @param The current key.
//
// @param The current value.
//
// @return true to halt or false to continue
typedef bool (*it_functor)(const key, const value_view);
#endif

// Basic iterator for the non-thread-safe ART implementation.
class db; // forward declaration
template <typename Db>
class it_t {   
 public:

  // Construct an iterator which is not positioned on any leaf in the index.
  it_t(const Db& db):db_(db) {}

#ifdef RECURSIVE_SCAN
  // FIXME Write a recursive scan function to scan the entire tree and
  // this would doubtless be quite fast and could invoke a lambda for
  // each visited key.  It can likely be done for reverse scan just as
  // easily.  The iterator could be positioned with using find()
  // semantics to return a find_result.  For OLC, we can restart the
  // iterator from the current key by performing a find(GT).  The main
  // question is how we do detect a version tag modification.
  //
  // @param The search key. The scan will begin at the first key GTE
  // to the search key in the index.
  //
  // @param fn A functor to invoke for each visited entry.
  void scan(key search_key/*, it_functor fn*/) const noexcept;
#endif
  
  // Return true iff the iterator is positioned on some leaf and false otherwise.
  bool valid() const noexcept;
    
  // Advance the iterator to next entry in the index and return
  // true.
  //
  // @return false if the iterator is not positioned on a leaf or if
  // there is no next entry.  An attempt to position the iterator
  // after the last leaf does not change the state of the iterator.
  bool next() noexcept;
    
  // Position the iterator on the first entry in the index.
  //
  // @return false if the index is empty.
  bool begin() noexcept;

  // Position the iterator on after the last leaf in the index.
  //
  // @return false if the index is empty.
  bool end() noexcept;

  // Position the iterator on the previous leaf in the index.  If the
  // iterator is positioned after the last leaf, then this will
  // position the iterator on the last leaf.
  //
  // @return false if the iterator is not positioned on a leaf or if
  // there is no previous leaf.  An attempt to position the iterator
  // before the first leaf does not change the state of the iterator.
  bool prior() noexcept;
    
  // Position the iterator on the first entry which orders GTE the
  // search_key. Returns true iff the search_key exists (exact
  // match) or if the iterator was positioned to an entry in the
  // index (!exact) and returns false otherwise.  If the iterator is
  // not positioned by this method, then the iterator is invalidated
  // (as if it were newly constructed).
  bool find(key search_key, find_enum dir) noexcept;
    
  // Iff the iterator is positioned on an index entry, then returns
  // a const pointer to a decoded copy of the key associated with
  // that index entry.  Otherwise returns nullptr.
  //
  // Note: std::optional does not allow reference types, hence going
  // with pointer to buffer return semantics.
  std::optional<const key> get_key() noexcept;

  // Iff the iterator is positioned on an index entry, then returns
  // the value associated with that index entry.
  std::optional<const value_view> get_val() const noexcept;
    
 private:

  // invalidate the iterator.
  void invalidate() noexcept {
    while(!stack_.empty()) stack_.pop(); // clear the stack
  }

#ifdef RECURSIVE_SCAN
  static constexpr int CONTINUE = 0;  // iterator will continue.
  static constexpr int RESTART = -1;  // iterator will restart from the current key.
  static constexpr int HALT = -2;     // iterator will halt.
  
  // Recursive inner implementation for the forward iterator. When
  // invoked, the iterator seek to the current key and then performs a
  // forward scan invoking the lambda for each visited leaf.  The scan
  // invokes itself recursively.  If the scan() returns false, the
  // scan is restarted for the current key.
  //
  // @param node The current node.
  //
  // @param level The depth in the tree. This is ZERO (0) when
  // initially called.  The depth is used when restarting the iterator
  // on a key since we need to pop up until we are back at level 0.
  //
  // @param bkey A buffer containing a materialized copy of the
  // external key, modified by side-effect.
  //
  // @param ckey The current key, modified by side-effect.
  //
  // @param rkey The remaining key, which is shortened during
  // recursive descent based on match bytes.
  //
  // @param fn The functor to invoke for each visited leaf.
  //
  // @return RESTART iff the iterator should restart from the root of
  // the tree on the current key; CONTINUE if the iterator should
  // continue; and HALT if the iterator should halt.
  int scan(detail::node_ptr node, uint32_t level, unodb::key& bkey, detail::art_key& ckey, detail::art_key rkey/*, it_functor fn*/) const noexcept;
#endif
  
  const Db& db_;                    // tree to be visited : TODO Assumes iterator can not modify the tree (simplying assumption).

  // The first element is the child index in the node, the 2nd is
  // pointer to the child. If not present, the pointer is nullptr, and
  // the index is undefined.
  //
  // FIXME This is the close to the definition that appears in
  // art_internal_impl.hpp.  However, there are two gaps for OLC.
  // First, the critical_section_policy needs to be carried through
  // into the stack_entry. That type information is not super
  // accessible so I am leaving it out in the first version of the
  // iterator (since it also amounts to a NOP except for OLC).
  // Second, the stack_entry needs to also carry the version tag from
  // the try_read_lock, which is of type art_policy::read_version.
  // That version tag is required to validate that a structural
  // mutation has not invalidated the path from the root, thus
  // requiring a restart (seaching for the current key from the root
  // to obtain a valid path).
  //
  // std::pair<std::uint8_t, critical_section_policy<node_ptr> *>
  using stack_entry = std::pair<std::uint8_t, unodb::detail::node_ptr>;

  // A stack reflecting the parent path from the root of the tree to
  // the current leaf.  A valid iterator is always positioned on a
  // leaf and always has a leaf on the top of the stack.  If the stack
  // is empty, the iterator is invalid.  The bottom of the stack is
  // always the root of the tree.
  //
  // The stack is a (child_index, child_ptr) pair.  The child_index is
  // the index position in the parent at which the child_ptr was
  // found.  The child_index has no meaning for the root of the tree.
  // The child_index is used to avoid searching the parent for the
  // child_ptr when advancing the iterator to the next() or the
  // prior() leaf in the index.
  //
  // Note: When finding the successor (or predecessor) the child_index
  // needs to be interpreted according to the node type.  For N4 and
  // N16, you just look at the next slot in the children[] to find the
  // successor.  For N256, you look at the next non-null slot in the
  // children[].  N48 is the oddest of the node types.  For N48, you
  // have to look at the key[], find the next mapped key value greater
  // than the current one and then look at its entry in the
  // children[].
  //
  // Note: For OLC, the child_index is only valid if the parent
  // version tag remains valid.
  std::stack<stack_entry> stack_ {};

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

#include "art_iter.hpp" // header only iterator methods

#endif  // UNODB_DETAIL_ART_HPP
