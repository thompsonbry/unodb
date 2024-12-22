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
#include "art_internal_impl.hpp"
#include "assert.hpp"
#include "in_fake_critical_section.hpp"
#include "node_type.hpp"

namespace unodb {

namespace detail {

class inode;

class inode_4;
class inode_16;
class inode_48;
class inode_256;

struct [[nodiscard]] node_header {};

static_assert(std::is_empty_v<node_header>);

template <class, template <class> class, class, class, template <class> class,
          template <class, class> class>
struct basic_art_policy;  // IWYU pragma: keep

using node_ptr = basic_node_ptr<node_header>;

struct impl_helpers;

using inode_defs = unodb::detail::basic_inode_def<inode, inode_4, inode_16,
                                                  inode_48, inode_256>;

template <class INode>
using db_inode_deleter =
    unodb::detail::basic_db_inode_deleter<INode, unodb::db>;

using art_policy = unodb::detail::basic_art_policy<
    unodb::db, unodb::in_fake_critical_section, unodb::detail::node_ptr,
    inode_defs, db_inode_deleter, unodb::detail::basic_db_leaf_deleter>;

using inode_base = unodb::detail::basic_inode_impl<art_policy>;

using leaf = unodb::detail::basic_leaf<unodb::detail::node_header>;

class inode : public inode_base {};

}  // namespace detail

class db final {
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
  
  void clear() noexcept;

  ///
  /// iterator
  ///

  // A typesafe enumeration for how the iterator will match keys during
  // search. You can use these enumerations to setup for a forward or
  // reverse scan.
  enum seek_enum {
    EQ,  // the search must position the iterator on an exact match for the search key in the tree.
    GTE, // the search must position the iterator on the first key GTE to the search key in the tree.
    LTE  // the search must position the iterator on the first key LTE to the search key in the tree.
  };

  // Basic iterator for the non-thread-safe ART implementation.
  class iterator {
    friend class db;
   public:

    // Construct an empty iterator.
    inline iterator(db& tree):db_(tree) {}

    // Position the iterator on the first entry in the index.
    iterator& first() noexcept;
    
    // Advance the iterator to next entry in the index.
    iterator& next() noexcept;
    
    // Position the iterator on the last entry in the index, which can
    // be used to initiate a reverse traversal.
    //
    // Note: This is NOT the same as end(), which does not position
    // the iterator on anything.
    iterator& last() noexcept;
    
    // Position the iterator on the previous entry in the index.
    iterator& prior() noexcept;
    
    // Position the iterator on the first entry which orders GTE the
    // search_key. Returns true iff the search_key exists (exact
    // match) or if the iterator was positioned to an entry in the
    // index (!exact) and returns false otherwise.  If the iterator is
    // not positioned by this method, then the iterator is invalidated
    // (as if it were newly constructed).
    bool seek(key search_key, seek_enum dir) noexcept;
    
    // Iff the iterator is positioned on an index entry, then returns
    // the key associated with that index entry.
    //
    // Note: std::optional does not allow reference types, hence going
    // with pointer to buffer return semantics.
    inline std::optional<const key> get_key() noexcept;
    
    // Iff the iterator is positioned on an index entry, then returns
    // the value associated with that index entry.
    inline std::optional<const value_view> get_val() const noexcept;
    
    inline bool operator==(const iterator& other) const noexcept;    
    inline bool operator!=(const iterator& other) const noexcept;

    // Debugging
    [[gnu::cold]] UNODB_DETAIL_NOINLINE void dump(std::ostream &os) const;

   protected:
    
    // Return true unless the stack is empty.
    inline bool valid() const noexcept { return ! stack_.empty(); }
    
   private:

    static constexpr int NP = detail::inode_base::NP; // node pointer
    static constexpr int KB = detail::inode_base::KB; // key byte
    static constexpr int CI = detail::inode_base::CI; // child_index
    
    // invalidate the iterator (pops everything off of the stack).
    inline iterator& invalidate() noexcept;

    // The element (0) is the key byte, element (1) is child index in
    // the node, element (2) is the pointer to the child or nullptr if
    // the iter_result is invalid (e.g., end()).
    using stack_entry = detail::inode_base::iter_result;
    
    // The outer db instance.
    db& db_;

    // A stack reflecting the parent path from the root of the tree to
    // the current leaf.  An empty stack corresponds to the end()
    // iterator.  The iterator for an empty tree is an empty stack.
    //
    // The stack is made up of (node_ptr, key, child_index) entries
    // defined by [iter_result].
    //
    // The [node_ptr] is never [nullptr] and points to the internal
    // node or leaf for that step in the path from the root to some
    // leaf.  For the bottom of the stack, [node_ptr] is the root.
    // For the top of the stack, [node_ptr] is the current leaf. In
    // the degenerate case where the tree is a single root leaf, then
    // the stack contains just that leaf.
    //
    // The [key] is the [std::byte] along which the path descends from
    // that [node_ptr].  The [key] has no meaning for a leaf.  The key
    // byte may be used to reconstruct the full key (along with any
    // prefix bytes in the nodes along the path).  The key byte is
    // tracked to avoid having to search the keys of some node types
    // (N48) when the [child_index] does not directly imply the key
    // byte.
    //
    // The [child_index] is the [std::uint8_t] index position in the
    // parent at which the [child_ptr] was found.  The [child_index]
    // has no meaning for a leaf.  In the special case of N48, the
    // [child_index] is the index into the [child_indexes[]].  For all
    // other internal node types, the [child_index] is a direct index
    // into the [children[]].  When finding the successor (or
    // predecessor) the [child_index] needs to be interpreted
    // according to the node type.  For N4 and N16, you just look at
    // the next slot in the children[] to find the successor.  For
    // N256, you look at the next non-null slot in the children[].
    // N48 is the oddest of the node types.  For N48, you have to look
    // at the child_indexes[], find the next mapped key value greater
    // than the current one, and then look at its entry in the
    // children[].
    //
    // FIXME For OLC, the child_index is only valid if the parent
    // version tag remains valid.  For that purpose, this tuple needs
    // to be expanded to also include the version tag of the parent.
    std::stack<stack_entry> stack_ {};

    // A buffer into which visited keys are decoded and materialized
    // by get_key().
    //
    // Note: The internal key is a sequence of unsigned bytes having
    // the appropriate lexicographic ordering.  The internal key needs
    // to be decoded to the external key.
    //
    // FIXME The current implementation stores the entire key in the
    // leaf. This works fine for simple primitive keys.  However, it
    // needs to be modified when the implementation is modified to
    // support variable length keys. In that situation, the full
    // internal key needs to be constructed using the [key] byte from
    // the path stack plus the prefix bytes from the internal nodes
    // along that path.
    key key_ {};
    
  }; // class iterator

  // Return an iterator that is positioned on the first entry in the
  // index (if any).  If the index is empty, the returned iterator
  // will be "end()".
  [[nodiscard]] iterator begin() noexcept { return iterator{*this}.first(); }

  // Return an iterator that is positioned on the last entry in the
  // index (if any).  If the index is empty, the returned iterator
  // will be "end()".
  [[nodiscard]] iterator last() noexcept { return iterator{*this}.last(); }

  // Return an iterator that is positioned after any possible entry in
  // the index.
  //
  // Note: end() is specific to a given db instance and not flyweight
  // (there is an internal stack object) so it is a good idea to lift
  // it out as a constant when writing loops which check against
  // end().
  //
  // FIXME Should calling end().prior() bring us to last()?  If it
  // does, how do we handle last().prior().prior()... when we reach
  // the first entry in the index?  At that point, we need to return
  // end() to indicate that the iterator is invalid().  If calling
  // end().prior() initiates reverse traversal from the last index
  // entry, then this could silently restart the reverse scan from
  // last().
  [[nodiscard]] iterator end() noexcept { return iterator(*this); }

  // Scan the tree, applying the caller's lambda to each visited leaf.
  //
  // @param fn A function f(iterator&) returning [bool::halt].  The
  // traversal will halt if the function returns [true].
  // 
  // FIXME Add ability to seek to some point to the iterator and make
  // this an apply() on the iterator accepting a fromKey and toKey.
  //
  // FIXME Support forward and reverse scans.  Perhaps just pass in
  // [scan_dir] as a two value enum and use that to position the
  // iterator via seek() and then drive it in the correct direction.
  template <typename FN>
  inline void scan(FN fn) noexcept {
    auto it { begin() };
    while ( it.valid() && ! fn( it ) ) {
      it.next();
    }
  }
  
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
