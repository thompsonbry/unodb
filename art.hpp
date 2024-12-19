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

  // Basic iterator for the non-thread-safe ART implementation.
  class iterator {   
   public:

    // Construct an empty iterator.
    iterator(db& tree):db_(tree) {}

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
  
    // Position the iterator on the first entry in the stack.
    iterator& first() noexcept;
    
    // Advance the iterator to next entry in the index and return
    // true.
    //
    // @return false if the iterator is not positioned on a leaf or if
    // there is no next entry.  An attempt to position the iterator
    // after the last leaf does not change the state of the iterator.
    iterator& next() noexcept;
    
    // Position the iterator on the previous leaf in the index.  If the
    // iterator is positioned after the last leaf, then this will
    // position the iterator on the last leaf.
    //
    // @return false if the iterator is not positioned on a leaf or if
    // there is no previous leaf.  An attempt to position the iterator
    // before the first leaf does not change the state of the iterator.
    iterator& prior() noexcept;
    
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
    std::optional<const key> get_key() noexcept {
      // FIXME Eventually this will need to use the stack to reconstruct
      // the key from the path from the root to this leaf.  Right now it
      // is relying on the fact that simple fixed width keys are stored
      // directly in the leaves.
      if ( ! valid() ) return {}; // not positioned on anything.
      const auto *const leaf{std::get<CP>( stack_.top() )->load().ptr<detail::leaf *>()}; // current leaf.
      key_ = leaf->get_key().decode(); // decode the key into the iterator's buffer.
      return key_; // return pointer to the internal key buffer.
    }

    // Iff the iterator is positioned on an index entry, then returns
    // the value associated with that index entry.
    std::optional<const value_view> get_val() const noexcept {
      if ( ! valid() ) return {}; // not positioned on anything.
      const auto *const leaf{std::get<CP>( stack_.top() )->load().ptr<detail::leaf *>()}; // current leaf.
      return leaf->get_value_view();
    }

    bool operator==(const iterator& other) const noexcept {
      if ( &db_ != &other.db_ ) return false;                          // different tree?
      if (   stack_.empty() && ! other.stack_.empty() ) return false;  // one stack is empty and the other is not?
      if ( ! stack_.empty() &&   other.stack_.empty() ) return false;  // ditto
      if ( stack_.empty() ) return true;                               // both empty.
      return std::get<CP>(       stack_.top() )->load().ptr<detail::leaf*>() // pointing at the same leaf?
          == std::get<CP>( other.stack_.top() )->load().ptr<detail::leaf*>()
          ;
    }
    
    bool operator!=(const iterator& other) const noexcept { return !(*this == other); }
    
   protected:

    // Return true iff the iterator is positioned on some leaf and
    // false otherwise.
    //
    // Note: An empty tree and the end() iterator are both modeled by
    // an empty stack.  So this is a shortcut for [*this==end].
    //
    // Note: DO NOT push anything with a nullptr child reference onto
    // the stack!
    bool valid() const noexcept {
      // Note: A valid iterator must have a path to a leaf.
      return ( ! stack_.empty() && std::get<CP>( stack_.top() )->load().type() == node_type::LEAF );
    }

   private:

    static constexpr int KB = 0; // key byte
    static constexpr int CI = 1; // child_index
    static constexpr int CP = 2; // child_pointer
    
    // invalidate the iterator.
    iterator& invalidate() noexcept {
      while ( ! stack_.empty() ) stack_.pop(); // clear the stack
      return *this;
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

    // The element (0) is the key byte, element (1) is child index in
    // the node, element (2) is the pointer to the child or nullptr if
    // the iter_result is invalid (e.g., end()).
    using stack_entry = detail::inode_base::iter_result;
    
    // The outer db instance.
    db& db_;

    // A stack reflecting the parent path from the root of the tree to
    // the current leaf.
    //
    // The stack is a (key, child_index, child_ptr) tuple.
    //
    // Each entry corresponds to the path for a given internal node.
    // An empty stack corresponds to the end() iterator.  The iterator
    // for an empty tree is always an empty stack.  For a valid
    // iterator, the bottom of the stack is an entry pointing to the
    // root of the tree (child_ptr is the tree root) and the top of
    // the stack is a pointer to the leaf (child_ptr is a leaf).
    //
    // The [key] is the [std::byte] along which the path descends to
    // the child.  The [key] has no meaning for the root of the tree
    // (aka the bottom of the stack).  The key byte may be used to
    // reconstruct the full key (along with any prefix bytes in the
    // nodes along the path).  The key byte is part of the stack entry
    // to avoid having to search the keys of some node types when the
    // child_index does not directly imply the key byte.
    //
    // The [child_index] is the [std::uint16_t] index position in the
    // parent at which the [child_ptr] was found.  The [child_index]
    // has no meaning for the root of the tree (aka the bottom of the
    // stack).  The [child_index] is used to avoid searching the
    // parent for the [child_ptr] when advancing the iterator to the
    // next() or the prior() leaf in the index.
    //
    // Note: When finding the successor (or predecessor) the
    // [child_index] needs to be interpreted according to the node
    // type.  For N4 and N16, you just look at the next slot in the
    // children[] to find the successor.  For N256, you look at the
    // next non-null slot in the children[].  N48 is the oddest of the
    // node types.  For N48, you have to look at the key[], find the
    // next mapped key value greater than the current one and then
    // look at its entry in the children[].
    //
    // The [child_ptr] is a critical section policy wrapping a
    // node_ptr and is never [nullptr].  The current leaf is found
    // from the [child_ptr] for the entry on the top of the stack.
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

  // Return an iterator that is positioned after any possible entry in
  // the index.
  [[nodiscard]] iterator end() noexcept { return iterator(*this); }
  
#if 0
  // member typedefs provided through inheriting from std::iterator
  class iterator {
    // iterator traits
    using iterator_category = std::forward_iterator_tag;      
    using value_type = std::pair<key,value_view>;
    using difference_type = long;
    using pointer = const long*;
    using reference = const long&;
    // A stack of node positions from the root to the current leaf.
    // An empty stack is used iff there is no data in the tree. If
    // the tree has any data, then the stack is a path to either a
    // leaf a single entry corresponding to end() [positioned beyond
    // the end of the tree].
    std::stack<basic_inode_impl::iter_result> stack_ {};
    // position the iterator on the first leaf (if any)
    explicit iterator() {
    }
    // position the iterator on the search key (iff found).
    explicit iterator(key search_key) {
    }
    // create an "end()" iterator.
    explicit iterator(const basic_inode_impl::iter_result& end_result) {
      stack_.push( end_result );
    }
   public:
    iterator& operator++() { num = TO >= FROM ? num + 1: num - 1; return *this; }
    iterator operator++(int) { iterator retval = *this; ++(*this); return retval; }
    bool operator==(iterator other) const { return num == other.num; }
    bool operator!=(iterator other) const { return !(*this == other); }
    reference operator*() const { return num; } // TODO Create get_key() and get_val() methods in case people want less data.
  };
  iterator begin() { return iterator(FROM); } // return an iterator positioned on the first leaf in the index.
  iterator end() { return iterator(basic_node_impl::end_result); }  // return an iterator positioned beyond the last leaf in the index.
}; // class iterator

iterator begin() { return &store[0]; }
const_iterator begin() const { return &store[0]; }
iterator end() { return &store[size]; }
const_iterator end() const { return &store[size]; }
#endif
  
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

  detail::node_ptr root{nullptr};  // FIXME This should be wrapped with the fake critical section.

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

#include "art_iter.hpp" // header only iterator methods FIXME Remove or keep?

#endif  // UNODB_DETAIL_ART_HPP
