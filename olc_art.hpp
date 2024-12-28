// Copyright 2019-2024 Laurynas Biveinis
#ifndef UNODB_DETAIL_OLC_ART_HPP
#define UNODB_DETAIL_OLC_ART_HPP

#include "global.hpp"

// IWYU pragma: no_include <__fwd/ostream.h>

#include <array>
#include <atomic>
#include <cstddef>
#include <cstdint>
#include <iosfwd>  // IWYU pragma: keep
#include <optional>
#include <stack>
#include <tuple>

#include "art_common.hpp"
#include "art_internal.hpp"
#include "assert.hpp"
#include "node_type.hpp"
#include "optimistic_lock.hpp"
#include "portability_arch.hpp"
#include "qsbr_ptr.hpp"

namespace unodb {

class olc_db;

namespace detail {

template <class,  // Db
          template <class> class,  // CriticalSectionPolicy
          class,                   // optimistic_lock
          class,                   // read_critical_section
          class,                   // NodePtr
          class,                   // INodeDefs
          template <class> class,  // INodeReclamator
          template <class, class> class>  // LeadReclamator
struct basic_art_policy;  // IWYU pragma: keep

struct olc_node_header;

using olc_node_ptr = basic_node_ptr<olc_node_header>;

template <class>
class db_inode_qsbr_deleter;  // IWYU pragma: keep

template <class, class>
class db_leaf_qsbr_deleter;  // IWYU pragma: keep

template <class Header, class Db>
[[nodiscard]] auto make_db_leaf_ptr(art_key, value_view, Db &);

struct olc_impl_helpers;

template <class AtomicArray>
using non_atomic_array =
    std::array<typename AtomicArray::value_type::value_type,
               std::tuple_size<AtomicArray>::value>;

template <class T>
inline non_atomic_array<T> copy_atomic_to_nonatomic(T &atomic_array) noexcept {
  non_atomic_array<T> result;
  for (typename decltype(result)::size_type i = 0; i < result.size(); ++i) {
    result[i] = atomic_array[i].load(std::memory_order_relaxed);
  }
  return result;
}

using olc_leaf_unique_ptr =
    detail::basic_db_leaf_unique_ptr<detail::olc_node_header, olc_db>;

}  // namespace detail

using qsbr_value_view = qsbr_ptr_span<const std::byte>;

// A concurrent Adaptive Radix Tree that is synchronized using optimistic lock
// coupling. At any time, at most two directly-related tree nodes can be
// write-locked by the insert algorithm and three by the delete algorithm. The
// lock used is optimistic lock (see optimistic_lock.hpp), where only writers
// lock and readers access nodes optimistically with node version checks. For
// deleted node reclamation, Quiescent State-Based Reclamation is used.
class olc_db final {
 public:
  using get_result = std::optional<qsbr_value_view>;

  // Creation and destruction
  olc_db() noexcept = default;

  ~olc_db() noexcept;

  // Querying
  [[nodiscard]] get_result get(key search_key) const noexcept;

  [[nodiscard]] auto empty() const noexcept { return root == nullptr; }

  // Modifying
  // Cannot be called during stack unwinding with std::uncaught_exceptions() > 0
  [[nodiscard]] bool insert(key insert_key, value_view v);

  [[nodiscard]] bool remove(key remove_key);

  // Only legal in single-threaded context, as destructor
  void clear() noexcept;

  ///
  /// iterator (the iterator is an internal API, the public API is scan()).
  ///
  protected:
  class iterator {
    friend class olc_db;
   public:

    // Construct an empty iterator.
    inline iterator(olc_db& tree):db_(tree) {}

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

    // Makes this the "end()" iterator (by clearing the stack).
    inline iterator& end() noexcept {return invalidate();}
    
    // Position the iterator on, before, or after the caller's key.
    // If the iterator can not be positioned, it will be set to end().
    // For example, if [fwd:=true] and the [search_key] is GT any key
    // in the index then the iterator will be positioned to end()
    // since there is no index entry greater than the search key.
    // Likewise, if [fwd:=false] and the [search_key] is LT any key in
    // the index, then the iterator will be positioned to end() since
    // there is no index entry LT the search key.
    //
    // @param search_key The internal key used to position the iterator.
    //
    // @param match Will be set to true iff the search key is an exact
    // match in the index data.  Otherwise, the match is not exact and
    // the iterator is positioned either before or after the
    // search_key.
    //
    // @param fwd When true, the iterator will be positioned first
    // entry which orders GTE the search_key and end() if there is no
    // such entry.  Otherwise, the iterator will be positioned on the
    // last key which orders LTE the search_key and end() if there is
    // no such entry.
    iterator& seek(const detail::art_key& search_key, bool& match, bool fwd = true) noexcept;
    
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

    // Push the given node onto the stack and traverse from the
    // caller's node to the left-most leaf under that node, pushing
    // nodes onto the stack as they are visited.
    iterator& left_most_traversal(detail::olc_node_ptr node) noexcept;

    // Descend from the current state of the stack to the right most
    // child leaf, updating the state of the iterator during the
    // descent.
    iterator& right_most_traversal(detail::olc_node_ptr node) noexcept;

    // Return the node on the top of the stack, which will wrap
    // nullptr if the stack is empty.
    inline detail::olc_node_ptr current_node() noexcept {
      return stack_.empty()
          ? detail::olc_node_ptr(nullptr)
          : std::get<NP>( stack_.top() );
      ;
    }
    
   private:

    // invalidate the iterator (pops everything off of the stack).
    inline iterator& invalidate() noexcept {
      while ( ! stack_.empty() ) stack_.pop(); // clear the stack
      return *this;
    }     

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
    // Note: The read_critical_section contains the version information
    // that must be valid to use the KB and CI data read from the NP.
    // The CS information is cached when when those data are read from
    // the NP along with the KB and CI values that were read.
    //
    // FIXME variable length keys: we need to track the prefix length
    // that was consumed from the key during the descent so we know
    // how much to pop off of the internal key buffer when popping
    // something off of the stack.  For OLC, that information must be
    // read when using the CS but you DO NOT check the CS for validity
    // when popping something off of the key buffer since you need to
    // pop off just as many bytes as were pushed on.
    using stack_entry = std::tuple
      < detail::olc_node_ptr  // node pointer (NP) TODO -- make this [const node_ptr]?
      , std::byte             // key byte     (KB)
      , std::uint8_t          // child-index  (CI) (index into children[] except for N48, which is index into the child_indexes[], aka the same as the key byte)
      , optimistic_lock::read_critical_section // read-critical-section (CS) (version information NP lock used to populate [KB] and [CI] fields in this tuple).
      >;
  
    static constexpr int NP = 0; // node pointer (to an internal node or leaf, can also be the root node or root leaf)
    static constexpr int KB = 1; // key byte     (when stepping down from that node)
    static constexpr int CI = 2; // child_index  (along which the path steps down from that node)
    static constexpr int CS = 3; // read_critical_section (for that node when obtaining the child_index).
    
    // The outer db instance.
    olc_db& db_;

    // A stack reflecting the parent path from the root of the tree to
    // the current leaf.  An empty stack corresponds to the end()
    // iterator.  The iterator for an empty tree is an empty stack.
    //
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
  
  //
  // end of the iterator API, which is an internal API.
  //
  
 public:
  
  ///
  /// public scan API
  ///

  // Note: The scan() interface is public.  The iterator and the
  // methods to obtain an iterator are protected (except for tests).
  // This encapsulation makes it easier to define methods which
  // operate on external keys (scan()) and those which operate on
  // internal keys (seek() and the iterator). It also makes life
  // easier for mutex_db since scan() can take the lock.
  
  // Alias for an object visited by the scan_api.
  struct visitor {
    friend class olc_db;
   protected:
    iterator& it;
    inline visitor(iterator& it_):it(it_){}
   public:
    inline key get_key() noexcept;  // visit the key (may side-effect the iterator so not const).
    inline value_view get_value() const noexcept; // visit the value.
  };
  
  // Scan the tree, applying the caller's lambda to each visited leaf.
  //
  // @param fn A function f(visitor&) returning [bool::halt].  The
  // traversal will halt if the function returns [true].
  //
  // @param fwd When [true] perform a forward scan, otherwise perform
  // a reverse scan.
  template <typename FN>
  inline void scan(FN fn, bool fwd = true) noexcept {
    // FIXME db_.scan( fn, fwd );
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
    // FIXME db_.scan( fromKey, fn, fwd );
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
    // FIXME db_.scan( fromKey, toKey, fn );
  }
  
  // Stats

#ifdef UNODB_DETAIL_WITH_STATS

  // Return current memory use by tree nodes in bytes
  [[nodiscard]] auto get_current_memory_use() const noexcept {
    return current_memory_use.load(std::memory_order_relaxed);
  }

  template <node_type NodeType>
  [[nodiscard]] auto get_node_count() const noexcept {
    return node_counts[as_i<NodeType>].load(std::memory_order_relaxed);
  }

  [[nodiscard]] auto get_node_counts() const noexcept {
    return detail::copy_atomic_to_nonatomic(node_counts);
  }

  template <node_type NodeType>
  [[nodiscard]] auto get_growing_inode_count() const noexcept {
    return growing_inode_counts[internal_as_i<NodeType>].load(
        std::memory_order_relaxed);
  }

  [[nodiscard]] auto get_growing_inode_counts() const noexcept {
    return detail::copy_atomic_to_nonatomic(growing_inode_counts);
  }

  template <node_type NodeType>
  [[nodiscard]] auto get_shrinking_inode_count() const noexcept {
    return shrinking_inode_counts[internal_as_i<NodeType>].load(
        std::memory_order_relaxed);
  }

  [[nodiscard]] auto get_shrinking_inode_counts() const noexcept {
    return detail::copy_atomic_to_nonatomic(shrinking_inode_counts);
  }

  [[nodiscard]] auto get_key_prefix_splits() const noexcept {
    return key_prefix_splits.load(std::memory_order_relaxed);
  }

#endif  // UNODB_DETAIL_WITH_STATS

  // Public utils
  [[nodiscard]] static constexpr auto key_found(
      const get_result &result) noexcept {
    return static_cast<bool>(result);
  }

  // Debugging
  [[gnu::cold]] UNODB_DETAIL_NOINLINE void dump(std::ostream &os) const;

  olc_db(const olc_db &) noexcept = delete;
  olc_db(olc_db &&) noexcept = delete;
  olc_db &operator=(const olc_db &) noexcept = delete;
  olc_db &operator=(olc_db &&) noexcept = delete;

 private:
  // If get_result is not present, the search was interrupted. Yes, this
  // resolves to std::optional<std::optional<value_view>>, but IMHO both
  // levels of std::optional are clear here
  using try_get_result_type = std::optional<get_result>;

  using try_update_result_type = std::optional<bool>;

  [[nodiscard]] try_get_result_type try_get(detail::art_key k) const noexcept;

  [[nodiscard]] try_update_result_type try_insert(
      detail::art_key k, value_view v,
      detail::olc_leaf_unique_ptr &cached_leaf);

  [[nodiscard]] try_update_result_type try_remove(detail::art_key k);

  void delete_root_subtree() noexcept;

#ifdef UNODB_DETAIL_WITH_STATS
  void increase_memory_use(std::size_t delta) noexcept;
  void decrease_memory_use(std::size_t delta) noexcept;

  void increment_leaf_count(std::size_t leaf_size) noexcept {
    increase_memory_use(leaf_size);
    node_counts[as_i<node_type::LEAF>].fetch_add(1, std::memory_order_relaxed);
  }

  UNODB_DETAIL_DISABLE_MSVC_WARNING(4189)
  void decrement_leaf_count(std::size_t leaf_size) noexcept {
    decrease_memory_use(leaf_size);

    const auto old_leaf_count UNODB_DETAIL_USED_IN_DEBUG =
        node_counts[as_i<node_type::LEAF>].fetch_sub(1,
                                                     std::memory_order_relaxed);
    UNODB_DETAIL_ASSERT(old_leaf_count > 0);
  }
  UNODB_DETAIL_RESTORE_MSVC_WARNINGS()

  template <class INode>
  constexpr void increment_inode_count() noexcept;

  template <class INode>
  constexpr void decrement_inode_count() noexcept;

  template <node_type NodeType>
  constexpr void account_growing_inode() noexcept;

  template <node_type NodeType>
  constexpr void account_shrinking_inode() noexcept;

#endif  // UNODB_DETAIL_WITH_STATS

  // optimistic lock guarding the [root].
  alignas(
      detail::hardware_destructive_interference_size) mutable optimistic_lock
      root_pointer_lock;

  // The root of the tree, guarded by the [root_pointer_lock].
  in_critical_section<detail::olc_node_ptr> root{detail::olc_node_ptr{nullptr}};

  static_assert(sizeof(root_pointer_lock) + sizeof(root) <=
                detail::hardware_constructive_interference_size);

#ifdef UNODB_DETAIL_WITH_STATS

  // Current logically allocated memory that is not scheduled to be reclaimed.
  // The total memory currently allocated is this plus the QSBR deallocation
  // backlog (qsbr::previous_interval_total_dealloc_size +
  // qsbr::current_interval_total_dealloc_size).
  alignas(detail::hardware_destructive_interference_size)
      std::atomic<std::size_t> current_memory_use{0};

  alignas(detail::hardware_destructive_interference_size)
      std::atomic<std::uint64_t> key_prefix_splits{0};

  template <class T>
  using atomic_array = std::array<std::atomic<typename T::value_type>,
                                  std::tuple_size<T>::value>;

  alignas(detail::hardware_destructive_interference_size)
      atomic_array<node_type_counter_array> node_counts{};
  alignas(detail::hardware_destructive_interference_size)
      atomic_array<inode_type_counter_array> growing_inode_counts{};
  alignas(detail::hardware_destructive_interference_size)
      atomic_array<inode_type_counter_array> shrinking_inode_counts{};

#endif  // UNODB_DETAIL_WITH_STATS

  friend auto detail::make_db_leaf_ptr<detail::olc_node_header, olc_db>(
      detail::art_key, value_view, olc_db &);

  template <class, class>
  friend class detail::basic_db_leaf_deleter;

  template <class, class>
  friend class detail::db_leaf_qsbr_deleter;

  template <class>
  friend class detail::db_inode_qsbr_deleter;

  template <class, template <class> class, class, class, class, class, template <class> class,
            template <class, class> class>
  friend struct detail::basic_art_policy;

  template <class, class>
  friend class detail::basic_db_inode_deleter;

  friend struct detail::olc_impl_helpers;
};

}  // namespace unodb

#endif  // UNODB_DETAIL_OLC_ART_HPP
