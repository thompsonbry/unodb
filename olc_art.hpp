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
#include "art_internal_impl.hpp"
#include "assert.hpp"
#include "node_type.hpp"
#include "optimistic_lock.hpp"
#include "portability_arch.hpp"
#include "qsbr_ptr.hpp"

namespace unodb {

class olc_db;

namespace detail {

// The OLC header contains an [optimistic_lock].
struct [[nodiscard]] olc_node_header {

  // Return a reference to the [optimistic_lock].
  [[nodiscard]] constexpr optimistic_lock &lock() const noexcept {
    return m_lock;
  }

#ifndef NDEBUG
  static void check_on_dealloc(const void *ptr) noexcept {
    static_cast<const olc_node_header *>(ptr)->m_lock.check_on_dealloc();
  }
#endif

 private:
  mutable optimistic_lock m_lock;  // The lock.
};
static_assert(std::is_standard_layout_v<olc_node_header>);

class olc_inode;
class olc_inode_4;
class olc_inode_16;
class olc_inode_48;
class olc_inode_256;

using olc_inode_defs =
    unodb::detail::basic_inode_def<olc_inode, olc_inode_4, olc_inode_16,
                                   olc_inode_48, olc_inode_256>;

using olc_node_ptr = basic_node_ptr<olc_node_header>;

template <class>
class db_inode_qsbr_deleter;  // IWYU pragma: keep

template <class, class>
class db_leaf_qsbr_deleter;  // IWYU pragma: keep

template <class Header, class Db>
[[nodiscard]] auto make_db_leaf_ptr(art_key, value_view, Db &);

struct olc_impl_helpers;

using olc_art_policy =
    unodb::detail::basic_art_policy<unodb::olc_db,
                                    unodb::in_critical_section,
                                    unodb::optimistic_lock,
                                    unodb::optimistic_lock::read_critical_section,
                                    unodb::detail::olc_node_ptr,
                                    olc_inode_defs,
                                    unodb::detail::db_inode_qsbr_deleter,
                                    unodb::detail::db_leaf_qsbr_deleter>;

using olc_db_leaf_unique_ptr = olc_art_policy::db_leaf_unique_ptr;

using olc_inode_base = unodb::detail::basic_inode_impl<olc_art_policy>;

class olc_inode : public olc_inode_base {};

using olc_leaf = unodb::detail::olc_art_policy::leaf_type;

//
//
//

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

// Declare internal methods to quiet compiler warnings.
void create_leaf_if_needed(olc_db_leaf_unique_ptr &cached_leaf,
                           unodb::detail::art_key k, unodb::value_view v,
                           unodb::olc_db &db_instance);

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

  // Querying for a value given a key.
  [[nodiscard]] get_result get(key search_key) const noexcept;

  // Return true iff the tree is empty (no root leaf).
  //
  // FIXME Should this be using the same pattern as get() to detect
  // races around the existance of the root node and to have a proper
  // memory barrier when looking to see if the root node exists?
  [[nodiscard]] auto empty() const noexcept { return root == nullptr; }

  // Insert a value under a key iff there is no entry for that key.
  //
  // Note: Cannot be called during stack unwinding with std::uncaught_exceptions() > 0
  //
  // @return true if the key value pair was inserted.
  //
  // FIXME There should be a lambda variant of this to handle
  // conflicts and support upsert or delete-upsert semantics. This
  // would call the caller's lambda once the method was positioned on
  // the leaf.  The caller could then update the value or perhaps
  // delete the entry under the key.  
  [[nodiscard]] bool insert(key insert_key, value_view v);

  // Remove the entry associated with the key.
  //
  // @return true if the delete was successful (i.e. the key was found
  // in the tree and the associated index entry was removed).
  [[nodiscard]] bool remove(key remove_key);

  // Removes all entries in the index.
  //
  // Note: Only legal in single-threaded context, as destructor
  void clear() noexcept;

  ///
  /// iterator (the iterator is an internal API, the public API is scan()).
  ///

  // The OLC scan() logic tracks the version tag (a read_critical_section)
  // for each node in the stack.  This information is required because the
  // iter_result tuples already contain physical information read from
  // nodes which may have been invalidated by subsequent mutations.  The
  // scan is built on iterator methods for seek(), next(), prior(), etc.
  // These methods must restart (rebuilding the stack and redoing the work)
  // if they encounter a version tag for an element on the stack which is
  // no longer valid.  Restart works by performing a seek() to the key for
  // the leaf on the bottom of the stack.  Restarts can be full (from the
  // root) or partial (from the first element in the stack which was not
  // invalidated by the structural modification).
  // 
  // During scan(), the iterator seek()s to some key and then invokes the
  // caller's lambda passing a reference to a visitor object.  That visitor
  // allows the caller to access the key and/or value associated with the
  // leaf.  If the leaf is concurrently deleted from the structure, the
  // visitor relies on epoch protection to return the data from the now
  // invalidated leaf.  This is still the state that the caller would have
  // observed without the concurrent structural modification.  When next()
  // is called, it will discover that the leaf on the bottom of the stack
  // is not valid (it is marked as obsolete) and it will have to restart by
  // seek() to the key for that leaf and then invoking next() if the key
  // still exists and otherwise we should already be on the successor of
  // that leaf.
  //
  // Note: The OLC thread safety mechanisms permit concurrent non-atomic
  // (multi-work) mutations to be applied to nodes.  This means that a
  // thread can read junk in the middle of some reorganization of a node
  // (e.g., the keys or children are being reordered to maintain an
  // invariant for I16).  To protect against reading such junk, the thread
  // reads the version tag before and after it accesses data in the node
  // and restarts if the version information has changed.  The thread must
  // not act on information that it had read until it verifies that the
  // version tag remained unchanged across the read operation.
  class iterator {
    friend class olc_db;
    template <class> friend class visitor;

   protected:
    
    // Construct an empty iterator.
    inline iterator(olc_db& tree):db_(tree) {}

   public: // EXPOSED TO THE TESTS
    
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
    inline std::optional<const key> get_key() noexcept {
      // Note: If the iterator is on a leaf, we return the key for that
      // leaf regardless of whether the leaf has been deleted.  This is
      // part of the design semantics for the OLC ART scan.
      //
      // FIXME Eventually this will need to use the stack to reconstruct
      // the key from the path from the root to this leaf.  Right now it
      // is relying on the fact that simple fixed width keys are stored
      // directly in the leaves.
      if ( ! valid() ) return {}; // not positioned on anything.
      const auto& e = stack_.top();
      const auto& node = std::get<NP>( e );
      UNODB_DETAIL_ASSERT( node.type() == node_type::LEAF ); // On a leaf.
      const auto *const aleaf{ node.ptr<detail::olc_leaf *>() }; // current leaf.
      key_ = aleaf->get_key().decode(); // decode the key into the iterator's buffer.
      return key_; // return pointer to the internal key buffer.
    }
    
    // Iff the iterator is positioned on an index entry, then returns
    // the value associated with that index entry.
    //
    // FIXME OLC THIS MUST BE A qsbr_value_view. See get_result!!!!
    // (because in the general case the value is not something small
    // and trivially copyable).
    inline std::optional<const value_view> get_val() const noexcept {
      // Note: If the iterator is on a leaf, we return the value for
      // that leaf regardless of whether the leaf has been deleted.
      // This is part of the design semantics for the OLC ART scan.
      //
      if ( ! valid() ) return {}; // not positioned on anything.
      const auto& e = stack_.top();
      const auto& node = std::get<NP>( e );
      UNODB_DETAIL_ASSERT( node.type() == node_type::LEAF ); // On a leaf.
      const auto *const aleaf{ node.ptr<detail::olc_leaf *>() }; // current leaf.
      return aleaf->get_value_view();
    }
    
    inline bool operator==(const iterator& other) const noexcept {
      if ( &db_ != &other.db_ ) return false;                     // different tree?
      if ( stack_.empty() != other.stack_.empty() ) return false; // one stack is empty and the other is not?
      if ( stack_.empty() ) return true;                          // both empty.
      // The main reason to compare iterators is to detect the end().
      //
      // This is looking at all components in the element on the top
      // of the stack (including the read_critical_section).
      const auto& a = stack_.top();
      const auto& b = other.stack_.top();
      return a == b; // top of stack is same (inode, key, and child_index).
    }
    
    inline bool operator!=(const iterator& other) const noexcept {return !(*this == other);}

    // Debugging
    [[gnu::cold]] UNODB_DETAIL_NOINLINE void dump(std::ostream &os) const;

   protected:
    
    // Return true unless the stack is empty.
    inline bool valid() const noexcept { return ! stack_.empty(); }

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

    bool try_first() noexcept; // Core logic invoked from retry loop.
    bool try_last()  noexcept; // Core logic invoked from retry loop.
    bool try_next()  noexcept; // Core logic invoked from retry loop.
    bool try_prior() noexcept; // Core logic invoked from retry loop.
    // Push the given node onto the stack and traverse from the
    // caller's node to the left-most leaf under that node, pushing
    // nodes onto the stack as they are visited.
    bool try_left_most_traversal(detail::olc_node_ptr node, optimistic_lock::read_critical_section& parent_critical_section) noexcept;
    // Descend from the current state of the stack to the right most
    // child leaf, updating the state of the iterator during the
    // descent.
    bool try_right_most_traversal(detail::olc_node_ptr node, optimistic_lock::read_critical_section& parent_critical_section) noexcept;
    bool try_seek(const detail::art_key& search_key, bool& match, bool fwd) noexcept; // Core logic invoked from retry loop.
    
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
      , version_tag           // The NP version tag invariant when the KB and CI were read from the node.
      >;
  
    static constexpr int NP = 0; // node pointer (to an internal node or leaf, can also be the root node or root leaf)
    static constexpr int KB = 1; // key byte     (when stepping down from that node)
    static constexpr int CI = 2; // child_index  (along which the path steps down from that node)
    static constexpr int VT = 3; // version tag  (for that node when obtaining the key_byte and child_index).

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
  
  // Scan the tree, applying the caller's lambda to each visited leaf.
  //
  // @param fn A function f(visitor&) returning [bool::halt].  The
  // traversal will halt if the function returns [true].
  //
  // @param fwd When [true] perform a forward scan, otherwise perform
  // a reverse scan.
  template <typename FN>
  inline void scan(FN fn, bool fwd = true) noexcept {
    if ( empty() ) return;
    if ( fwd ) {
      auto it { iterator(*this).first() };
      visitor v{ it };
      while ( it.valid() ) {
        if ( UNODB_DETAIL_UNLIKELY( fn( v ) ) ) break;
        it.next();
      }
    } else {
      auto it { iterator(*this).last() };
      visitor v { it };
      while ( it.valid() ) {
        if ( UNODB_DETAIL_UNLIKELY( fn( v ) ) ) break;
        it.prior();
      }
    }
  }    

  // Scan in the indicated direction, applying the caller's lambda to
  // each visited leaf.
  //
  // @param fromKey_ is an inclusive bound for the starting point of
  // the scan.
  //
  // @param fn A function f(visitor&) returning [bool::halt].  The
  // traversal will halt if the function returns [true].
  //
  // @param fwd When [true] perform a forward scan, otherwise perform
  // a reverse scan.
  template <typename FN>
  inline void scan(const key fromKey_, FN fn, bool fwd = true) noexcept {
    if ( empty() ) return;
    const detail::art_key fromKey{fromKey_};  // convert to internal key
    bool match {};
    if ( fwd ) {
      auto it { iterator(*this).seek( fromKey, match, true/*fwd*/ ) };
      visitor v { it };
      while ( it.valid() ) {
        if ( UNODB_DETAIL_UNLIKELY( fn( v ) ) ) break;
        it.next();
      }
    } else {
      auto it { iterator(*this).seek( fromKey, match, false/*fwd*/ ) };
      visitor v { it };
      while ( it.valid() ) {
        if ( UNODB_DETAIL_UNLIKELY( fn( v ) ) ) break;
        it.prior();
      }
    }
  }    

  // Scan the key range, applying the caller's lambda to each visited
  // leaf.  The scan will proceed in lexicographic order iff fromKey
  // is less than toKey and in reverse lexicographic order iff toKey
  // is less than fromKey.
  //
  // @param fromKey_ is an inclusive bound for the starting point of
  // the scan.
  //
  // @param toKey_ is an exclusive bound for the ending point of the
  // scan.
  //
  // @param fn A function f(visitor&) returning [bool::halt].  The
  // traversal will halt if the function returns [true].
  template <typename FN>
  inline void scan(const key fromKey_, const key toKey_, FN fn) noexcept {
    // FIXME There should be a cheaper way to handle the exclusive bound
    // case.  This relies on key decoding, which is expensive for variable
    // length keys.  At a minimum, we could compare the internal keys to
    // avoid the decoding.  But it would be nice to know the leaf that we
    // will not visit and just halt when we get there.
    constexpr bool debug = false;  // set true to debug scan. FIXME REMOVE [debug]?
    if ( empty() ) return;
    const detail::art_key fromKey{fromKey_};  // convert to internal key
    const detail::art_key toKey{toKey_};      // convert to internal key
    const auto ret = fromKey.cmp( toKey );    // compare the internal keys.
    const bool fwd { ret < 0 };               // fromKey is less than toKey
    if ( ret == 0 ) return;                   // NOP if fromKey == toKey since toKey is exclusive upper bound.
    bool match {};
    if ( fwd ) {
      auto it1 { iterator(*this).seek( fromKey, match, true/*fwd*/ ) }; // lower bound
      // auto it2 { end().seek( toKey, match, true/*fwd*/ ) }; // upper bound
      // if ( it2.get_key() == toKey_ ) it2.prior();  // back up one if the toKey exists (exclusive upper bound).
      if constexpr ( debug ) {
        std::cerr<<"scan:: fwd"<<std::endl;
        std::cerr<<"scan:: fromKey="<<fromKey_<<std::endl; it1.dump(std::cerr);
        // std::cerr<<"scan:: toKey="<<toKey_<<std::endl; it2.dump(std::cerr);
      }
      visitor v { it1 };
      while ( it1.valid() && it1.get_key() < toKey_ ) {
        if ( UNODB_DETAIL_UNLIKELY( fn( v ) ) ) break;
        // if ( UNODB_DETAIL_UNLIKELY( it1.current_node() == it2.current_node() ) ) break;
        it1.next();
        if constexpr( debug ) {
          std::cerr<<"scan: next()"<<std::endl; it1.dump( std::cerr );
        }
      }
    } else { // reverse traversal.
      auto it1 { iterator(*this).seek( fromKey, match, true/*fwd*/ ) }; // upper bound
      // auto it2 { end().seek( toKey, match, false/*fwd*/ ) }; // lower bound
      // if ( it2.get_key() == toKey_ ) it2.next();  // advance one if the toKey exists (exclusive lower bound during reverse traversal)
      if constexpr( debug ) {
        std::cerr<<"scan:: rev"<<std::endl;
        std::cerr<<"scan:: fromKe   y="<<fromKey_<<std::endl; it1.dump(std::cerr);
        // std::cerr<<"scan:: toKey="<<toKey_<<std::endl; it2.dump(std::cerr);
      }
      visitor v { it1 };
      while ( it1.valid() && it1.get_key() > toKey_ ) {
        if ( UNODB_DETAIL_UNLIKELY( fn( v ) ) ) break;
        // if ( UNODB_DETAIL_UNLIKELY( it1.current_node() == it2.current_node() ) ) break;
        it1.prior();
        if constexpr( debug ) {
          std::cerr<<"scan: prior()"<<std::endl; it1.dump( std::cerr );
        }
      }
    }
  }
  
  //
  // TEST ONLY METHODS
  //

  // Used to write the iterator tests.
  auto __test_only_iterator__() noexcept {return iterator(*this);}
  
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
