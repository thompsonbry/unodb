// Copyright 2019-2024 Laurynas Biveinis
#ifndef UNODB_DETAIL_ART_INTERNAL_HPP
#define UNODB_DETAIL_ART_INTERNAL_HPP

//
// CAUTION: [global.hpp] MUST BE THE FIRST INCLUDE IN ALL SOURCE AND
// HEADER FILES !!!
//
// This header defines _GLIBCXX_DEBUG and _GLIBCXX_DEBUG_PEDANTIC for
// DEBUG builds.  If some standard headers are included before and
// after those symbols are defined, then that results in different
// container internal structure layouts and that is Not Good.
#include "global.hpp"  // IWYU pragma: keep

// IWYU pragma: no_include <__fwd/ostream.h>
// IWYU pragma: no_include <_string.h>

#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <iosfwd>  // IWYU pragma: keep
#include <memory>
#include <type_traits>

#include "art_common.hpp"
#include "assert.hpp"
#include "heap.hpp"  // allocate_aligned and free_aligned
#include "node_type.hpp"
#include "portability_builtins.hpp"  // key encode and decode

namespace unodb::detail {

// Forward declarations to use in unodb::db and its siblings
template <class>
class [[nodiscard]] basic_leaf;

template <class, class>
class [[nodiscard]] basic_db_leaf_deleter;

// Internal ART key in binary-comparable format.  Application keys may
// be simple fixed width types (such as std::uint64_t) or variable
// length keys.  For the former, there are convenience methods on db,
// olc_db, etc. to convert external keys into the binary compariable
// format.  For the latter, the application is responsible for
// converting the data (e.g., certain columns in some ordering for a
// row of some relation) into the internal binary comparable key
// format.  A convenience class is offered to encode data.  The
// encoding is always well defined and decoding exists for all simple
// fixed width data types.  Unicode encoding is complex and out of
// scope - use a quality library such as ICU to produce appropriate
// Unicode sort keys for your application.  Unicode decoding is NOT
// well defined.  Applications involving database records and Unicode
// data will typically store the record identifier in a secondary
// index (ART) as the value associated with the key.  Using the record
// identifier, the original tuple can be discovered and the original
// Unicode data recovered from that tuple.
template <typename KeyType>
struct [[nodiscard]] basic_art_key final {
  // Convert an external key into an internal key supporting
  // lexicographic comparison.  This is only intended for key types
  // for which simple conversions are possible.  For complex keys,
  // including multiple key components or Unicode data, the
  // application should use a gsl::space<std::byte> which already
  // supports lexicographic comparison.
  //
  // TODO(thompsonbry) variable length keys. pull encode() out into a
  // key encoder.
  [[nodiscard, gnu::const]] static UNODB_DETAIL_CONSTEXPR_NOT_MSVC KeyType
  make_binary_comparable(KeyType k) noexcept {
#ifdef UNODB_DETAIL_LITTLE_ENDIAN
    return bswap(k);
#else
#error Needs implementing
#endif
  }

  constexpr basic_art_key() noexcept = default;

  UNODB_DETAIL_CONSTEXPR_NOT_MSVC explicit basic_art_key(KeyType key_) noexcept
      : key{make_binary_comparable(key_)} {}

  // @return -1, 0, or 1 if this key is LT, EQ, or GT the other key.
  [[nodiscard, gnu::pure]] constexpr int cmp(
      basic_art_key<KeyType> key2) const noexcept {
    // TODO(thompsonbry) : variable length keys.  This needs to
    // consider no more bytes than the shorter key and if the two keys
    // have the same prefix, then they are != if one is longer (and
    // for == we can just compare the size as a short cut for this).
    // Also needs unit tests for variable length keys.
    return std::memcmp(&key, &key2.key, size);
  }

  // Return the byte at the specified index position in the binary
  // comparable key.
  [[nodiscard, gnu::pure]] constexpr auto operator[](
      std::size_t index) const noexcept {
    UNODB_DETAIL_ASSERT(index < size);
    return key_bytes[index];
  }

  // TODO(thompsonbry) variable length keys.  This returns the
  // internal key rather than decoding the key.  It is used in THREE
  // (3) places by key_prefix.  Those uses need to be cleaned up and
  // this removed since it completely breaks encapsulation.  Also,
  // this method really can't be written for variable length keys
  // unless we are returning a gsl::span.  I've changed this from a
  // cast operator to something more explicit to make it easier to
  // track and fix this up.
  [[nodiscard, gnu::pure]] constexpr std::uint64_t get_internal_key()
      const noexcept {
    return key;
  }

  // Return the decoded form of the key.
  //
  // TODO(thompsonbry) variable length keys. pull decode() out into a
  // key decoder.  Note that key decoding is best effort only. This is
  // ONLY used by the iterator::visitor::get_key() method.
  [[nodiscard, gnu::pure]] constexpr KeyType decode() const noexcept {
#ifdef UNODB_DETAIL_LITTLE_ENDIAN
    return bswap(key);
#else
#error Needs implementing
#endif
  }

  // Shift the internal key some number of bytes to the right, causing
  // the key to be shorter by that may bytes.
  //
  // Note: For a fixed width type, this causes the key to be logically
  // zero filled as it becomes shorter.  E.g.
  //
  // 0x0011223344556677 shift_right(2) => 0x2233445566770000
  constexpr void shift_right(const std::size_t num_bytes) noexcept {
    UNODB_DETAIL_ASSERT(num_bytes <= size);
    key >>= (num_bytes * 8);
  }

  static constexpr auto size = sizeof(KeyType);

  union {
    KeyType key;
    std::array<std::byte, size> key_bytes;
  };

  static void static_asserts() {
    static_assert(std::is_trivially_copyable_v<basic_art_key<KeyType>>);
    static_assert(sizeof(basic_art_key<KeyType>) == sizeof(KeyType));
  }
};  // class basic_art_key

using art_key = basic_art_key<unodb::key>;

[[gnu::cold]] UNODB_DETAIL_NOINLINE void dump_byte(std::ostream &os,
                                                   std::byte byte);

[[gnu::cold]] UNODB_DETAIL_NOINLINE std::ostream &operator<<(
    std::ostream &os UNODB_DETAIL_LIFETIMEBOUND, art_key key);

// typed class representing the depth of the tree.
class [[nodiscard]] tree_depth final {
 public:
  using value_type = unsigned;

  explicit constexpr tree_depth(value_type value_ = 0) noexcept
      : value{value_} {
    UNODB_DETAIL_ASSERT(value <= art_key::size);
  }

  // NOLINTNEXTLINE(google-explicit-constructor)
  [[nodiscard, gnu::pure]] constexpr operator value_type() const noexcept {
    UNODB_DETAIL_ASSERT(value <= art_key::size);
    return value;
  }

  constexpr tree_depth &operator++() noexcept {
    ++value;
    UNODB_DETAIL_ASSERT(value <= art_key::size);
    return *this;
  }

  constexpr void operator+=(value_type delta) noexcept {
    value += delta;
    UNODB_DETAIL_ASSERT(value <= art_key::size);
  }

 private:
  value_type value;
};

template <class Header, class Db>
class basic_db_leaf_deleter {
 public:
  using leaf_type = basic_leaf<Header>;

  static_assert(std::is_trivially_destructible_v<leaf_type>);

  constexpr explicit basic_db_leaf_deleter(
      Db &db_ UNODB_DETAIL_LIFETIMEBOUND) noexcept
      : db{db_} {}

  void operator()(leaf_type *to_delete) const noexcept;

  [[nodiscard, gnu::pure]] Db &get_db() const noexcept { return db; }

 private:
  Db &db;
};

template <class Header, class Db>
using basic_db_leaf_unique_ptr =
    std::unique_ptr<basic_leaf<Header>, basic_db_leaf_deleter<Header, Db>>;

template <class T>
struct dependent_false : std::false_type {};

template <class INode, class Db>
class basic_db_inode_deleter {
 public:
  constexpr explicit basic_db_inode_deleter(
      Db &db_ UNODB_DETAIL_LIFETIMEBOUND) noexcept
      : db{db_} {}

  void operator()(INode *inode_ptr) noexcept;

  [[nodiscard, gnu::pure]] Db &get_db() noexcept { return db; }

 private:
  Db &db;
};

// basic_node_ptr is a tagged pointer (the tag is the node type).  You
// have to know statically the target type, then call
// node_ptr_var.ptr<target_type *>.ptr() to get target_type.
UNODB_DETAIL_DISABLE_MSVC_WARNING(26490)
template <class Header>
class [[nodiscard]] basic_node_ptr {
 public:
  using header_type = Header;

  // The default constructor does not initialize fields: it is used by
  // std::array and we don't want to initialize to zero or any other value there
  // at construction time.
  // cppcheck-suppress uninitMemberVar
  constexpr basic_node_ptr() noexcept = default;

  explicit basic_node_ptr(std::nullptr_t) noexcept
      : tagged_ptr{reinterpret_cast<std::uintptr_t>(nullptr)} {}

  // construct a node pointer given a raw pointer and a node type.
  //
  // Note: The constructor casts away [const] for use when the
  // node_ptr will be [const].
  basic_node_ptr(const header_type *ptr UNODB_DETAIL_LIFETIMEBOUND,
                 unodb::node_type type) noexcept
      : tagged_ptr{tag_ptr(const_cast<header_type *>(ptr), type)} {}

  basic_node_ptr<Header> &operator=(std::nullptr_t) noexcept {
    tagged_ptr = reinterpret_cast<std::uintptr_t>(nullptr);
    return *this;
  }

  [[nodiscard, gnu::pure]] constexpr auto type() const noexcept {
    return static_cast<unodb::node_type>(tagged_ptr & tag_bit_mask);
  }

  [[nodiscard, gnu::pure]] constexpr auto raw_val() const noexcept {
    return tagged_ptr;
  }

  template <class T>
  [[nodiscard, gnu::pure]] auto *ptr() const noexcept {
    return reinterpret_cast<T>(tagged_ptr & ptr_bit_mask);
  }

  // same raw_val means same type and same ptr.
  [[nodiscard, gnu::pure]] auto operator==(
      const basic_node_ptr &other) const noexcept {
    return tagged_ptr == other.tagged_ptr;
  }

  [[nodiscard, gnu::pure]] auto operator==(std::nullptr_t) const noexcept {
    return tagged_ptr == reinterpret_cast<std::uintptr_t>(nullptr);
  }

  [[nodiscard, gnu::pure]] auto operator!=(std::nullptr_t) const noexcept {
    return tagged_ptr != reinterpret_cast<std::uintptr_t>(nullptr);
  }

 private:
  std::uintptr_t tagged_ptr;

  [[nodiscard, gnu::const]] static std::uintptr_t tag_ptr(
      Header *ptr_, unodb::node_type tag) noexcept {
    const auto uintptr = reinterpret_cast<std::uintptr_t>(ptr_);
    const auto result =
        uintptr | static_cast<std::underlying_type_t<decltype(tag)>>(tag);
    UNODB_DETAIL_ASSERT((result & ptr_bit_mask) == uintptr);
    return result;
  }

  [[nodiscard, gnu::const]] static constexpr unsigned mask_bits_needed(
      unsigned count) noexcept {
    return count < 2 ? 1 : 1 + mask_bits_needed(count >> 1U);
  }

  static constexpr auto lowest_non_tag_bit =
      1ULL << mask_bits_needed(node_type_count);
  static constexpr auto tag_bit_mask = lowest_non_tag_bit - 1;
  static constexpr auto ptr_bit_mask = ~tag_bit_mask;

  static auto static_asserts() {
    static_assert(sizeof(basic_node_ptr<Header>) == sizeof(void *));
    static_assert(alignof(header_type) - 1 > lowest_non_tag_bit);
  }
};
UNODB_DETAIL_RESTORE_MSVC_WARNINGS()

///
/// fast utility methods TODO(thompsonbry) move to a header?
///

/// 32bit int shift-or utility function that is used by HighestOneBit
/// and NextPowerofTwo functions.  the only reason we have this
/// function is to reduce code repetition.
template <typename T>
constexpr typename std::enable_if<std::is_integral<T>::value, T>::type
shiftOr32bitInt(T i) {
  i |= (i >> 1);
  i |= (i >> 2);
  i |= (i >> 4);
  i |= (i >> 8);
  i |= (i >> 16);
  return i;
}

// Templatated function to find the next power of 2.  We have 32-bit
// and 64-bit specializations.
//
// Note: it will overflow if the there is no higher power of 2 for a
// given type T.
template <typename T>
constexpr typename std::enable_if<std::is_integral<T>::value && sizeof(T) == 4,
                                  T>::type
NextPowerOfTwo(T i) {
  return shiftOr32bitInt(i) + 1;
}

template <typename T>
constexpr typename std::enable_if<std::is_integral<T>::value && sizeof(T) == 8,
                                  T>::type
NextPowerOfTwo(T i) {
  i = shiftOr32bitInt(i);
  i |= (i >> 32);
  return ++i;
}

}  // namespace unodb::detail

namespace unodb {

// An object visited by the scan API.  The visitor passed to the
// caller's lambda by the scan for each index entry visited by the
// scan.
template <typename Iterator>
class visitor {
  friend class olc_db;
  friend class db;

 protected:
  Iterator &it;
  explicit visitor(Iterator &it_) : it(it_) {}

 public:
  // Visit the (decoded) key.
  //
  // Note: The lambda MUST NOT export a reference to the visited key.
  // If you want to access the visited key outside of the scope of a
  // single lambda invocation, then you must make a copy of the data.
  //
  // Note: Key decoding can be expensive and its utility is limited to
  // simple primitive keys.  In particular, key decoding is not well
  // defined for Unicode data in keys.
  //
  // TODO(thompsonbry) Variable length keys: We need to define a
  // visitor method to visit the internal key buffer without any
  // decoding.
  inline auto get_key() const noexcept { return it.get_key().value(); }

  // Visit the value.
  //
  // Note: The lambda MUST NOT export a reference to the visited
  // value.  If you to access the value outside of the scope of a
  // single lambda invocation, then you must make a copy of the data.
  inline auto get_value() const noexcept { return it.get_val().value(); }
};  // class visitor

///
/// Key encodes and key decoder
///
// const auto dynamic_extent = gsl::dynamic_extent;

// TODO(thompsonbry) : variable length keys. write and test
// key_encoder.
//
// TODO(thompsonbry) : variable length integer encoding and decoding
// support.
//
// TODO Minimum initial capacity and memory pooling?  Thread local?
// Special case for uint64_t only keys.
class key_encoder {
  // used for the initial buffer (one cache line)
  std::byte ibuf[64];

  // The buffer to accmulate the encoded key.  Originally this is the
  // [ibuf].  If that overflows, then something will be allocated.
  std::byte *buf;
  size_t cap;  // current buffer capacity
  size_t len;  // #of bytes in the buffer having encoded data.

  // ensures that we have at least the specified capacity in the buffer.
  void ensureCapacity(size_t min_capacity) {
    if (UNODB_DETAIL_LIKELY(cap >= min_capacity)) return;
    // Find the allocation size in bytes which satisfies that minimum
    // capacity.  We first look for the next power of two.  Then we
    // adjust for the case where the [min_capacity] is already a power
    // of two (a common edge case).
    auto nsize = detail::NextPowerOfTwo(min_capacity);
    auto asize = (min_capacity == (nsize >> 1)) ? min_capacity : nsize;
    auto tmp = detail::allocate_aligned(asize);  // new allocation.
    std::memcpy(tmp, buf, len);                  // copy over the data.
    if (cap >= sizeof(ibuf)) {  // free old buffer iff allocated
      detail::free_aligned(buf);
    }
    buf = reinterpret_cast<std::byte *>(tmp);
  }

 public:
  // setup a new key encoder.
  key_encoder() : buf(&ibuf[0]), cap(sizeof(ibuf)), len(0) {}

  void encode(std::int64_t v) {
    v = (v < 0)  // fix up lexicographic ordering.
            ? v - static_cast<std::int64_t>(0x8000000000000000L)
            : v + static_cast<std::int64_t>(0x8000000000000000L);
    encode(reinterpret_cast<std::uint64_t &>(v));
  }

  void encode(std::uint64_t v) {
    ensureCapacity(len + sizeof(v));
#ifdef UNODB_DETAIL_LITTLE_ENDIAN
    v = detail::bswap(v);
#else
#error Needs implementing
#endif
    buf[len++] = static_cast<std::byte>(v >> 56);
    buf[len++] = static_cast<std::byte>(v >> 48);
    buf[len++] = static_cast<std::byte>(v >> 40);
    buf[len++] = static_cast<std::byte>(v >> 32);
    buf[len++] = static_cast<std::byte>(v >> 24);
    buf[len++] = static_cast<std::byte>(v >> 16);
    buf[len++] = static_cast<std::byte>(v >> 8);
    buf[len++] = static_cast<std::byte>(v >> 0);
  }
};  // class key_encoder

// TODO(thompsonbry) : variable length keys. write and test
// key_decoder.
class key_decoder {
 private:
  const key_view buf;
  size_t offset{};

 public:
  key_decoder(const key_view data) : buf(data) {}

  // Convert an internal key into an external key. This is only
  // intended for key types for which simple conversions are possible.
  // For complex keys, including multiple key components or Unicode
  // data, the application should use a gsl::space<std::byte> which
  // already supports lexicographic comparison.
  //
  // TODO(thompsonbry) variable length keys. pull decode() out into a
  // key decoder.  Note that key decoding is best effort only.
  void decode(std::uint64_t &) {
    // #ifdef UNODB_DETAIL_LITTLE_ENDIAN
    //     out = unodb::detail::bswap(
    //         *reinterpret_cast<const std::uint64_t*>( buf.data() + offset ) //
    //         TODO(thompsonbry) Is this safe for unaligned data?
    //                                );
    // #else
    // #error Needs implementing
    // #endif
    //     offset += sizeof(out);
  }

};  // class key_decoder

}  // namespace unodb

#endif  // UNODB_DETAIL_ART_INTERNAL_HPP
