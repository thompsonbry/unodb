// Copyright 2019-2025 UnoDB contributors
#ifndef UNODB_DETAIL_ART_COMMON_HPP
#define UNODB_DETAIL_ART_COMMON_HPP

// Should be the first include
#include "global.hpp"  // IWYU pragma: keep

// IWYU pragma: no_include <__fwd/ostream.h>
// IWYU pragma: no_include <ostream>
// IWYU pragma: no_include <ostream.h>

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <iomanip>
#include <iosfwd>  // IWYU pragma: keep
#include <iostream>
#include <span>

#include "heap.hpp"
#include "portability_builtins.hpp"

namespace unodb {

template <typename Key>
class db;

template <typename Key>
class olc_db;

/// Values are passed as non-owning pointers to memory with associated
/// length (std::span). The memory is copied upon insertion.
using value_view = std::span<const std::byte>;

/// Keys are passed as non-owning pointers to memory with associated
/// length (std::span).
using key_view = std::span<const std::byte>;

/// An object visited by the scan API.  The visitor passed to the
/// caller's lambda by the scan for each index entry visited by the
/// scan.
template <typename Iterator>
class visitor {
 protected:
  Iterator &it;
  explicit visitor(Iterator &it_) : it(it_) {}

 public:
  using key_type = typename Iterator::key_type;
  /// Visit the encoded key.
  ///
  /// Note: The lambda MUST NOT export a reference to the visited key.
  /// If you want to access the visited key outside of the scope of a
  /// single lambda invocation, then you must make a copy of the data.
  ///
  /// Note: The application MAY use the [key_decoder] to decode any
  /// key corresponding to a sequence of one or more primitive data
  /// types.  However, key decoding is not well defined for Unicode
  /// sort keys.  The recommended pattern when the key contains
  /// Unicode data is to convert it to a sort key using some collation
  /// order.  The Unicode data may then be recovered by associating
  /// the key with a record identifier, looking up the record and
  /// reading off the Unicode value there.  This is a common secondary
  /// index scenario.
  [[nodiscard]] inline auto get_key() const noexcept {
    // TODO(laurynas) The auto return appears required for get_key().
    // E.g., example_art.cpp fails with return type == key_type.
    return it.get_key();
  }

  /// Visit the value.
  ///
  /// Note: The lambda MUST NOT export a reference to the visited
  /// value.  If you to access the value outside of the scope of a
  /// single lambda invocation, then you must make a copy of the data.
  [[nodiscard]] inline auto get_value() const noexcept {
    // Note: auto return required for olc qsbr wrapper.
    return it.get_val();
  }

 private:
  friend class olc_db<key_type>;
  friend class db<key_type>;
};  // class visitor

namespace detail {

/// A constant determining the initial capacity for the key_encoder
/// and other similar internal buffers.  This should be set high
/// enough that such objects DO NOT allocate for commonly used key
/// lengths.  These objects use an internal buffer of this capacity
/// and then switch over to an explicitly allocated buffer if the
/// capacity would be exceeded.
///
/// Note: If you are only using fixed width keys, then this can be
/// sizeof(T).  But in typical scenarios these objects are on the
/// stack and there is little if any penalty to having a larger
/// initial capacity for these buffers.
static constexpr size_t INITIAL_BUFFER_CAPACITY = 256;

/// Dump the a byte as a hexadecimal number.
[[gnu::cold]] void dump_byte(std::ostream &os, std::byte byte);

/// Dump the value as a sequence of bytes.
[[gnu::cold]] void dump_val(std::ostream &os, unodb::value_view v);

/// Dump a std::span byte-wise (works on any key_view).
template <typename T>
[[gnu::cold]] void dump_key(std::ostream &os, key_view key) {
  os << "key: 0x";
  const auto sz = key.size_bytes();
  for (std::size_t i = 0; i < sz; ++i) unodb::detail::dump_byte(os, key[i]);
}

/// Dump the key in lexicographic byte-wise order.
template <typename T>
[[gnu::cold]] void dump_key(std::ostream &os, T key) {
  if constexpr (std::is_same_v<T, key_view>) {
    os << "key: 0x";
    const auto sz = key.size_bytes();
    for (std::size_t i = 0; i < sz; ++i) unodb::detail::dump_byte(os, key[i]);
  } else {
    os << "key: 0x" << std::hex << std::setfill('0') << std::setw(sizeof(key))
       << key << std::dec;
  }
}

///
/// fast utility methods
///

/// 32bit int shift-or utility function that is used by next_power_of_two
/// function.
template <typename T>
constexpr typename std::enable_if<std::is_integral<T>::value, T>::type
shift_or_32bit_int(T i) {
  i |= (i >> 1);
  i |= (i >> 2);
  i |= (i >> 4);
  i |= (i >> 8);
  i |= (i >> 16);
  return i;
}

/// Find the next power of 2 for a 32-bit or 64-bit value.
///
/// Note: it will overflow if the there is no higher power of 2 for a
/// given type T.
template <typename T>
constexpr typename std::enable_if<std::is_integral<T>::value && sizeof(T) == 4,
                                  T>::type
next_power_of_two(T i) {
  return shift_or_32bit_int(i) + static_cast<T>(1);
}

template <typename T>
constexpr typename std::enable_if<std::is_integral<T>::value && sizeof(T) == 8,
                                  T>::type
next_power_of_two(T i) {
  i = shift_or_32bit_int(i);
  i |= (i >> 32U);
  return ++i;
}

/// Compute the lexicographically next bit permutation.  This method
/// gets used when you want to form an exclusive upper bound for some
/// key range.  You take the upper bound and form the bitwise
/// successor of that value to turn it into an exclusive upper
/// bound. This has to be done for each component of the composite
/// key, working backwards from the end of the key, until a component
/// is found which does not overflow (is not already ~0).
///
/// Suppose we have a pattern of N bits set to 1 in an integer and we
/// want the next permutation of N 1 bits in a lexicographical
/// sense. For example, if N is 3 and the bit pattern is 00010011, the
/// next patterns would be 00010101, 00010110, 00011001,00011010,
/// 00011100, 00100011, and so forth. The following is a fast way to
/// compute the next permutation.
///
/// Source:
/// https://graphics.stanford.edu/~seander/bithacks.html#NextBitPermutation
///
/// @param v Some unsigned value.
template <typename T>
T successor(T v) {
  const T t = v | (v - 1u);  // t gets v's least significant 0 bits set to 1
  // Next set to 1 the most significant bit to change, set to 0 the
  // least significant ones, and add the necessary 1 bits.
  const T w = (t + 1) | (((~t & -~t) - 1) >> (ctz(v) + 1));
  return w;
}

/// Utility method for power of two expansion of buffers (internal
/// API, forward declaration).
inline void ensure_capacity(std::byte *&buf,     // buffer to resize
                            size_t &cap,         // current buffer capacity
                            size_t off,          // current #of used bytes
                            size_t min_capacity  // desired new minimum capacity
) {
  // Find the allocation size in bytes which satisfies that minimum
  // capacity.  We first look for the next power of two.  Then we
  // adjust for the case where the [min_capacity] is already a power
  // of two (a common edge case).
  auto nsize = detail::next_power_of_two(min_capacity);
  auto asize = (min_capacity == (nsize >> 1U)) ? min_capacity : nsize;
  auto *tmp = detail::allocate_aligned(asize);  // new allocation.
  std::memcpy(tmp, buf, off);                   // copy over the data.
  if (cap > INITIAL_BUFFER_CAPACITY) {          // free old buffer iff allocated
    detail::free_aligned(buf);
  }
  buf = reinterpret_cast<std::byte *>(tmp);
  cap = asize;
}

}  // namespace detail

///
/// Key encodes and key decoder
///

/// A utility class to generate binary comparable keys from a sequence
/// of key components.  This class supports the various kinds of
/// primitive data types and provides support for the caller to pass
/// through Unicode sort keys.
class key_encoder {
  //
  // TODO(thompsonbry) - variable length keys - handle floating point types
  // TODO(thompsonbry) - variable length keys - handle successors
  //
  // TODO(thompsonbry) - variable length keys - handle unicode sort keys
  // (caller must normalize, generate the sort key, and pad?)
  //
  // TODO(thompsonbry) - variable length keys - attempt to simplify by
  // using templates for msb, bswap, and encode/decode of unsigned
  // values.
 protected:
  // highest bit for various data types.
  static constexpr std::uint8_t msb8 = 1U << 7;
  static constexpr std::uint16_t msb16 = 1U << 15;
  static constexpr std::uint32_t msb32 = 1U << 31;
  static constexpr std::uint64_t msb64 = 1ULL << 63;

  /// The current capacity of the buffer.
  [[nodiscard]] size_t capacity() const noexcept { return cap; }

  /// Ensure that the buffer can hold at least [req] additional bytes.
  void ensure_available(size_t req) {
    if (UNODB_DETAIL_UNLIKELY(off + req > cap)) {
      ensure_capacity(off + req);  // resize
    }
  }

  /// The maximum length of a text component of the key.  Keys are
  /// truncated to at most this many bytes and then logically extended
  /// using the #pad byte and a trailing run length until the field is
  /// logically #maxlen bytes wide.
  static constexpr auto maxlen{std::numeric_limits<std::uint16_t>::max()};

  /// The pad byte used when encoding variable length text into a key
  /// to logically extend the text field to #maxlen bytes.  The pad
  /// byte (which is added to the buffer as an unsigned value) is
  /// followed by a run length count such that the key is logically
  /// padded out to the maximum length of a text field, which is
  /// #maxlen.
  static constexpr auto pad{static_cast<std::byte>(0x00)};

 public:
  /// setup a new key encoder.
  key_encoder() noexcept = default;

  ~key_encoder() {
    if (cap > sizeof(ibuf)) {  // free old buffer iff allocated
      detail::free_aligned(buf);
    }
  }

  /// Reset the encoder to encode another key.
  key_encoder &reset() {
    off = 0;
    return *this;
  }

  /// Read-only view of the internal buffer showing only those bytes
  /// that were encoded since the last reset().
  [[nodiscard]] key_view get_key_view() const noexcept {
    return key_view(buf, off);
  }

  /// The number of bytes of data in the internal buffer.
  [[nodiscard]] size_t size_bytes() const noexcept { return off; }

  //
  // signed integers
  //

  key_encoder &encode(std::int8_t v) {
    // TODO(laurynas): look into inling the 1 constants.
    constexpr auto i_one = static_cast<int8_t>(1);
    constexpr auto u_one = static_cast<uint8_t>(1);
    const auto u = static_cast<uint8_t>(
        (v >= 0) ? msb8 + static_cast<uint8_t>(v)
                 : msb8 - static_cast<uint8_t>(-(v + i_one)) - u_one);
    return encode(u);
  }

  key_encoder &encode(std::int16_t v) {
    constexpr auto i_one = static_cast<int16_t>(1);
    constexpr auto u_one = static_cast<uint16_t>(1);
    const auto u = static_cast<uint16_t>(
        (v >= 0) ? msb16 + static_cast<uint16_t>(v)
                 : msb16 - static_cast<uint16_t>(-(v + i_one)) - u_one);
    return encode(u);
  }

  key_encoder &encode(std::int32_t v) {
    constexpr int32_t i_one = 1;
    constexpr uint32_t u_one = static_cast<uint32_t>(1);
    const uint32_t u =
        (v >= 0) ? msb32 + static_cast<uint32_t>(v)
                 : msb32 - static_cast<uint32_t>(-(v + i_one)) - u_one;
    return encode(u);
  }

  key_encoder &encode(std::int64_t v) {
    constexpr int64_t i_one = static_cast<int64_t>(1);
    constexpr uint64_t u_one = static_cast<uint64_t>(1);
    const uint64_t u =
        (v >= 0) ? msb64 + static_cast<uint64_t>(v)
                 : msb64 - static_cast<uint64_t>(-(v + i_one)) - u_one;
    return encode(u);
  }

  //
  // unsigned integers
  //

  key_encoder &encode(std::uint8_t v) {
    ensure_available(sizeof(v));
    buf[off++] = reinterpret_cast<const std::byte &>(v);
    return *this;
  }

  key_encoder &encode(std::uint16_t v) {
    ensure_available(sizeof(v));
#ifdef UNODB_DETAIL_LITTLE_ENDIAN
    const auto u = unodb::detail::bswap(v);
#else
    const auto u = v;
#endif
    UNODB_DETAIL_ASSERT(sizeof(u) == sizeof(v));
    std::memcpy(buf + off, &u, sizeof(v));
    off += sizeof(v);
    return *this;
  }

  key_encoder &encode(std::uint32_t v) {
    ensure_available(sizeof(v));
#ifdef UNODB_DETAIL_LITTLE_ENDIAN
    const auto u = unodb::detail::bswap(v);
#else
    const auto u = v;
#endif
    UNODB_DETAIL_ASSERT(sizeof(u) == sizeof(v));
    std::memcpy(buf + off, &u, sizeof(v));
    off += sizeof(v);
    return *this;
  }

  key_encoder &encode(std::uint64_t v) {
    ensure_available(sizeof(v));
#ifdef UNODB_DETAIL_LITTLE_ENDIAN
    const auto u = unodb::detail::bswap(v);
#else
    const auto u = v;
#endif
    UNODB_DETAIL_ASSERT(sizeof(u) == sizeof(v));
    std::memcpy(buf + off, &u, sizeof(v));
    off += sizeof(v);
    return *this;
  }

  /// This method may be used to encode Unicode (UTF8) sort keys into
  /// a key and is required for use cases where the text field is not
  /// the terminal component of the key.  You can also get away with
  /// encoding any C string data as long as the data does not include
  /// a nul (0x00) byte.
  ///
  /// The caller is responsible for using a quality library (e.g.,
  /// ICU) to (a) normalize their Unicode data; and (b) generate a
  /// Unicode sort key from their Unicode data.  The sort key will
  /// impose specific collation ordering semantics as configured by
  /// the application (locale, collation strength, decomposition
  /// mode).
  ///
  /// The key_build accepts a view onto some sequence of bytes, which
  /// must not include a nul (0x00) byte.  The view will be truncated
  /// to at most #maxlen bytes.  If the data is less than #maxlen
  /// bytes, then a #pad byte is added and a run count to logically
  /// extend the text field in the key to #maxlen bytes. The
  /// truncation and padding keeps multi-field keys with embedded
  /// variable length text fields aligned such that the field
  /// following a variable length text field does not bleed into the
  /// lexiographic ordering of the variable length text field. It is
  /// not necessary to do this if the text is the only component in
  /// the key.  In that case, you can simply append the bytes using
  /// key_encoder::append().
  key_encoder &encode_text(std::span<const std::byte> text) {
    // truncate view to at most maxlen bytes.
    text = (text.size_bytes() > maxlen) ? text.subspan(maxlen) : text;
    // Note: Because the [pad] is 0x00, we do not need to strip off
    // trailing pad bytes in the [text] since 0x00 is disallowed.  If
    // the pad byte was 0x20 (space), then we WOULD need to strip off
    // any trailing space characters here by walking backwards over
    // the text and finding the first non-space character.  A failure
    // to do that when [pad] is a legal character would result in
    // "...0x20" not comparing as equals with "...".
    static_assert(static_cast<std::byte>(0) == pad);  // codifies assertion
    //
    // Ensure enough room for the text, the pad byte, and the
    // run-length encoding of the pad byte.
    ensure_available(text.size_bytes() + 1 + sizeof(maxlen));
    const auto padlen = text.size_bytes() - maxlen;
    append(text);                            // append bytes to the buffer.
    encode(static_cast<std::uint8_t>(pad));  // unsigned byte
    encode(padlen);  // logical run-length of the pad byte.
    return *this;
  }

  /// Append a sequence of unsigned bytes to the encoded key.
  ///
  /// Note: DO NOT use this method if you are attempting to add text
  /// to the key in any position other than the final component of the
  /// key. It will not Do The Right Thing (DTRT).
  ///
  /// @param data A sequence of bytes that will be appended to the
  /// key.
  //
  // TODO Look at how to handle std::string_view, which is defined in
  // terms of characters (CharT), not bytes.
  key_encoder &append(std::span<const std::byte> data) {
    const auto sz = data.size_bytes();
    ensure_available(sz);
    std::memcpy(buf + off, data.data(), sz);
    off += sz;
    return *this;
  }

 private:
  /// Ensure that we have at least the specified capacity in the
  /// buffer.
  void ensure_capacity(size_t min_capacity) {
    unodb::detail::ensure_capacity(buf, cap, off, min_capacity);
  }

  /// Used for the initial buffer.
  std::byte ibuf[detail::INITIAL_BUFFER_CAPACITY];

  /// The buffer to accmulate the encoded key.  Originally this is the
  /// [ibuf].  If that overflows, then something will be allocated.
  std::byte *buf{&ibuf[0]};

  /// The current buffer capacity
  size_t cap{sizeof(ibuf)};

  /// The number of bytes in the buffer having encoded data.
  size_t off{0};
};  // class key_encoder

/// A utility class that can decode binary comparable keys as long as
/// those keys (except for Unicode sort keys).  To use this class, you
/// need to know how a given key was encoded as a sequence of key
/// components.
class key_decoder {
 private:
  const std::byte *buf;  /// the data to be decoded
  const size_t cap;      /// #of bytes in that buffer.
  size_t off{0};         /// the byte offset into that data.

  // highest bit for various data types.
  static constexpr uint64_t msb8 = 1ULL << 7;
  static constexpr uint64_t msb16 = 1ULL << 15;
  static constexpr uint64_t msb32 = 1ULL << 31;
  static constexpr uint64_t msb64 = 1ULL << 63;

 public:
  /// Build a decoder for the key_view.
  explicit key_decoder(const key_view kv)
      : buf(kv.data()), cap(kv.size_bytes()) {}

  //
  // signed integers
  //

  /// Decode a component of the indicated type from the key.
  key_decoder &decode(std::int8_t &v) {
    const auto one = static_cast<std::uint8_t>(1);
    std::uint8_t u;
    decode(u);
    v = (u >= msb8) ? static_cast<int8_t>(u - msb8)
                    : -static_cast<int8_t>(msb8 - one - u) -
                          static_cast<std::int8_t>(1);
    return *this;
  }

  /// Decode a component of the indicated type from the key.
  key_decoder &decode(std::int16_t &v) {
    const auto one = static_cast<std::uint16_t>(1);
    std::uint16_t u;
    decode(u);
    v = (u >= msb16) ? static_cast<int16_t>(u - msb16)
                     : -static_cast<int16_t>(msb16 - one - u) -
                           static_cast<std::int16_t>(1);
    return *this;
  }

  /// Decode a component of the indicated type from the key.
  key_decoder &decode(std::int32_t &v) {
    const auto one = static_cast<std::uint32_t>(1);
    std::uint32_t u;
    decode(u);
    v = (u >= msb32) ? static_cast<int32_t>(u - msb32)
                     : -static_cast<int32_t>(msb32 - one - u) - 1;
    return *this;
  }

  /// Decode a component of the indicated type from the key.
  key_decoder &decode(std::int64_t &v) {
    const auto one = static_cast<std::uint64_t>(1);
    std::uint64_t u;
    decode(u);
    v = (u >= msb64) ? static_cast<int64_t>(u - msb64)
                     : -static_cast<int64_t>(msb64 - one - u) - 1LL;
    return *this;
  }

  // unsigned integers

  /// Decode a component of the indicated type from the key.
  key_decoder &decode(std::uint8_t &v) {
    v = reinterpret_cast<const std::uint8_t &>(buf[off++]);
    return *this;
  }

  /// Decode a component of the indicated type from the key.
  key_decoder &decode(std::uint16_t &v) {
    std::uint16_t u;
    std::memcpy(&u, buf + off, sizeof(u));
#ifdef UNODB_DETAIL_LITTLE_ENDIAN
    v = unodb::detail::bswap(u);
#else
    v = u;
#endif
    off += sizeof(u);
    return *this;
  }

  /// Decode a component of the indicated type from the key.
  key_decoder &decode(std::uint32_t &v) {
    std::uint32_t u;
    std::memcpy(&u, buf + off, sizeof(u));
#ifdef UNODB_DETAIL_LITTLE_ENDIAN
    v = unodb::detail::bswap(u);
#else
    v = u;
#endif
    off += sizeof(u);
    return *this;
  }

  /// Decode a component of the indicated type from the key.
  key_decoder &decode(std::uint64_t &v) {
    std::uint64_t u;
    std::memcpy(&u, buf + off, sizeof(u));
#ifdef UNODB_DETAIL_LITTLE_ENDIAN
    v = unodb::detail::bswap(u);
#else
    v = u;
#endif
    off += sizeof(u);
    return *this;
  }
};  // class key_decoder

/// An instance of this exception is thrown if there is an attempt to
/// insert a key which is a prefix of another key.  Applications using
/// variable length or composite keys SHOULD use the key_encoder to
/// avoid this problem.
///
/// TODO(thompsonbry) Create a subclass of runtime_error for unodb
/// specific runtime errors.  This is one case.  The other cases are
/// key too long and value too long.
#define UNODB_KEY_CONTRACT_VIOLATION() \
  throw new std::runtime_error(        \
      "Key contract violation: A key must not be a prefix of an existing key")

}  // namespace unodb

#endif  // UNODB_DETAIL_ART_COMMON_HPP
