// Copyright 2024-2025 UnoDB contributors

// Should be the first include
#include "global.hpp"  // IWYU pragma: keep

// IWYU pragma: no_include <string>

#include <algorithm>
#include <array>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <sstream>
#include <vector>

#include <gtest/gtest.h>

#include "art_common.hpp"
#include "art_internal.hpp"
#include "gtest_utils.hpp"

namespace {

/// Test suite for key encoding, decoding, and the lexicographic
/// ordering obtained from the encoded keys.
template <class Db>
class ARTKeyEncodeDecodeTest : public ::testing::Test {
 public:
  using Test::Test;
};

using unodb::detail::compare;

// exposes some protected methods and data to the tests.
class my_key_encoder : public unodb::key_encoder {
 public:
  my_key_encoder() = default;
  static constexpr size_t get_initial_capacity() {
    return unodb::detail::INITIAL_BUFFER_CAPACITY;
  }
  size_t capacity() { return key_encoder::capacity(); }
  size_t size_bytes() { return key_encoder::size_bytes(); }
  void ensure_available(size_t req) { key_encoder::ensure_available(req); }
};

constexpr auto INITIAL_CAPACITY = my_key_encoder::get_initial_capacity();

/// Test helper verifies that [ekey1] < [ekey2].
///
/// @param ekey1 An external key of some type.
///
/// @param ekey2 Another external key of the same type.
template <typename T>
void do_encode_decode_lt_test(const T ekey1, const T ekey2) {
  if constexpr (std::is_same_v<T, float> || std::is_same_v<T, double>) {
    // Note: floating point +0 and -0 compare as equal, so we do not
    // compare the keys for non-quality if one of the keys is zero.
    if (std::fpclassify(ekey1) != FP_ZERO) {
      EXPECT_NE(ekey1, ekey2);  // not the same ekey.
    }
  } else {
    EXPECT_NE(ekey1, ekey2);  // not the same ekey.
  }
  unodb::key_encoder enc1{};
  unodb::key_encoder enc2{};  // separate decoder (backed by different span).
  const auto ikey1 = enc1.encode(ekey1).get_key_view();  // into encoder buf!
  const auto ikey2 = enc2.encode(ekey2).get_key_view();  // into encoder buf!
  EXPECT_TRUE(compare(ikey1, ikey1) == 0);               // compare w/ self
  EXPECT_TRUE(compare(ikey2, ikey2) == 0);               // compare w/ self
  EXPECT_TRUE(compare(ikey1, ikey2) != 0);               // not the same ikey.
  // Check the core assertion for this test helper. The internal keys
  // (after encoding) obey the asserted ordering over the external
  // keys (before encoding).
  if (!(compare(ikey1, ikey2) < 0)) {
    std::stringstream ss1;
    std::stringstream ss2;
    unodb::detail::dump_key(ss1, ikey1);
    unodb::detail::dump_key(ss2, ikey2);
    FAIL() << "ikey1 < ikey2"
           << ": ekey1(" << ekey1 << ")[" << ss1.str() << "]"
           << ", ekey2(" << ekey2 << ")[" << ss2.str() << "]";
  } else {
    // Verify key2 > key1
    EXPECT_TRUE(compare(ikey2, ikey1) > 0);
    // Verify that we can round trip both values.
    unodb::key_decoder dec1{ikey1};
    unodb::key_decoder dec2{ikey2};
    T akey1;
    T akey2;
    dec1.decode(akey1);
    dec2.decode(akey2);
    EXPECT_EQ(ekey1, akey1);
    EXPECT_EQ(ekey2, akey2);
  }
}

UNODB_START_TESTS()

// basic memory management - initial buffer case.
TEST(ARTKeyEncodeDecodeTest, C00001) {
  my_key_encoder enc{};
  EXPECT_EQ(enc.capacity(), INITIAL_CAPACITY);
  EXPECT_EQ(enc.size_bytes(), 0);
  // ensure some space is available w/o change in encoder.
  enc.ensure_available(INITIAL_CAPACITY - 1);  // edge case
  EXPECT_EQ(enc.capacity(), INITIAL_CAPACITY);
  EXPECT_EQ(enc.size_bytes(), 0);
  // ensure some space is available w/o change in encoder.
  enc.ensure_available(INITIAL_CAPACITY);  // edge case
  EXPECT_EQ(enc.capacity(), INITIAL_CAPACITY);
  EXPECT_EQ(enc.size_bytes(), 0);
  // reset -- nothing changes.
  enc.reset();
  EXPECT_EQ(enc.capacity(), INITIAL_CAPACITY);
  EXPECT_EQ(enc.size_bytes(), 0);
  // key_view is empty
  auto kv = enc.get_key_view();
  EXPECT_EQ(kv.size_bytes(), 0);
}

// basic memory management -- buffer extension case.
TEST(ARTKeyEncodeDecodeTest, C00002) {
  my_key_encoder enc{};
  EXPECT_EQ(enc.capacity(), INITIAL_CAPACITY);
  EXPECT_EQ(enc.size_bytes(), 0);
  // ensure some space is available w/o change in encoder.
  enc.ensure_available(INITIAL_CAPACITY + 1);       // edge case.
  EXPECT_EQ(enc.capacity(), INITIAL_CAPACITY * 2);  // assumes power of two
  EXPECT_EQ(enc.size_bytes(), 0);
  EXPECT_EQ(enc.get_key_view().size_bytes(), 0);  // key_view is empty
  // reset.
  enc.reset();
  EXPECT_EQ(enc.capacity(), INITIAL_CAPACITY * 2);  // unchanged
  EXPECT_EQ(enc.size_bytes(), 0);                   // reset
  EXPECT_EQ(enc.get_key_view().size_bytes(), 0);    // key_view is empty
}

// Encode/decode round trip test.
template <typename T>
void do_encode_decode_test(const T ekey) {
  my_key_encoder enc{};
  enc.encode(ekey);
  const unodb::key_view kv = enc.get_key_view();  // encode
  EXPECT_EQ(kv.size_bytes(), sizeof(ekey));       // check size
  // decode check
  unodb::key_decoder dec{kv};
  T akey;
  dec.decode(akey);
  EXPECT_EQ(akey, ekey);
}

// Encode/decode round trip test which also verifies the encoded byte sequence.
template <typename T>
void do_encode_decode_test(const T ekey,
                           const std::array<const std::byte, sizeof(T)> ikey) {
  my_key_encoder enc{};
  enc.encode(ekey);
  const unodb::key_view kv = enc.get_key_view();  // encode
  EXPECT_EQ(kv.size_bytes(), sizeof(ekey));       // check size
  // check order.
  size_t i = 0;
  for (const auto byte : ikey) {
    EXPECT_EQ(byte, kv[i++]);
  }
  // decode check
  unodb::key_decoder dec{kv};
  T akey;
  dec.decode(akey);
  EXPECT_EQ(akey, ekey);
}

TEST(ARTKeyEncodeDecodeTest, UInt8C00010) {
  using T = std::uint8_t;
  constexpr auto one = static_cast<T>(1);
  // Check the encoder byte order.
  constexpr std::array<const std::byte, sizeof(T)> ikey{
      static_cast<std::byte>(0x01)};
  do_encode_decode_test(static_cast<T>(0x01ULL), ikey);
  // round-trip tests.
  do_encode_decode_test(static_cast<T>(0));
  do_encode_decode_test(static_cast<T>(0 + 1));
  do_encode_decode_test(static_cast<T>(0 - 1));
  do_encode_decode_test(std::numeric_limits<T>::min());
  do_encode_decode_test(std::numeric_limits<T>::max());
  do_encode_decode_test(std::numeric_limits<T>::min() + one);
  do_encode_decode_test(std::numeric_limits<T>::max() - one);
  // check lexicographic ordering for std::uint8_t pairs.
  do_encode_decode_lt_test(static_cast<T>(0x01ULL), static_cast<T>(0x09ULL));
  do_encode_decode_lt_test(static_cast<T>(0), static_cast<T>(1));
  do_encode_decode_lt_test(static_cast<T>(0x7FULL), static_cast<T>(0x80ULL));
  do_encode_decode_lt_test(static_cast<T>(0xFEULL), static_cast<T>(~0ULL));
}

TEST(ARTKeyEncodeDecodeTest, Int8C00010) {
  using T = std::int8_t;
  constexpr auto one = static_cast<T>(1);
  // Check the encoder byte order.
  constexpr std::array<const std::byte, sizeof(T)> ikey{
      static_cast<std::byte>(0x81)};
  do_encode_decode_test(static_cast<T>(0x01LL), ikey);
  // round-trip tests.
  do_encode_decode_test(static_cast<T>(0));
  do_encode_decode_test(static_cast<T>(0 + 1));
  do_encode_decode_test(static_cast<T>(0 - 1));
  do_encode_decode_test(std::numeric_limits<T>::min());
  do_encode_decode_test(std::numeric_limits<T>::max());
  do_encode_decode_test(std::numeric_limits<T>::min() + one);
  do_encode_decode_test(std::numeric_limits<T>::max() - one);
  // check lexicographic ordering for std::uint8_t pairs.
  do_encode_decode_lt_test(static_cast<T>(0), static_cast<T>(1));
  do_encode_decode_lt_test(static_cast<T>(5), static_cast<T>(7));
  do_encode_decode_lt_test(std::numeric_limits<T>::min(),
                           static_cast<T>(std::numeric_limits<T>::min() + one));
  do_encode_decode_lt_test(static_cast<T>(std::numeric_limits<T>::max() - one),
                           std::numeric_limits<T>::max());
}

TEST(ARTKeyEncodeDecodeTest, UInt16C00010) {
  using T = std::uint16_t;
  constexpr auto one = static_cast<T>(1);
  // Check the encoder byte order.
  constexpr std::array<const std::byte, sizeof(T)> ikey{
      static_cast<std::byte>(0x01), static_cast<std::byte>(0x02)};
  do_encode_decode_test(static_cast<T>(0x0102ULL), ikey);
  // round-trip tests.
  do_encode_decode_test(static_cast<T>(0));
  do_encode_decode_test(static_cast<T>(0 + 1));
  do_encode_decode_test(static_cast<T>(0 - 1));
  do_encode_decode_test(std::numeric_limits<T>::min());
  do_encode_decode_test(std::numeric_limits<T>::max());
  do_encode_decode_test(std::numeric_limits<T>::min() + one);
  do_encode_decode_test(std::numeric_limits<T>::max() - one);
  // check lexicographic ordering for std::uint16_t pairs.
  do_encode_decode_lt_test(static_cast<T>(0x0102ULL),
                           static_cast<T>(0x090AULL));
  do_encode_decode_lt_test(static_cast<T>(0), static_cast<T>(1));
  do_encode_decode_lt_test(static_cast<T>(0x7FFFULL),
                           static_cast<T>(0x8000ULL));
  do_encode_decode_lt_test(static_cast<T>(0xFFFEULL), static_cast<T>(~0ULL));
}

TEST(ARTKeyEncodeDecodeTest, Int16C00010) {
  using T = std::int16_t;
  constexpr auto one = static_cast<T>(1);
  // Check the encoder byte order.
  constexpr std::array<const std::byte, sizeof(T)> ikey{
      static_cast<std::byte>(0x81), static_cast<std::byte>(0x02)};
  do_encode_decode_test(static_cast<T>(0x0102LL), ikey);
  // round-trip tests.
  do_encode_decode_test(static_cast<T>(0));
  do_encode_decode_test(static_cast<T>(0 + 1));
  do_encode_decode_test(static_cast<T>(0 - 1));
  do_encode_decode_test(std::numeric_limits<T>::min());
  do_encode_decode_test(std::numeric_limits<T>::max());
  do_encode_decode_test(std::numeric_limits<T>::min() + one);
  do_encode_decode_test(std::numeric_limits<T>::max() - one);
  // check lexicographic ordering for std::uint16_t pairs.
  do_encode_decode_lt_test(static_cast<T>(0), static_cast<T>(1));
  do_encode_decode_lt_test(static_cast<T>(5), static_cast<T>(7));
  do_encode_decode_lt_test(std::numeric_limits<T>::min(),
                           static_cast<T>(std::numeric_limits<T>::min() + one));
  do_encode_decode_lt_test(static_cast<T>(std::numeric_limits<T>::max() - one),
                           std::numeric_limits<T>::max());
}

TEST(ARTKeyEncodeDecodeTest, Uint32C00010) {
  using T = std::uint32_t;
  constexpr auto one = static_cast<T>(1);
  // Check the encoder byte order.
  constexpr std::array<const std::byte, sizeof(T)> ikey{
      static_cast<std::byte>(0x01), static_cast<std::byte>(0x02),
      static_cast<std::byte>(0x03), static_cast<std::byte>(0x04)};
  do_encode_decode_test(static_cast<T>(0x01020304), ikey);
  // round-trip tests.
  do_encode_decode_test(static_cast<T>(0));
  do_encode_decode_test(static_cast<T>(0 + 1));
  do_encode_decode_test(static_cast<T>(0 - 1));
  do_encode_decode_test(std::numeric_limits<T>::min());
  do_encode_decode_test(std::numeric_limits<T>::max());
  do_encode_decode_test(std::numeric_limits<T>::min() + one);
  do_encode_decode_test(std::numeric_limits<T>::max() - one);
  // check lexicographic ordering for std::uint32_t pairs.
  do_encode_decode_lt_test(static_cast<T>(0x01020304ULL),
                           static_cast<T>(0x090A0B0CULL));
  do_encode_decode_lt_test(static_cast<T>(0), static_cast<T>(1));
  do_encode_decode_lt_test(static_cast<T>(0x7FFFFFFFULL),
                           static_cast<T>(0x80000000ULL));
  do_encode_decode_lt_test(static_cast<T>(0xFFFFFFFEULL),
                           static_cast<T>(~0ULL));
}

TEST(ARTKeyEncodeDecodeTest, Int32C00010) {
  using T = std::int32_t;
  constexpr auto one = 1;  // useless cast:: static_cast<T>(1);
  // Check the encoder byte order.
  constexpr std::array<const std::byte, sizeof(T)> ikey{
      static_cast<std::byte>(0x81), static_cast<std::byte>(0x02),
      static_cast<std::byte>(0x03), static_cast<std::byte>(0x04)};
  do_encode_decode_test(static_cast<T>(0x01020304LL), ikey);
  // round-trip tests.
  //
  // Note: 0, 1, ~0, etc. are already std::int32_t.  If that is not
  // true universally, then we need conditional compilation here to
  // avoid "warning useless cast" errors in the compiler.
  do_encode_decode_test(0);
  do_encode_decode_test(0 + 1);
  do_encode_decode_test(0 - 1);
  do_encode_decode_test(std::numeric_limits<T>::min());
  do_encode_decode_test(std::numeric_limits<T>::min() + one);
  do_encode_decode_test(std::numeric_limits<T>::max());
  do_encode_decode_test(std::numeric_limits<T>::max() - one);
  // check lexicographic ordering for std::uint32_t pairs.
  do_encode_decode_lt_test(0, 1);
  do_encode_decode_lt_test(5, 7);
  do_encode_decode_lt_test(std::numeric_limits<T>::min(),
                           std::numeric_limits<T>::min() + one);
  do_encode_decode_lt_test(std::numeric_limits<T>::max() - one,
                           std::numeric_limits<T>::max());
}

TEST(ARTKeyEncodeDecodeTest, UInt64C00010) {
  using T = std::uint64_t;
  constexpr auto one = static_cast<T>(1);
  // Check the encoder byte order.
  constexpr std::array<const std::byte, sizeof(T)> ikey{
      static_cast<std::byte>(0x01), static_cast<std::byte>(0x02),
      static_cast<std::byte>(0x03), static_cast<std::byte>(0x04),
      static_cast<std::byte>(0x05), static_cast<std::byte>(0x06),
      static_cast<std::byte>(0x07), static_cast<std::byte>(0x08)};
  do_encode_decode_test(static_cast<T>(0x0102030405060708), ikey);
  // round-trip tests.
  do_encode_decode_test(static_cast<T>(0));
  do_encode_decode_test(static_cast<T>(0 + 1));
  do_encode_decode_test(static_cast<T>(0 - 1));
  do_encode_decode_test(std::numeric_limits<T>::min());
  do_encode_decode_test(std::numeric_limits<T>::max());
  do_encode_decode_test(std::numeric_limits<T>::min() + one);
  do_encode_decode_test(std::numeric_limits<T>::max() - one);
  // check lexicographic ordering for std::uint64_t pairs.
  do_encode_decode_lt_test<T>(0x0102030405060708ULL, 0x090A0B0C0D0F1011ULL);
  do_encode_decode_lt_test(static_cast<T>(0), static_cast<T>(1));
  do_encode_decode_lt_test<T>(0x7FFFFFFFFFFFFFFFULL, 0x8000000000000000ULL);
  do_encode_decode_lt_test<T>(0xFFFFFFFFFFFFFFFEULL, static_cast<T>(~0ULL));
}

TEST(ARTKeyEncodeDecodeTest, Int64C00010) {
  using T = std::int64_t;
  constexpr auto one = static_cast<T>(1);
  // Check the encoder byte order.
  constexpr std::array<const std::byte, sizeof(T)> ikey{
      static_cast<std::byte>(0x81), static_cast<std::byte>(0x02),
      static_cast<std::byte>(0x03), static_cast<std::byte>(0x04),
      static_cast<std::byte>(0x05), static_cast<std::byte>(0x06),
      static_cast<std::byte>(0x07), static_cast<std::byte>(0x08)};
  do_encode_decode_test<T>(0x0102030405060708LL, ikey);
  // round-trip tests.
  do_encode_decode_test(static_cast<T>(0));
  do_encode_decode_test(static_cast<T>(0 + 1));
  do_encode_decode_test(static_cast<T>(0 - 1));
  do_encode_decode_test(std::numeric_limits<T>::min());
  do_encode_decode_test(std::numeric_limits<T>::max());
  do_encode_decode_test(std::numeric_limits<T>::min() + one);
  do_encode_decode_test(std::numeric_limits<T>::max() - one);
  // check lexicographic ordering for std::uint64_t pairs.
  do_encode_decode_lt_test(static_cast<T>(0), static_cast<T>(1));
  do_encode_decode_lt_test(static_cast<T>(5), static_cast<T>(7));
  do_encode_decode_lt_test(std::numeric_limits<T>::min(),
                           std::numeric_limits<T>::min() + one);
  do_encode_decode_lt_test(std::numeric_limits<T>::max() - one,
                           std::numeric_limits<T>::max());
}

//
// Append span<const::byte> (aka unodb::key_view).
//

void do_encode_bytes_test(std::span<const std::byte> a) {
  my_key_encoder enc;
  const auto sz = a.size();
  enc.append(a);
  const auto cmp = std::memcmp(enc.get_key_view().data(), a.data(), sz);
  EXPECT_EQ(0, cmp);
  EXPECT_EQ(sz, enc.size_bytes());
}

/// Unit test look at the simple case of appending a sequence of bytes
/// to the key_encoder.
TEST(ARTKeyEncodeDecodeTest, AppendSpanConstByteC0001) {
  constexpr auto test_data_0 = std::array<const std::byte, 3>{
      std::byte{0x02}, std::byte{0x05}, std::byte{0x05}};
  constexpr auto test_data_1 = std::array<const std::byte, 3>{
      std::byte{0x03}, std::byte{0x00}, std::byte{0x05}};
  constexpr auto test_data_2 = std::array<const std::byte, 3>{
      std::byte{0x03}, std::byte{0x00}, std::byte{0x10}};
  constexpr auto test_data_3 = std::array<const std::byte, 3>{
      std::byte{0x03}, std::byte{0x05}, std::byte{0x05}};
  constexpr auto test_data_4 = std::array<const std::byte, 3>{
      std::byte{0x03}, std::byte{0x05}, std::byte{0x10}};
  constexpr auto test_data_5 = std::array<const std::byte, 3>{
      std::byte{0x03}, std::byte{0x10}, std::byte{0x05}};
  constexpr auto test_data_6 = std::array<const std::byte, 3>{
      std::byte{0x04}, std::byte{0x05}, std::byte{0x10}};
  constexpr auto test_data_7 = std::array<const std::byte, 3>{
      std::byte{0x04}, std::byte{0x10}, std::byte{0x05}};

  do_encode_bytes_test(std::span<const std::byte>(test_data_0));
  do_encode_bytes_test(std::span<const std::byte>(test_data_1));
  do_encode_bytes_test(std::span<const std::byte>(test_data_2));
  do_encode_bytes_test(std::span<const std::byte>(test_data_3));
  do_encode_bytes_test(std::span<const std::byte>(test_data_4));
  do_encode_bytes_test(std::span<const std::byte>(test_data_5));
  do_encode_bytes_test(std::span<const std::byte>(test_data_6));
  do_encode_bytes_test(std::span<const std::byte>(test_data_7));
}

//
// float & double tests.
//

/// Can be used for anything (handles NaN as a special case).
void do_encode_decode_float_test(const float expected) {
  using U = std::uint32_t;
  using F = float;
  // encode
  unodb::key_encoder enc;
  enc.reset().encode(expected);
  // Check decode as float (round trip).
  F actual;
  {
    unodb::key_decoder dec{enc.get_key_view()};
    dec.decode(actual);
  }
  if (std::isnan(expected)) {
    // Verify canonical NaN.
    EXPECT_TRUE(std::isnan(actual));
    U u;
    unodb::key_decoder dec{enc.get_key_view()};
    dec.decode(u);
  } else {
    EXPECT_EQ(actual, expected);
  }
}

/// Test encode/decode of various floating point values.
TEST(ARTKeyEncodeDecodeTest, FloatC0001) {
  using F = float;
  constexpr auto pzero = 0.f;
  constexpr auto nzero = -0.f;
  static_assert(std::signbit(pzero) == 0);
  static_assert(std::signbit(nzero) == 1);
  do_encode_decode_float_test(pzero);
  do_encode_decode_float_test(nzero);
  do_encode_decode_float_test(10.001F);
  do_encode_decode_float_test(-10.001F);
  do_encode_decode_float_test(std::numeric_limits<F>::min());
  do_encode_decode_float_test(std::numeric_limits<F>::lowest());
  do_encode_decode_float_test(std::numeric_limits<F>::max());
  do_encode_decode_float_test(std::numeric_limits<F>::epsilon());
  do_encode_decode_float_test(std::numeric_limits<F>::denorm_min());
}

/// inf
TEST(ARTKeyEncodeDecodeTest, FloatC0002Infinity) {
  using F = float;
  using U = std::uint32_t;
  constexpr auto inf = std::numeric_limits<F>::infinity();
  EXPECT_EQ(reinterpret_cast<const U&>(inf), 0x7f800000U);
  do_encode_decode_float_test(inf);
}

/// -inf
TEST(ARTKeyEncodeDecodeTest, FloatC0003NegInfinity) {
  using F = float;
  using U = std::uint32_t;
  constexpr auto ninf = -std::numeric_limits<F>::infinity();
  static_assert(sizeof(ninf) == sizeof(float));
  static_assert(std::numeric_limits<float>::is_iec559, "IEEE 754 required");
  static_assert(ninf < std::numeric_limits<float>::lowest());
  static_assert(std::isinf(ninf));
  static_assert(!std::isnan(ninf));
  EXPECT_EQ(reinterpret_cast<const U&>(ninf), 0xff800000U);
  do_encode_decode_float_test(ninf);
}

/// quiet_NaN
TEST(ARTKeyEncodeDecodeTest, FloatC0004QuietNaN) {
  using F = float;
  constexpr F f{std::numeric_limits<F>::quiet_NaN()};
  EXPECT_TRUE(std::isnan(f));
  do_encode_decode_float_test(f);
}

/// signaling_NaN
TEST(ARTKeyEncodeDecodeTest, FloatC0005SignalingNan) {
  using F = float;
  constexpr F f{std::numeric_limits<F>::signaling_NaN()};
  EXPECT_TRUE(std::isnan(f));
  do_encode_decode_float_test(f);
}

/// NaN can be formed for any floating point value using std::nanf().
TEST(ARTKeyEncodeDecodeTest, FloatC0006NumericNaN) {
  do_encode_decode_float_test(std::nanf("-1"));
  do_encode_decode_float_test(std::nanf("1"));
  do_encode_decode_float_test(std::nanf("100.1"));
  do_encode_decode_float_test(std::nanf("-100.1"));
}

/// Verify the ordering over various floating point pairs.
TEST(ARTKeyEncodeDecodeTest, FloatC0007Order) {
  using F = float;
  constexpr auto pzero = 0.f;
  constexpr auto nzero = -0.f;
  static_assert(std::signbit(pzero) == 0);
  static_assert(std::signbit(nzero) == 1);
  constexpr auto minf = std::numeric_limits<F>::min();
  constexpr auto maxf = std::numeric_limits<F>::max();
  constexpr auto inf = std::numeric_limits<F>::infinity();
  constexpr auto ninf = -std::numeric_limits<F>::infinity();
  constexpr auto lowest = std::numeric_limits<F>::lowest();
  do_encode_decode_lt_test(-10.01F, -1.01F);
  do_encode_decode_lt_test(-1.F, pzero);
  do_encode_decode_lt_test(nzero, pzero);
  do_encode_decode_lt_test(pzero, 1.0F);
  do_encode_decode_lt_test(1.01F, 10.01F);
  do_encode_decode_lt_test(ninf, lowest);
  do_encode_decode_lt_test(0.F, minf);
  do_encode_decode_lt_test(maxf, inf);
}

/// Can be used for anything (handles NaN as a special case).
void do_encode_decode_double_test(const double expected) {
  using U = std::uint64_t;
  using F = double;
  // encode
  unodb::key_encoder enc;
  enc.reset().encode(expected);
  // Check decode as double (round trip).
  F actual;
  {
    unodb::key_decoder dec{enc.get_key_view()};
    dec.decode(actual);
  }
  if (std::isnan(expected)) {
    // Verify canonical NaN.
    EXPECT_TRUE(std::isnan(actual));
    U u;
    unodb::key_decoder dec{enc.get_key_view()};
    dec.decode(u);
  } else {
    EXPECT_EQ(actual, expected);
  }
}

/// Test encode/decode of various double precisions floating point
/// values.
TEST(ARTKeyEncodeDecodeTest, DoubleC0001) {
  using F = double;
  constexpr auto pzero = 0.f;
  constexpr auto nzero = -0.f;
  static_assert(std::signbit(pzero) == 0);
  static_assert(std::signbit(nzero) == 1);
  do_encode_decode_float_test(pzero);
  do_encode_decode_float_test(nzero);
  do_encode_decode_double_test(10.001);
  do_encode_decode_double_test(-10.001);
  do_encode_decode_double_test(std::numeric_limits<F>::min());
  do_encode_decode_double_test(std::numeric_limits<F>::lowest());
  do_encode_decode_double_test(std::numeric_limits<F>::max());
  do_encode_decode_double_test(std::numeric_limits<F>::epsilon());
  do_encode_decode_double_test(std::numeric_limits<F>::denorm_min());
}

/// inf
TEST(ARTKeyEncodeDecodeTest, DoubleC0002Infinity) {
  using F = double;
  using U = std::uint64_t;
  constexpr auto inf = std::numeric_limits<F>::infinity();
  EXPECT_EQ(reinterpret_cast<const U&>(inf), 0x7ff0000000000000ULL);
  do_encode_decode_double_test(inf);
}

/// -inf
TEST(ARTKeyEncodeDecodeTest, DoubleC0003NegInfinity) {
  using F = double;
  using U = std::uint64_t;
  constexpr auto ninf = -std::numeric_limits<F>::infinity();
  static_assert(sizeof(ninf) == sizeof(double));
  static_assert(std::numeric_limits<double>::is_iec559, "IEEE 754 required");
  static_assert(ninf < std::numeric_limits<double>::lowest());
  static_assert(std::isinf(ninf));
  static_assert(!std::isnan(ninf));
  EXPECT_EQ(reinterpret_cast<const U&>(ninf), 0xfff0000000000000ULL);
  do_encode_decode_double_test(ninf);
}

/// quiet_NaN
TEST(ARTKeyEncodeDecodeTest, DoubleC0004QuietNaN) {
  using F = double;
  constexpr F f{std::numeric_limits<F>::quiet_NaN()};
  EXPECT_TRUE(std::isnan(f));
  do_encode_decode_double_test(f);
}

/// signaling_NaN
TEST(ARTKeyEncodeDecodeTest, DoubleC0005SignalingNan) {
  using F = double;
  constexpr F f{std::numeric_limits<F>::signaling_NaN()};
  EXPECT_TRUE(std::isnan(f));
  do_encode_decode_double_test(f);
}

/// NaN can be formed for any double precision floating point value
/// using std::nanf().
TEST(ARTKeyEncodeDecodeTest, DoubleC0006NumericNaN) {
  do_encode_decode_double_test(std::nan("-1"));
  do_encode_decode_double_test(std::nan("1"));
  do_encode_decode_double_test(std::nan("100.1"));
  do_encode_decode_double_test(std::nan("-100.1"));
}

/// Verify the ordering over various double precision floating point
/// pairs.
TEST(ARTKeyEncodeDecodeTest, DoubleC0007Order) {
  using F = double;
  constexpr auto pzero = 0.;
  constexpr auto nzero = -0.;
  static_assert(std::signbit(pzero) == 0);
  static_assert(std::signbit(nzero) == 1);
  constexpr auto minf = std::numeric_limits<F>::min();
  constexpr auto maxf = std::numeric_limits<F>::max();
  constexpr auto inf = std::numeric_limits<F>::infinity();
  constexpr auto ninf = -std::numeric_limits<F>::infinity();
  constexpr auto lowest = std::numeric_limits<F>::lowest();
  do_encode_decode_lt_test(-10.01, -1.01);
  do_encode_decode_lt_test(-1., pzero);
  do_encode_decode_lt_test(nzero, pzero);
  do_encode_decode_lt_test(pzero, 1.0);
  do_encode_decode_lt_test(1.01, 10.01);
  do_encode_decode_lt_test(ninf, lowest);
  do_encode_decode_lt_test(0., minf);
  do_encode_decode_lt_test(maxf, inf);
}

//
// append "C" string
//

void do_encode_cstring_test(const char* a) {
  my_key_encoder enc;
  const auto sz = strlen(a);
  enc.append(a);
  const auto cmp = std::memcmp(enc.get_key_view().data(), a, sz);
  EXPECT_EQ(0, cmp);
  EXPECT_EQ(sz, enc.size_bytes());
}

TEST(ARTKeyEncodeDecodeTest, AppendCStringC0001) {
  do_encode_cstring_test("abc");
  do_encode_cstring_test("def");
  do_encode_cstring_test("gadzooks");
  do_encode_cstring_test("banana");
  do_encode_cstring_test("");
}

//
// Encoding of text fields (optionaly truncated to maxlen and padded
// out to maxlen via run length encoding).
//

// Helper class to hold copies of key_views from a key_encoder.  We
// need to make copies because the key_view is backed by the data in
// the encoder. So we copy the data out into a new allocation and
// return a key_view backed by that allocation. The set of those
// allocations is held by this factory object and they go out of scope
// together.
class key_factory {
 public:
  /// Used to retain arrays backing unodb::key_views.
  std::vector<std::vector<std::byte>> key_views{};

  /// Copy the data from the encoder into a new entry in #key_views.
  unodb::key_view make_key_view(unodb::key_encoder& enc) {
    auto kv{enc.get_key_view()};
    const auto sz{kv.size()};
    key_views.emplace_back(std::vector<std::byte>(sz));
    auto& a = key_views.back();  // a *reference* to data emplaced_back.
    std::copy(kv.data(), kv.data() + sz, a.begin());  // copy data to inner vec
    return unodb::key_view(a.data(), sz);  // view of inner vec's data.
  }
};

void do_simple_pad_test(unodb::key_encoder& enc, const char* s) {
  using ST = unodb::key_encoder::size_type;
  const auto len = strlen(s);                         // text length.
  const auto sz = (len > unodb::key_encoder::maxlen)  // truncated len.
                      ? unodb::key_encoder::maxlen
                      : len;
  const auto kv = enc.reset().encode_text(s).get_key_view();
  // Check expected resulting key length.
  EXPECT_EQ(kv.size(), sz + sizeof(unodb::key_encoder::pad) + sizeof(ST))
      << "text(" << sz << ")[" << (sz < 100 ? s : "...") << "]";
  // Verify that the first N bytes are the same as the given text.
  EXPECT_EQ(std::memcmp(s, kv.data(), sz), 0)
      << "text(" << sz << ")[" << (sz < 100 ? s : "...") << "]";
  // Check for the pad byte.
  EXPECT_EQ(kv[sz], unodb::key_encoder::pad)
      << "text(" << sz << ")[" << (sz < 100 ? s : "...") << "]";
  // Check the pad length.
  const ST padlen{static_cast<ST>(unodb::key_encoder::maxlen - sz)};
  ST tmp;
  memcpy(&tmp, kv.data() + sz + 1, sizeof(ST));  // copy out pad length.
  const ST tmp2 = unodb::detail::bswap(tmp);     // decode.
  EXPECT_EQ(tmp2, padlen) << "text(" << sz << ")[" << (sz < 100 ? s : "...")
                          << "]";
}

/// Helper generates a large string and feeds it into
/// do_simple_pad_test().
void do_pad_test_large_string(unodb::key_encoder& enc, size_t nbytes,
                              bool expect_truncation = false) {
  std::unique_ptr<void, decltype(std::free)*> ptr{malloc(nbytes), std::free};
  auto p{reinterpret_cast<char*>(ptr.get())};
  std::memset(p, 'a', nbytes);  // fill with some char.
  // for( size_t i = 0; i < nbytes; i++ ) {
  //   p[ i ] = ( 'a' + (i % 16) );
  // }
  do_simple_pad_test(enc, p);
  if (expect_truncation) {
    auto kv = enc.get_key_view();
    const size_t max_key_size = unodb::key_encoder::maxlen +
                                sizeof(unodb::key_encoder::pad) +
                                sizeof(unodb::key_encoder::size_type);
    EXPECT_EQ(kv.size(), max_key_size);
  }
}

/// Verify proper padding to maxlen.
TEST(ARTKeyEncodeDecodeTest, EncodeTextC0001) {
  unodb::key_encoder enc;
  do_simple_pad_test(enc, "");
  do_simple_pad_test(enc, "abc");
  do_simple_pad_test(enc, "brown");
  do_simple_pad_test(enc, "banana");
}

/// Unit test variant examines truncation for a key whose length is
/// maxlen - 1.
TEST(ARTKeyEncodeDecodeTest, EncodeTextC0002) {
  unodb::key_encoder enc;
  do_pad_test_large_string(enc, unodb::key_encoder::maxlen - 1);
}

/// Unit test variant examines truncation for a key whose length is
/// exactly maxlen.
TEST(ARTKeyEncodeDecodeTest, EncodeTextC0003) {
  unodb::key_encoder enc;
  do_pad_test_large_string(enc, unodb::key_encoder::maxlen);
}

/// Unit test where the key is truncated.
TEST(ARTKeyEncodeDecodeTest, EncodeTextC0004) {
  unodb::key_encoder enc;
  do_pad_test_large_string(enc, unodb::key_encoder::maxlen + 1, true);
}

/// Unit test where the key is truncated.
TEST(ARTKeyEncodeDecodeTest, EncodeTextC0005) {
  unodb::key_encoder enc;
  do_pad_test_large_string(enc, unodb::key_encoder::maxlen + 2, true);
}

/// Verify the lexicographic sort order obtained for {bro, brown,
/// break, bre}, including verifying that the pad byte causes a prefix
/// such as "bro" to sort before a term which extends that prefix,
/// such as "brown".
TEST(ARTKeyEncodeDecodeTest, DISABLED_EncodeTextC0020) {
  key_factory fac;
  unodb::key_encoder enc;
  fac.make_key_view(enc.reset().encode_text("brown"));
  fac.make_key_view(enc.reset().encode_text("bro"));
  fac.make_key_view(enc.reset().encode_text("break"));
  fac.make_key_view(enc.reset().encode_text("bre"));
  std::sort(fac.key_views.begin(), fac.key_views.end());
  EXPECT_TRUE(strcmp("bro", reinterpret_cast<const char*>(
                                fac.key_views[0].data())) == 0);
  EXPECT_TRUE(strcmp("brown", reinterpret_cast<const char*>(
                                  fac.key_views[1].data())) == 0);
  EXPECT_TRUE(strcmp("bre", reinterpret_cast<const char*>(
                                fac.key_views[2].data())) == 0);
  EXPECT_TRUE(strcmp("break", reinterpret_cast<const char*>(
                                  fac.key_views[3].data())) == 0);
}

// TODO(thompsonbry) variable length keys - multi-field tests.

UNODB_END_TESTS()

}  // namespace
