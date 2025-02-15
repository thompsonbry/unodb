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

// Test helper verifies that [ekey1] < [ekey2].
template <typename T>
void do_encode_decode_order_test(const T ekey1, const T ekey2) {
  unodb::key_encoder enc1{};
  unodb::key_encoder enc2{};  // separate decoder (backed by different span).
  const auto ikey1 = enc1.encode(ekey1).get_key_view();  // into encoder buf!
  const auto ikey2 = enc2.encode(ekey2).get_key_view();  // into encoder buf!
  EXPECT_EQ(compare(ikey1, ikey1), 0);
  EXPECT_EQ(compare(ikey2, ikey2), 0);
  EXPECT_NE(compare(ikey1, ikey2), 0);
  EXPECT_LT(compare(ikey1, ikey2), 0);
  EXPECT_GT(compare(ikey2, ikey1), 0);
  unodb::key_decoder dec1{ikey1};
  unodb::key_decoder dec2{ikey2};
  T akey1;
  T akey2;
  dec1.decode(akey1);
  dec2.decode(akey2);
  EXPECT_EQ(ekey1, akey1);
  EXPECT_EQ(ekey2, akey2);
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
  do_encode_decode_order_test(static_cast<T>(0x01ULL), static_cast<T>(0x09ULL));
  do_encode_decode_order_test(static_cast<T>(0), static_cast<T>(1));
  do_encode_decode_order_test(static_cast<T>(0x7FULL), static_cast<T>(0x80ULL));
  do_encode_decode_order_test(static_cast<T>(0xFEULL), static_cast<T>(~0ULL));
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
  do_encode_decode_order_test(static_cast<T>(0), static_cast<T>(1));
  do_encode_decode_order_test(static_cast<T>(5), static_cast<T>(7));
  do_encode_decode_order_test(
      std::numeric_limits<T>::min(),
      static_cast<T>(std::numeric_limits<T>::min() + one));
  do_encode_decode_order_test(
      static_cast<T>(std::numeric_limits<T>::max() - one),
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
  do_encode_decode_order_test(static_cast<T>(0x0102ULL),
                              static_cast<T>(0x090AULL));
  do_encode_decode_order_test(static_cast<T>(0), static_cast<T>(1));
  do_encode_decode_order_test(static_cast<T>(0x7FFFULL),
                              static_cast<T>(0x8000ULL));
  do_encode_decode_order_test(static_cast<T>(0xFFFEULL), static_cast<T>(~0ULL));
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
  do_encode_decode_order_test(static_cast<T>(0), static_cast<T>(1));
  do_encode_decode_order_test(static_cast<T>(5), static_cast<T>(7));
  do_encode_decode_order_test(
      std::numeric_limits<T>::min(),
      static_cast<T>(std::numeric_limits<T>::min() + one));
  do_encode_decode_order_test(
      static_cast<T>(std::numeric_limits<T>::max() - one),
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
  do_encode_decode_order_test(static_cast<T>(0x01020304ULL),
                              static_cast<T>(0x090A0B0CULL));
  do_encode_decode_order_test(static_cast<T>(0), static_cast<T>(1));
  do_encode_decode_order_test(static_cast<T>(0x7FFFFFFFULL),
                              static_cast<T>(0x80000000ULL));
  do_encode_decode_order_test(static_cast<T>(0xFFFFFFFEULL),
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
  do_encode_decode_order_test(0, 1);
  do_encode_decode_order_test(5, 7);
  do_encode_decode_order_test(std::numeric_limits<T>::min(),
                              std::numeric_limits<T>::min() + one);
  do_encode_decode_order_test(std::numeric_limits<T>::max() - one,
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
  do_encode_decode_order_test<T>(0x0102030405060708ULL, 0x090A0B0C0D0F1011ULL);
  do_encode_decode_order_test(static_cast<T>(0), static_cast<T>(1));
  do_encode_decode_order_test<T>(0x7FFFFFFFFFFFFFFFULL, 0x8000000000000000ULL);
  do_encode_decode_order_test<T>(0xFFFFFFFFFFFFFFFEULL, static_cast<T>(~0ULL));
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
  do_encode_decode_order_test(static_cast<T>(0), static_cast<T>(1));
  do_encode_decode_order_test(static_cast<T>(5), static_cast<T>(7));
  do_encode_decode_order_test(std::numeric_limits<T>::min(),
                              std::numeric_limits<T>::min() + one);
  do_encode_decode_order_test(std::numeric_limits<T>::max() - one,
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
    EXPECT_EQ(u, 0x7fc00000U);  // specific known value.
  } else {
    EXPECT_EQ(actual, expected);
    if (reinterpret_cast<const U&>(expected) == 0U) {
      // Verify that the encoded value is 0U.
      U u;
      unodb::key_decoder dec{enc.get_key_view()};
      dec.decode(u);
      EXPECT_EQ(u, 0U);  // specific known value.
    }
  }
}

/// Test encode/decode of various floating point values.
TEST(ARTKeyEncodeDecodeTest, FloatC0001) {
  using F = float;
  do_encode_decode_float_test(0.F);
  do_encode_decode_float_test(10.001F);
  do_encode_decode_float_test(-10.001F);
  do_encode_decode_float_test(std::numeric_limits<F>::min());
  do_encode_decode_float_test(std::numeric_limits<F>::lowest());
  do_encode_decode_float_test(std::numeric_limits<F>::max());
  do_encode_decode_float_test(std::numeric_limits<F>::epsilon());
  do_encode_decode_float_test(-std::numeric_limits<F>::denorm_min());
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
    EXPECT_EQ(u, 0x7ff8000000000000ULL);  // specific known value.
  } else {
    EXPECT_EQ(actual, expected);
    if (reinterpret_cast<const U&>(expected) == 0ULL) {
      // Verify that the encoded value is 0U.
      U u;
      unodb::key_decoder dec{enc.get_key_view()};
      dec.decode(u);
      EXPECT_EQ(u, 0ULL);  // specific known value.
    }
  }
}

/// Test encode/decode of various double precisions floating point
/// values.
TEST(ARTKeyEncodeDecodeTest, DoubleC0001) {
  using F = double;
  do_encode_decode_double_test(0.0);
  do_encode_decode_double_test(10.001);
  do_encode_decode_double_test(-10.001);
  do_encode_decode_double_test(std::numeric_limits<F>::min());
  do_encode_decode_double_test(std::numeric_limits<F>::lowest());
  do_encode_decode_double_test(std::numeric_limits<F>::max());
  do_encode_decode_double_test(std::numeric_limits<F>::epsilon());
  do_encode_decode_double_test(-std::numeric_limits<F>::denorm_min());
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

void do_simple_pad_test(const char* s) {
  using ST = unodb::key_encoder::size_type;
  const auto sz = strlen(s);
  unodb::key_encoder enc;
  const auto kv = enc.reset().encode_text(s).get_key_view();
  EXPECT_EQ(kv.size(), sz + 1 + sizeof(ST)) << "[" << s << "]";
  EXPECT_EQ(std::memcmp(s, kv.data(), sz), 0) << "[" << s << "]";
  EXPECT_EQ(kv[sz], unodb::key_encoder::pad) << "[" << s << "]";
  const ST padlen{static_cast<ST>(unodb::key_encoder::maxlen - sz)};
  ST tmp;
  memcpy(&tmp, kv.data() + sz + 1, sizeof(ST));  // copy out pad length.
  ST tmp2 = unodb::detail::bswap(tmp);
  EXPECT_EQ(tmp2, padlen) << "[" << s << "]";
}

/// Verify proper padding to maxlen.
//
// FIXME(thompsonbry) variable length keys - extend test to handle
// truncation.
TEST(ARTKeyEncodeDecodeTest, EncodeTextC0001) {
  do_simple_pad_test("");
  do_simple_pad_test("abc");
  do_simple_pad_test("brown");
  do_simple_pad_test("banana");
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

// FIXME(thompsonbry) variable length keys - multi-field tests.

UNODB_END_TESTS()

}  // namespace
