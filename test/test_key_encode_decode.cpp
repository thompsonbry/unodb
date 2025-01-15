// Copyright 2019-2024 Laurynas Biveinis

// IWYU pragma: no_include <array>
// IWYU pragma: no_include <string>
// IWYU pragma: no_include "gtest/gtest.h"

//
// CAUTION: [global.hpp] MUST BE THE FIRST INCLUDE IN ALL SOURCE AND
// HEADER FILES !!!
//
// This header defines _GLIBCXX_DEBUG and _GLIBCXX_DEBUG_PEDANTIC for
// DEBUG builds.  If some standard headers are included before and
// after those symbols are defined, then that results in different
// container internal structure layouts and that is Not Good.
#include "global.hpp"  // IWYU pragma: keep

#include <cstddef>
#include <cstdint>
#include <limits>
#include <stdexcept>

#include <gtest/gtest.h>

#include "art_common.hpp"
#include "art_internal.hpp"
#include "db_test_utils.hpp"
#include "gtest_utils.hpp"
#include "test_utils.hpp"

namespace {

// TODO(thompsonbry) : variable length keys.  Add coverage for
// lexicographic ordering of all the interesting key types via the
// key_encoder and their proper decoding (where possible) via the
// decoder.
//
// TODO(thompsonbry) : variable length keys.  Add a microbenchmark for
// the key_encoder.
template <class Db>
class ARTKeyEncodeDecodeTest : public ::testing::Test {
 public:
  using Test::Test;
};

using unodb::detail::compare;

// exposes some protected methods and data to the tests.
class my_key_encoder : public unodb::key_encoder {
 public:
  my_key_encoder() : key_encoder() {}
  static constexpr size_t get_initial_capacity() {
    return key_encoder::INITIAL_CAPACITY;
  }
  size_t capacity() { return key_encoder::capacity(); }
  size_t size_bytes() { return key_encoder::size_bytes(); }
  void ensure_available(size_t req) { key_encoder::ensure_available(req); }
};

static constexpr auto INITIAL_CAPACITY = my_key_encoder::get_initial_capacity();

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

// std::uint64_t
TEST(ARTKeyEncodeDecodeTest, C00010) {
  constexpr std::uint64_t ekey = 0x0102030405060708;
  my_key_encoder enc{};
  enc.encode(ekey);
  const unodb::key_view kv = enc.get_key_view();   // encode
  EXPECT_EQ(kv.size_bytes(), sizeof(ekey));        // check size
  EXPECT_EQ(static_cast<std::byte>(0x01), kv[0]);  // check order.
  EXPECT_EQ(static_cast<std::byte>(0x02), kv[1]);
  EXPECT_EQ(static_cast<std::byte>(0x03), kv[2]);
  EXPECT_EQ(static_cast<std::byte>(0x04), kv[3]);
  EXPECT_EQ(static_cast<std::byte>(0x05), kv[4]);
  EXPECT_EQ(static_cast<std::byte>(0x06), kv[5]);
  EXPECT_EQ(static_cast<std::byte>(0x07), kv[6]);
  EXPECT_EQ(static_cast<std::byte>(0x08), kv[7]);
}

// check lexicographic ordering for two std::uint64_t keys.
//
// TODO(thompsonbry) we need a torture test for lexicographic ordering
// focused on the edge cases of signed and unsigned types.
TEST(ARTKeyEncodeDecodeTest, C00011) {
  const std::uint64_t ekey1 = 0x0102030405060708ULL;  // external key
  const std::uint64_t ekey2 = 0x090A0B0C0D0F1011ULL;  // external key
  unodb::key_encoder enc1{};
  unodb::key_encoder enc2{};
  const auto ikey1 = enc1.encode(ekey1).get_key_view();  // into encoder buf!
  const auto ikey2 = enc2.encode(ekey2).get_key_view();  // into encoder buf!
  EXPECT_TRUE(compare(ikey1, ikey1) == 0);
  EXPECT_TRUE(compare(ikey2, ikey2) == 0);
  EXPECT_TRUE(compare(ikey1, ikey2) != 0);
  EXPECT_TRUE(compare(ikey1, ikey2) < 0);
  EXPECT_TRUE(compare(ikey2, ikey1) > 0);
}

UNODB_END_TESTS()

}  // namespace
