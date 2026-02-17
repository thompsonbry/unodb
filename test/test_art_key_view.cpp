// Copyright 2025 UnoDB contributors

// Should be the first include
#include "global.hpp"  // IWYU pragma: keep

// IWYU pragma: no_include <__cstddef/byte.h>
// IWYU pragma: no_include <array>
// IWYU pragma: no_include <span>
// IWYU pragma: no_include <string>
// IWYU pragma: no_include <string_view>

#include <cstddef>  // IWYU pragma: keep
#include <cstdint>
#include <limits>
#include <stdexcept>
#include <tuple>

#include <gtest/gtest.h>

#include "art_common.hpp"
#include "db_test_utils.hpp"
#include "gtest_utils.hpp"

namespace {

template <class Db>
class ARTKeyViewCorrectnessTest : public ::testing::Test {
 public:
  using Test::Test;
};

using ARTTypes =
    ::testing::Types<unodb::test::key_view_db, unodb::test::key_view_mutex_db,
                     unodb::test::key_view_olc_db>;

UNODB_TYPED_TEST_SUITE(ARTKeyViewCorrectnessTest, ARTTypes)

/// Unit test of correct rejection of a key which is too large to be
/// stored in the tree.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, TooLongKey) {
  constexpr std::byte fake_val{0x00};
  const unodb::key_view too_long{
      &fake_val,
      static_cast<std::uint64_t>(std::numeric_limits<std::uint32_t>::max()) +
          1U};

  unodb::test::tree_verifier<TypeParam> verifier;

  UNODB_ASSERT_THROW(std::ignore = verifier.get_db().insert(too_long, {}),
                     std::length_error);

  verifier.assert_empty();

#ifdef UNODB_DETAIL_WITH_STATS
  verifier.assert_growing_inodes({0, 0, 0, 0});
#endif  // UNODB_DETAIL_WITH_STATS
}

/// Unit test inserts several string keys with proper encoding and
/// validates the tree.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, EncodedTextKeys) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];
  verifier.insert(enc.reset().encode_text("").get_key_view(), val);
  verifier.insert(enc.reset().encode_text("a").get_key_view(), val);
  verifier.insert(enc.reset().encode_text("abba").get_key_view(), val);
  verifier.insert(enc.reset().encode_text("banana").get_key_view(), val);
  verifier.insert(enc.reset().encode_text("camel").get_key_view(), val);
  verifier.insert(enc.reset().encode_text("yellow").get_key_view(), val);
  verifier.insert(enc.reset().encode_text("ostritch").get_key_view(), val);
  verifier.insert(enc.reset().encode_text("zebra").get_key_view(), val);
  verifier.check_present_values();  // checks keys and key ordering.
}

/// Compound keys (uint32:4 + uint8:1 + uint64:8 = 13 bytes) where the
/// keys share a prefix longer than key_prefix_capacity (7 bytes).
///
/// When two 13-byte keys share the same uint32 and uint8 and have small
/// uint64 values, they share 12 of 13 bytes.  After the 7-byte inode
/// prefix, byte[7] = 0x00 for both keys, causing a dispatch byte
/// collision in the leaf-to-inode4 split.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, CompoundKeysLongSharedPrefix) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  // Two 13-byte keys sharing 12 bytes of prefix.
  verifier.insert(
      enc.reset().encode(std::uint32_t{100}).encode(std::uint8_t{0x42}).encode(
          std::uint64_t{1}).get_key_view(), val);
  verifier.insert(
      enc.reset().encode(std::uint32_t{100}).encode(std::uint8_t{0x42}).encode(
          std::uint64_t{2}).get_key_view(), val);
  verifier.check_present_values();
}

/// Three compound keys with the same uint32+uint8 prefix and different
/// small uint64 values.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, ThreeCompoundKeysLongSharedPrefix) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  verifier.insert(
      enc.reset().encode(std::uint32_t{100}).encode(std::uint8_t{0x42}).encode(
          std::uint64_t{1}).get_key_view(), val);
  verifier.insert(
      enc.reset().encode(std::uint32_t{100}).encode(std::uint8_t{0x42}).encode(
          std::uint64_t{2}).get_key_view(), val);
  verifier.insert(
      enc.reset().encode(std::uint32_t{100}).encode(std::uint8_t{0x42}).encode(
          std::uint64_t{3}).get_key_view(), val);
  verifier.check_present_values();
}

/// 9-byte compound keys (uint32:4 + uint8:1 + uint32:4) with small
/// trailing uint32 values share 8 bytes of prefix (> key_prefix_capacity + 1).
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, NineByteCompoundKeysLongPrefix) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  verifier.insert(
      enc.reset().encode(std::uint32_t{100}).encode(std::uint8_t{0x42}).encode(
          std::uint32_t{1}).get_key_view(), val);
  verifier.insert(
      enc.reset().encode(std::uint32_t{100}).encode(std::uint8_t{0x42}).encode(
          std::uint32_t{2}).get_key_view(), val);
  verifier.check_present_values();
}

/// Control: compound keys that diverge within the first 8 bytes work.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, CompoundKeysDifferentPrefixes) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  verifier.insert(
      enc.reset().encode(std::uint32_t{50}).encode(std::uint8_t{0x42}).encode(
          std::uint64_t{1}).get_key_view(), val);
  verifier.insert(
      enc.reset().encode(std::uint32_t{200}).encode(std::uint8_t{0x42}).encode(
          std::uint64_t{2}).get_key_view(), val);
  verifier.check_present_values();
}

}  // namespace
