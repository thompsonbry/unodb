// Copyright 2025 UnoDB contributors

// Should be the first include
#include "global.hpp"  // IWYU pragma: keep

// IWYU pragma: no_include <string>
// IWYU pragma: no_include <string_view>
// IWYU pragma: no_include "gtest/gtest.h"

#include <array>
#include <cstddef>
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

UNODB_START_TESTS()

/// Unit test of correct rejection of a key which is too large to be
/// stored in the tree.
UNODB_DETAIL_DISABLE_MSVC_WARNING(6326)
TYPED_TEST(ARTKeyViewCorrectnessTest, TooLongKey) {
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
UNODB_DETAIL_RESTORE_MSVC_WARNINGS()

/// Unit test inserts several string keys with proper encoding and
/// validates the tree.
TYPED_TEST(ARTKeyViewCorrectnessTest, EncodedTextKeys) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto& val = unodb::test::test_values[0];
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

/// This test inserts a single key which is longer than the
/// unodb::detail::key_prefix plus the `key_byte`.  In this case, the
/// key needs to be unfolded as a sequence of inodes until the entire
/// key is absorbed.  Thus, the tree depth for this single key is
/// `key.size_bytes() / 8`.
///
// TODO(thompsonbry) no root leaf.  Write more unit tests to probe
// more cases.
TYPED_TEST(ARTKeyViewCorrectnessTest, SingleKeyUnfoldedByINodePath) {
  unodb::test::tree_verifier<TypeParam> verifier;
  // key is an 8-byte prefix of the key we insert.
  constexpr auto a0 = std::array<std::byte, 8>{
      std::byte{0x00}, std::byte{0x01}, std::byte{0x02}, std::byte{0x03},
      std::byte{0x04}, std::byte{0x05}, std::byte{0x06}, std::byte{0x07}};
  // key is 16-bytes long, so it terminates on the second inode.
  constexpr auto a1 = std::array<std::byte, 16>{
      std::byte{0x00}, std::byte{0x01}, std::byte{0x02}, std::byte{0x03},
      std::byte{0x04}, std::byte{0x05}, std::byte{0x06}, std::byte{0x07},
      std::byte{0x10}, std::byte{0x11}, std::byte{0x12}, std::byte{0x13},
      std::byte{0x14}, std::byte{0x15}, std::byte{0x16}, std::byte{0x17}};
  unodb::key_view k0{a0};
  unodb::key_view k1{a1};
  verifier.insert(k1, unodb::test::test_values[2]);

  verifier.assert_root_not_leaf();
  verifier.check_present_values();
  verifier.check_absent_keys({k0});

#ifdef UNODB_DETAIL_WITH_STATS
  verifier.assert_node_counts({0, 2, 0, 0, 0});  // two I4
  verifier.assert_growing_inodes({2, 0, 0, 0});  // two I4
#endif                                           // UNODB_DETAIL_WITH_STATS
}

UNODB_END_TESTS()

}  // namespace
