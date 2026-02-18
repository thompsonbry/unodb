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

// ===================================================================
// Compound key_view tests for the dispatch byte collision bug.
//
// key_prefix_capacity is 7 bytes.  When two key_view keys share more
// than 7 bytes of common prefix, the leaf-to-inode4 split must create
// a chain of internal nodes rather than a single inode4, because the
// dispatch byte (the byte immediately after the stored prefix) is the
// same for both keys.
//
// Test plan groups:
//   1. Prefix boundary cases — validate various shared-prefix lengths
//   2. Node growth — inode4 -> inode16 -> inode48 -> inode256
//   3. Removal & shrinkage — chained inodes collapse correctly
//   4. Mixed key lengths — different-length keys with long shared prefix
//   5. Duplicate & edge cases — duplicate insert, get-missing
// ===================================================================

// Helper: encode a compound key (uint32, uint8, uint64) = 13 bytes.
inline unodb::key_view make_key13(unodb::key_encoder& enc, std::uint32_t a,
                                  std::uint8_t b, std::uint64_t c) {
  return enc.reset().encode(a).encode(b).encode(c).get_key_view();
}

// Helper: encode a compound key (uint32, uint8, uint32) = 9 bytes.
inline unodb::key_view make_key9(unodb::key_encoder& enc, std::uint32_t a,
                                 std::uint8_t b, std::uint32_t c) {
  return enc.reset().encode(a).encode(b).encode(c).get_key_view();
}

// -------------------------------------------------------------------
// Group 0: Original bug reproduction tests
// -------------------------------------------------------------------

/// Two 13-byte keys sharing 12 bytes — dispatch byte collision.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, CompoundKeysLongSharedPrefix) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  verifier.insert(make_key13(enc, 100, 0x42, 1), val);
  verifier.insert(make_key13(enc, 100, 0x42, 2), val);
  verifier.check_present_values();
}

/// Three compound keys with the same uint32+uint8 prefix.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, ThreeCompoundKeysLongSharedPrefix) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  verifier.insert(make_key13(enc, 100, 0x42, 1), val);
  verifier.insert(make_key13(enc, 100, 0x42, 2), val);
  verifier.insert(make_key13(enc, 100, 0x42, 3), val);
  verifier.check_present_values();
}

/// 9-byte keys sharing 8 bytes — minimal collision case.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, NineByteCompoundKeysLongPrefix) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  verifier.insert(make_key9(enc, 100, 0x42, 1), val);
  verifier.insert(make_key9(enc, 100, 0x42, 2), val);
  verifier.check_present_values();
}

/// Control: keys diverge within the first 8 bytes — works today.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, CompoundKeysDifferentPrefixes) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  verifier.insert(make_key13(enc, 50, 0x42, 1), val);
  verifier.insert(make_key13(enc, 200, 0x42, 2), val);
  verifier.check_present_values();
}

// -------------------------------------------------------------------
// Group 1: Prefix boundary cases
// -------------------------------------------------------------------

/// Keys diverge at byte 8 (prefix fills capacity, dispatch byte differs).
/// Encodes (uint32=100, uint8=0x42, uint64) where the uint64 values
/// have different high bytes: 0x0100... vs 0x0200...
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, CompoundKeysDivergeAtByte8) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  // byte layout: [4 bytes uint32][1 byte uint8][8 bytes uint64]
  // bytes 0-4 identical, bytes 5-7 = prefix, byte 5 = dispatch byte for
  // uint64 high byte.  These values have different byte[5]:
  verifier.insert(make_key13(enc, 100, 0x42, 0x0100000000000000ULL), val);
  verifier.insert(make_key13(enc, 100, 0x42, 0x0200000000000000ULL), val);
  verifier.check_present_values();
}

/// Keys share 9 bytes — requires two levels of chaining beyond prefix.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, CompoundKeysMaxPrefixPlusTwo) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  // 13-byte keys sharing bytes 0..8 (9 bytes), differing at byte 9.
  // uint32=100, uint8=0x42 gives 5 shared bytes.  uint64 values
  // 0x0000010000000001 vs 0x0000020000000001 differ at byte 7 of the
  // uint64 (= byte 12 overall... let's be precise).
  // We want 9 shared bytes total = bytes 0..8.  That's the 5-byte
  // (uint32+uint8) prefix plus 4 more zero bytes from uint64.
  // uint64 values: 0x0000000001000000 vs 0x0000000002000000
  // encoded big-endian: 00 00 00 00 01 00 00 00 vs 00 00 00 00 02 00 00 00
  // shared through byte 8 (= prefix byte 4 of uint64), differ at byte 9.
  verifier.insert(make_key13(enc, 100, 0x42, 0x0000000100000000ULL), val);
  verifier.insert(make_key13(enc, 100, 0x42, 0x0000000200000000ULL), val);
  verifier.check_present_values();
}

/// Keys identical except last byte — maximum chaining depth.
/// 13-byte keys sharing 12 bytes, differing only at byte 12.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest,
                 CompoundKeysIdenticalExceptLastByte) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  verifier.insert(make_key13(enc, 100, 0x42, 1), val);
  verifier.insert(make_key13(enc, 100, 0x42, 2), val);
  verifier.insert(make_key13(enc, 100, 0x42, 3), val);
  verifier.insert(make_key13(enc, 100, 0x42, 4), val);
  verifier.check_present_values();
}

/// Stress test: for a 20-byte key, insert pairs that diverge at each
/// possible dispatch-byte position after the 7-byte prefix.  For
/// divergence position d (7 <= d <= 18), the two keys share bytes
/// 0..d-1 and differ at byte d.  All pairs coexist in the same tree
/// but use distinct byte[0] values so each pair occupies an independent
/// subtree and the second insert always hits the leaf-split path.
///
/// This exercises inode chains of every depth from 1 (d=7, dispatch
/// byte immediately after prefix) to 12 (d=18, second-to-last byte).
///
/// Key construction: 20 bytes built from encode(uint8_t) calls.
/// Byte 0 encodes the divergence position d (making subtrees disjoint).
/// Bytes 1..6 are 0xAA (filling the 7-byte prefix with bytes 0..6).
/// Bytes 7..d-1 are 0x00 (shared chain bytes beyond the prefix).
/// Byte d is 0x01 vs 0x02 (the divergence point).
/// Bytes d+1..19 are 0x00 (padding).
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, StressDivergeAtEveryPosition) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  constexpr unsigned key_len = 20;
  constexpr unsigned prefix_cap = 7;

  for (unsigned d = prefix_cap; d < key_len - 1; ++d) {
    for (unsigned variant = 1; variant <= 2; ++variant) {
      enc.reset();
      enc.encode(static_cast<std::uint8_t>(d));  // byte 0: unique per d
      for (unsigned i = 1; i < key_len; ++i) {
        if (i < prefix_cap) {
          enc.encode(std::uint8_t{0xAA});         // bytes 1..6: shared prefix
        } else if (i < d) {
          enc.encode(std::uint8_t{0x00});          // bytes 7..d-1: shared chain
        } else if (i == d) {
          enc.encode(static_cast<std::uint8_t>(variant));  // divergence point
        } else {
          enc.encode(std::uint8_t{0x00});          // padding
        }
      }
      verifier.insert(enc.get_key_view(), val);
    }
  }
  // 12 divergence positions × 2 keys each = 24 keys total.
  verifier.check_present_values();
}

// -------------------------------------------------------------------
// Group 2: Node growth (inode4 -> inode16 -> inode48 -> inode256)
// -------------------------------------------------------------------

/// 5 keys with same 12-byte prefix — forces inode4 -> inode16 growth.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, CompoundKeysFiveChildren) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  for (std::uint64_t i = 1; i <= 5; ++i) {
    verifier.insert(make_key13(enc, 100, 0x42, i), val);
  }
  verifier.check_present_values();
}

/// 17 keys — forces inode16 -> inode48 growth.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, CompoundKeysSeventeenChildren) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  for (std::uint64_t i = 1; i <= 17; ++i) {
    verifier.insert(make_key13(enc, 100, 0x42, i), val);
  }
  verifier.check_present_values();
}

/// 50 keys — forces inode48 -> inode256 growth.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, CompoundKeysFiftyChildren) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  for (std::uint64_t i = 1; i <= 50; ++i) {
    verifier.insert(make_key13(enc, 100, 0x42, i), val);
  }
  verifier.check_present_values();
}

// -------------------------------------------------------------------
// Group 3: Removal & shrinkage
// -------------------------------------------------------------------

/// Insert 2 colliding keys, remove one, verify the other is still found.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, CompoundKeysInsertThenRemove) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  verifier.insert(make_key13(enc, 100, 0x42, 1), val);
  verifier.insert(make_key13(enc, 100, 0x42, 2), val);
  verifier.remove(make_key13(enc, 100, 0x42, 1));
  verifier.check_present_values();
}

/// Insert 3 colliding keys, remove all, verify tree is empty.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, CompoundKeysInsertRemoveAll) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  verifier.insert(make_key13(enc, 100, 0x42, 1), val);
  verifier.insert(make_key13(enc, 100, 0x42, 2), val);
  verifier.insert(make_key13(enc, 100, 0x42, 3), val);
  verifier.remove(make_key13(enc, 100, 0x42, 1));
  verifier.remove(make_key13(enc, 100, 0x42, 2));
  verifier.remove(make_key13(enc, 100, 0x42, 3));
  verifier.assert_empty();
}

/// Insert 5 colliding keys (-> inode16), remove 2 (-> inode4 shrink).
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, CompoundKeysShrinkInode16) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  for (std::uint64_t i = 1; i <= 5; ++i) {
    verifier.insert(make_key13(enc, 100, 0x42, i), val);
  }
  verifier.remove(make_key13(enc, 100, 0x42, 1));
  verifier.remove(make_key13(enc, 100, 0x42, 2));
  verifier.check_present_values();
}

// -------------------------------------------------------------------
// Group 4: Mixed key lengths
// -------------------------------------------------------------------

/// A 9-byte key and a 13-byte key sharing the first 8 bytes.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, MixedLengthKeysLongPrefix) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  // 9-byte key: (uint32=100, uint8=0x42, uint32=1)
  verifier.insert(make_key9(enc, 100, 0x42, 1), val);
  // 13-byte key: (uint32=100, uint8=0x42, uint64=1)
  verifier.insert(make_key13(enc, 100, 0x42, 1), val);
  verifier.check_present_values();
}

// -------------------------------------------------------------------
// Group 5: Duplicate & edge cases
// -------------------------------------------------------------------

/// Inserting the same 13-byte key twice returns false on the second insert.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, CompoundKeyDuplicateInsert) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  verifier.insert(make_key13(enc, 100, 0x42, 1), val);
  // Second insert of same key should fail.
  UNODB_ASSERT_FALSE(verifier.get_db().insert(make_key13(enc, 100, 0x42, 1),
                                              val));
  verifier.check_present_values();
}

/// Get with a key sharing 12 bytes but differing at the last byte
/// should return empty when only one key is present.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, CompoundKeyGetMissing) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  verifier.insert(make_key13(enc, 100, 0x42, 1), val);
  const auto result = verifier.get_db().get(make_key13(enc, 100, 0x42, 2));
  UNODB_ASSERT_FALSE(TypeParam::key_found(result));
  verifier.check_present_values();
}

}  // namespace
