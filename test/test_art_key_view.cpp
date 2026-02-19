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
// key_view tests for the dispatch byte collision bug.
//
// key_prefix_capacity is 7 bytes.  When two key_view keys share more
// than 7 bytes of common prefix, the leaf-to-inode4 split must create
// a chain of internal nodes rather than a single inode4, because the
// dispatch byte (the byte immediately after the stored prefix) is the
// same for both keys.
//
// Keys are 9 bytes: (uint8_t tag, uint64_t value).  Same tag + small
// values → 8 shared bytes, triggering the bug.  10-byte keys
// (uint8_t tag, uint64_t value, uint8_t suffix) are used for
// mixed-length tests.  Both lengths exceed key_prefix_capacity + 1.
//
// Test plan groups:
//   0. Bug reproduction — minimal cases
//   1. Prefix boundary cases — validate various shared-prefix lengths
//   2. Node growth — inode4 -> inode16 -> inode48 -> inode256
//   3. Removal & shrinkage — chained inodes collapse correctly
//   4. Mixed key lengths — different-length keys with long shared prefix
//   5. Duplicate & edge cases — duplicate insert, get-missing
//   6. Stats verification — node counts at intermediate states
//     6a. Insert stats — verify chain structure after insert
//     6b. Partial remove — bottom inode shrinks, chain preserved
//         I16→I4, I48→I16, I256→I48
//     6c. Full remove — remove all keys through each bottom inode size
//         I4, I16, I48, I256
//     6d. Cascade — chain under parent at min_size, removing chain
//         triggers parent shrinkage: I4→leaf, I16→I4, I48→I16, I256→I48
//     6e. Multi-level chain — 17-byte keys, 2 chain levels
// ===================================================================

// Helper: encode a 9-byte key (uint8 + uint64).
// Same tag byte → 8 shared bytes when uint64 values are small.
inline unodb::key_view make_key(unodb::key_encoder& enc, std::uint8_t tag,
                                std::uint64_t v) {
  return enc.reset().encode(tag).encode(v).get_key_view();
}

// Helper: encode a 1-byte key (uint8 only).
// Diverges at byte 0 from any key with a different first byte.
// Used in cascade tests where we need direct-leaf children of the root
// alongside a chain subtree.
inline unodb::key_view make_short_key(unodb::key_encoder& enc,
                                      std::uint8_t tag) {
  return enc.reset().encode(tag).get_key_view();
}

// Helper: encode a 10-byte key (uint8 + uint64 + uint8).
// When used with the same tag and v as make_key, the 9-byte key is a
// prefix of this 10-byte key — which ART does not support.  Use
// different v values to avoid prefix relationships.
// Both lengths (9 and 10) exceed key_prefix_capacity + 1 = 8.
inline unodb::key_view make_long_key(unodb::key_encoder& enc,
                                     std::uint8_t tag, std::uint64_t v,
                                     std::uint8_t suffix) {
  return enc.reset().encode(tag).encode(v).encode(suffix).get_key_view();
}

// -------------------------------------------------------------------
// Group 0: Original bug reproduction tests
// -------------------------------------------------------------------

/// Two 9-byte keys sharing 8 bytes — dispatch byte collision.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, CompoundKeysLongSharedPrefix) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  verifier.insert(make_key(enc, 0x42, 1), val);
  verifier.insert(make_key(enc, 0x42, 2), val);
  verifier.check_present_values();
#ifdef UNODB_DETAIL_WITH_STATS
  // chain I4 (prefix=7, 1 child) + bottom I4 (2 children) + 2 leaves
  verifier.assert_node_counts({2, 2, 0, 0, 0});
#endif  // UNODB_DETAIL_WITH_STATS
}

/// Three keys with the same tag byte and small uint64 values.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, ThreeCompoundKeysLongSharedPrefix) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  verifier.insert(make_key(enc, 0x42, 1), val);
  verifier.insert(make_key(enc, 0x42, 2), val);
  verifier.insert(make_key(enc, 0x42, 3), val);
  verifier.check_present_values();
#ifdef UNODB_DETAIL_WITH_STATS
  // chain I4 + bottom I4 (3 children) + 3 leaves
  verifier.assert_node_counts({3, 2, 0, 0, 0});
#endif  // UNODB_DETAIL_WITH_STATS
}

/// 9-byte keys sharing 8 bytes — minimal collision case.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, NineByteCompoundKeysLongPrefix) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  verifier.insert(make_key(enc, 0x42, 1), val);
  verifier.insert(make_key(enc, 0x42, 2), val);
  verifier.check_present_values();
#ifdef UNODB_DETAIL_WITH_STATS
  verifier.assert_node_counts({2, 2, 0, 0, 0});
#endif  // UNODB_DETAIL_WITH_STATS
}

/// Control: keys diverge within the first 8 bytes — works today.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, CompoundKeysDifferentPrefixes) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  verifier.insert(make_key(enc, 0x01, 1), val);
  verifier.insert(make_key(enc, 0x02, 2), val);
  verifier.check_present_values();
}

// -------------------------------------------------------------------
// Group 1: Prefix boundary cases
// -------------------------------------------------------------------

/// Keys diverge at byte 1 (prefix fills capacity, dispatch byte differs).
/// uint64 values with different high bytes produce different byte[1].
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, CompoundKeysDivergeAtByte8) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  verifier.insert(make_key(enc, 0x42, 0x0100000000000000ULL), val);
  verifier.insert(make_key(enc, 0x42, 0x0200000000000000ULL), val);
  verifier.check_present_values();
}

/// Keys share 5 bytes (tag + 4 zero bytes of uint64), differ at byte 5.
/// Requires two levels of chaining beyond the prefix.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, CompoundKeysMaxPrefixPlusTwo) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  // 9-byte keys: tag=0x42, uint64 values differ at their 4th byte
  // (= byte 5 overall).  Shared: bytes 0..4.
  verifier.insert(make_key(enc, 0x42, 0x0000000100000000ULL), val);
  verifier.insert(make_key(enc, 0x42, 0x0000000200000000ULL), val);
  verifier.check_present_values();
}

/// Keys identical except last byte — maximum chaining depth for 9-byte keys.
/// 9-byte keys sharing 8 bytes, differing only at byte 8.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest,
                 CompoundKeysIdenticalExceptLastByte) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  verifier.insert(make_key(enc, 0x42, 1), val);
  verifier.insert(make_key(enc, 0x42, 2), val);
  verifier.insert(make_key(enc, 0x42, 3), val);
  verifier.insert(make_key(enc, 0x42, 4), val);
  verifier.check_present_values();
#ifdef UNODB_DETAIL_WITH_STATS
  // chain I4 + bottom I4 (4 children, at capacity) + 4 leaves
  verifier.assert_node_counts({4, 2, 0, 0, 0});
#endif  // UNODB_DETAIL_WITH_STATS
}

/// Two 17-byte keys sharing 16 bytes — forces two consecutive chain
/// nodes (depth 0→8 and depth 8→16) before the normal 2-child split.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, MultiLevelChain) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  // 17 bytes: 0xAA × 16, then 0x01 vs 0x02.
  auto make17 = [&](std::uint8_t last) {
    enc.reset();
    for (unsigned i = 0; i < 16; ++i) enc.encode(std::uint8_t{0xAA});
    enc.encode(last);
    return enc.get_key_view();
  };
  verifier.insert(make17(0x01), val);
  verifier.insert(make17(0x02), val);
  verifier.check_present_values();
#ifdef UNODB_DETAIL_WITH_STATS
  // 2 chain I4s (depth 0→8, 8→16) + bottom I4 (2 children) + 2 leaves
  verifier.assert_node_counts({2, 3, 0, 0, 0});
#endif  // UNODB_DETAIL_WITH_STATS
}

/// Three 17-byte keys: A and B share 16 bytes, C diverges at byte 10.
/// After inserting A and B (two chain levels), inserting C splits the
/// second chain node mid-prefix.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest,
                 InsertDivergingAtIntermediateChainDepth) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  auto make17 = [&](std::uint8_t byte10, std::uint8_t last) {
    enc.reset();
    for (unsigned i = 0; i < 10; ++i) enc.encode(std::uint8_t{0xAA});
    enc.encode(byte10);
    for (unsigned i = 11; i < 16; ++i) enc.encode(std::uint8_t{0xAA});
    enc.encode(last);
    return enc.get_key_view();
  };
  // A and B share 16 bytes (byte10=0xAA), differ at byte 16.
  verifier.insert(make17(0xAA, 0x01), val);
  verifier.insert(make17(0xAA, 0x02), val);
  // C diverges at byte 10 — splits the second chain node.
  verifier.insert(make17(0xBB, 0x03), val);
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

/// 5 keys with same 8-byte prefix — forces inode4 -> inode16 growth.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, CompoundKeysFiveChildren) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  for (std::uint64_t i = 1; i <= 5; ++i) {
    verifier.insert(make_key(enc, 0x42, i), val);
  }
  verifier.check_present_values();
#ifdef UNODB_DETAIL_WITH_STATS
  // chain I4 + I16 (5 children) + 5 leaves
  verifier.assert_node_counts({5, 1, 1, 0, 0});
#endif  // UNODB_DETAIL_WITH_STATS
}

/// 17 keys — forces inode16 -> inode48 growth.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, CompoundKeysSeventeenChildren) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  for (std::uint64_t i = 1; i <= 17; ++i) {
    verifier.insert(make_key(enc, 0x42, i), val);
  }
  verifier.check_present_values();
#ifdef UNODB_DETAIL_WITH_STATS
  // chain I4 + I48 (17 children) + 17 leaves
  verifier.assert_node_counts({17, 1, 0, 1, 0});
#endif  // UNODB_DETAIL_WITH_STATS
}

/// 50 keys — forces inode48 -> inode256 growth.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, CompoundKeysFiftyChildren) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  for (std::uint64_t i = 1; i <= 50; ++i) {
    verifier.insert(make_key(enc, 0x42, i), val);
  }
  verifier.check_present_values();
#ifdef UNODB_DETAIL_WITH_STATS
  // chain I4 + I256 (50 children) + 50 leaves
  verifier.assert_node_counts({50, 1, 0, 0, 1});
#endif  // UNODB_DETAIL_WITH_STATS
}

// -------------------------------------------------------------------
// Group 3: Removal & shrinkage
// -------------------------------------------------------------------

// Group 3a: Chain collapse scenarios

/// Insert 2 colliding keys, remove one, verify the other is still found.
/// The chain of inode_4s should collapse to a single leaf.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, CompoundKeysInsertThenRemove) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  verifier.insert(make_key(enc, 0x42, 1), val);
  verifier.insert(make_key(enc, 0x42, 2), val);
  verifier.remove(make_key(enc, 0x42, 1));
  verifier.check_present_values();
#ifdef UNODB_DETAIL_WITH_STATS
  // Bottom I4 collapsed via leave_last_child.  Chain I4 remains with
  // 1 child (the surviving leaf).
  verifier.assert_node_counts({1, 1, 0, 0, 0});
#endif  // UNODB_DETAIL_WITH_STATS
}

/// Insert 3 keys: two sharing 8 bytes, one diverging earlier.
/// Remove one of the 8-byte-shared pair.  The surviving structure
/// should be an inode with 2 children (the remaining keys).
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, RemoveFromChainLeavesInode) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  // Keys 1 and 2 share 8 bytes; key 3 diverges at byte 5.
  // key3 uint64 = 0x0000000100000000 differs at byte 5 (overall).
  verifier.insert(make_key(enc, 0x42, 1), val);
  verifier.insert(make_key(enc, 0x42, 2), val);
  verifier.insert(make_key(enc, 0x42, 0x0000000100000000ULL), val);
  verifier.remove(make_key(enc, 0x42, 1));
  verifier.check_present_values();
}

/// Insert 3 colliding keys, remove in reverse order, assert empty.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, RemoveAllFromChainReverseOrder) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  verifier.insert(make_key(enc, 0x42, 1), val);
  verifier.insert(make_key(enc, 0x42, 2), val);
  verifier.insert(make_key(enc, 0x42, 3), val);
  verifier.remove(make_key(enc, 0x42, 3));
  verifier.remove(make_key(enc, 0x42, 2));
  verifier.remove(make_key(enc, 0x42, 1));
  verifier.assert_empty();
}

/// Insert 3 colliding keys, remove in forward order, assert empty.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, RemoveAllFromChainForwardOrder) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  verifier.insert(make_key(enc, 0x42, 1), val);
  verifier.insert(make_key(enc, 0x42, 2), val);
  verifier.insert(make_key(enc, 0x42, 3), val);
  verifier.remove(make_key(enc, 0x42, 1));
  verifier.remove(make_key(enc, 0x42, 2));
  verifier.remove(make_key(enc, 0x42, 3));
  verifier.assert_empty();
}

// Group 3b: Shrinkage at chain terminal

/// Insert 5 keys (-> inode16 at chain terminal), remove 3 (-> inode4).
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, ShrinkInode16InChain) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  for (std::uint64_t i = 1; i <= 5; ++i) {
    verifier.insert(make_key(enc, 0x42, i), val);
  }
  verifier.remove(make_key(enc, 0x42, 1));
  verifier.remove(make_key(enc, 0x42, 2));
  verifier.remove(make_key(enc, 0x42, 3));
  verifier.check_present_values();
#ifdef UNODB_DETAIL_WITH_STATS
  // I16(5) shrinks to I4(4) on first remove, then 2 more removes → I4(2).
  verifier.assert_node_counts({2, 2, 0, 0, 0});
#endif  // UNODB_DETAIL_WITH_STATS
}

/// Insert 17 keys (-> inode48), remove 13 (-> shrink to inode4).
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, ShrinkInode48InChain) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  for (std::uint64_t i = 1; i <= 17; ++i) {
    verifier.insert(make_key(enc, 0x42, i), val);
  }
  for (std::uint64_t i = 1; i <= 13; ++i) {
    verifier.remove(make_key(enc, 0x42, i));
  }
  verifier.check_present_values();
#ifdef UNODB_DETAIL_WITH_STATS
  // I48(17) shrinks to I16(16) on first remove, then I16(5) shrinks
  // to I4(4) on 13th remove.
  verifier.assert_node_counts({4, 2, 0, 0, 0});
#endif  // UNODB_DETAIL_WITH_STATS
}

/// Insert 5 keys (-> inode16), remove all 5, assert empty.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, ShrinkToEmptyFromInode16InChain) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  for (std::uint64_t i = 1; i <= 5; ++i) {
    verifier.insert(make_key(enc, 0x42, i), val);
  }
  for (std::uint64_t i = 1; i <= 5; ++i) {
    verifier.remove(make_key(enc, 0x42, i));
  }
  verifier.assert_empty();
}

// Group 3c: Mixed-depth removal

/// Insert a 10-byte and 9-byte key sharing 8 bytes (same tag, different
/// uint64 values).  Remove the 10-byte key, verify 9-byte key.  Then
/// remove it too, assert empty.
///
/// Note: the two keys must NOT be in a prefix relationship — ART does
/// not support one key being a prefix of another.  Using different
/// uint64 values ensures they diverge within the shared bytes.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, RemoveMixedLengthFromChain) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  verifier.insert(make_long_key(enc, 0x42, 1, 0xFF), val);
  verifier.insert(make_key(enc, 0x42, 2), val);
  verifier.remove(make_long_key(enc, 0x42, 1, 0xFF));
  verifier.check_present_values();
  verifier.remove(make_key(enc, 0x42, 2));
  verifier.assert_empty();
}

// Group 3d: Stress removal

/// Insert 24 keys (divergence at positions 7..18), remove every other
/// key, verify remaining.  Then remove all, assert empty.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, StressInsertRemoveAtEveryPosition) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  constexpr unsigned key_len = 20;
  constexpr unsigned prefix_cap = 7;

  // Insert all 24 keys (same structure as StressDivergeAtEveryPosition).
  for (unsigned d = prefix_cap; d < key_len - 1; ++d) {
    for (unsigned variant = 1; variant <= 2; ++variant) {
      enc.reset();
      enc.encode(static_cast<std::uint8_t>(d));
      for (unsigned i = 1; i < key_len; ++i) {
        if (i < prefix_cap) {
          enc.encode(std::uint8_t{0xAA});
        } else if (i < d) {
          enc.encode(std::uint8_t{0x00});
        } else if (i == d) {
          enc.encode(static_cast<std::uint8_t>(variant));
        } else {
          enc.encode(std::uint8_t{0x00});
        }
      }
      verifier.insert(enc.get_key_view(), val);
    }
  }
  verifier.check_present_values();

  // Remove variant=1 keys (one from each pair).
  for (unsigned d = prefix_cap; d < key_len - 1; ++d) {
    enc.reset();
    enc.encode(static_cast<std::uint8_t>(d));
    for (unsigned i = 1; i < key_len; ++i) {
      if (i < prefix_cap) {
        enc.encode(std::uint8_t{0xAA});
      } else if (i < d) {
        enc.encode(std::uint8_t{0x00});
      } else if (i == d) {
        enc.encode(std::uint8_t{1});
      } else {
        enc.encode(std::uint8_t{0x00});
      }
    }
    verifier.remove(enc.get_key_view());
  }
  verifier.check_present_values();

  // Remove remaining variant=2 keys.
  for (unsigned d = prefix_cap; d < key_len - 1; ++d) {
    enc.reset();
    enc.encode(static_cast<std::uint8_t>(d));
    for (unsigned i = 1; i < key_len; ++i) {
      if (i < prefix_cap) {
        enc.encode(std::uint8_t{0xAA});
      } else if (i < d) {
        enc.encode(std::uint8_t{0x00});
      } else if (i == d) {
        enc.encode(std::uint8_t{2});
      } else {
        enc.encode(std::uint8_t{0x00});
      }
    }
    verifier.remove(enc.get_key_view());
  }
  verifier.assert_empty();
}

// -------------------------------------------------------------------
// Group 4: Mixed key lengths
// -------------------------------------------------------------------

/// A 10-byte key and a 9-byte key sharing 8 bytes (same tag, different
/// uint64 values).  The keys must not be in a prefix relationship.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, MixedLengthKeysLongPrefix) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  verifier.insert(make_long_key(enc, 0x42, 1, 0xFF), val);
  verifier.insert(make_key(enc, 0x42, 2), val);
  verifier.check_present_values();
#ifdef UNODB_DETAIL_WITH_STATS
  // chain I4 + bottom I4 (2 children) + 2 leaves
  verifier.assert_node_counts({2, 2, 0, 0, 0});
#endif  // UNODB_DETAIL_WITH_STATS
}

// -------------------------------------------------------------------
// Group 5: Duplicate & edge cases
// -------------------------------------------------------------------

/// Inserting the same 9-byte key twice returns false on the second insert.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, CompoundKeyDuplicateInsert) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  verifier.insert(make_key(enc, 0x42, 1), val);
  // Second insert of same key should fail.
  UNODB_ASSERT_FALSE(verifier.get_db().insert(make_key(enc, 0x42, 1),
                                              val));
  verifier.check_present_values();
}

/// Get with a key sharing 8 bytes but differing at the last byte
/// should return empty when only one key is present.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, CompoundKeyGetMissing) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  verifier.insert(make_key(enc, 0x42, 1), val);
  const auto result = verifier.get_db().get(make_key(enc, 0x42, 2));
  UNODB_ASSERT_FALSE(TypeParam::key_found(result));
  verifier.check_present_values();
}

#ifdef UNODB_DETAIL_WITH_STATS

// ===================================================================
// Group 6: Stats verification — node counts at intermediate states
//
// These tests verify that the tree's internal bookkeeping (node counts,
// memory use) is correct after insert and remove operations involving
// single-child chain I4 nodes.
//
// Inode size thresholds:
//   I4:   min=2, capacity=4   (shrinks via leave_last_child)
//   I16:  min=5, capacity=16  (shrinks to I4)
//   I48:  min=17, capacity=48 (shrinks to I16)
//   I256: min=49, capacity=256 (shrinks to I48)
//
// For keys make_key(enc, 0x42, v) with small v:
//   9 bytes: [0x42, 0,0,0,0,0,0, 0, v]
//   All share 8 bytes, differ only at byte 8.
//   Tree: chain I4 (prefix=7, dispatch=0x00) → bottom inode (children
//   keyed by v).
// ===================================================================

// -------------------------------------------------------------------
// Group 6a: Insert stats — verify chain structure
// -------------------------------------------------------------------

/// Verify node counts after inserting 2 chain-creating keys.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, ChainNodeCountsAfterInsert) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  verifier.insert(make_key(enc, 0x42, 1), val);
  // Single leaf — no inodes yet.
  verifier.assert_node_counts({1, 0, 0, 0, 0});

  verifier.insert(make_key(enc, 0x42, 2), val);
  // chain I4 + bottom I4 + 2 leaves
  verifier.assert_node_counts({2, 2, 0, 0, 0});
  verifier.check_present_values();
}

// -------------------------------------------------------------------
// Group 6b: Partial remove — bottom inode shrinks, chain preserved
// -------------------------------------------------------------------

/// Insert 3 keys, remove 1.  Chain I4 + bottom I4 (2 children).
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, ChainPartialRemoveI4) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  for (std::uint64_t i = 1; i <= 3; ++i)
    verifier.insert(make_key(enc, 0x42, i), val);
  verifier.assert_node_counts({3, 2, 0, 0, 0});

  verifier.remove(make_key(enc, 0x42, 1));
  verifier.check_present_values();
  // I4(3) → remove → I4(2).  Chain I4 unchanged.
  verifier.assert_node_counts({2, 2, 0, 0, 0});
}

/// Insert 5 keys (→I16), remove 1 (I16 at min_size → shrink to I4).
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, ChainShrinkI16ToI4) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  for (std::uint64_t i = 1; i <= 5; ++i)
    verifier.insert(make_key(enc, 0x42, i), val);
  verifier.assert_node_counts({5, 1, 1, 0, 0});

  verifier.remove(make_key(enc, 0x42, 1));
  verifier.check_present_values();
  // I16(5) at min_size → shrink to I4(4).  Chain I4 + bottom I4.
  verifier.assert_node_counts({4, 2, 0, 0, 0});
  verifier.assert_shrinking_inodes({0, 1, 0, 0});
}

/// Insert 17 keys (→I48), remove 1 (I48 at min_size → shrink to I16).
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, ChainShrinkI48ToI16) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  for (std::uint64_t i = 1; i <= 17; ++i)
    verifier.insert(make_key(enc, 0x42, i), val);
  verifier.assert_node_counts({17, 1, 0, 1, 0});

  verifier.remove(make_key(enc, 0x42, 1));
  verifier.check_present_values();
  // I48(17) at min_size → shrink to I16(16).  Chain I4 + I16.
  verifier.assert_node_counts({16, 1, 1, 0, 0});
  verifier.assert_shrinking_inodes({0, 0, 1, 0});
}

/// Insert 49 keys (→I256), remove 1 (I256 at min_size → shrink to I48).
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, ChainShrinkI256ToI48) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  for (std::uint64_t i = 1; i <= 49; ++i)
    verifier.insert(make_key(enc, 0x42, i), val);
  verifier.assert_node_counts({49, 1, 0, 0, 1});

  verifier.remove(make_key(enc, 0x42, 1));
  verifier.check_present_values();
  // I256(49) at min_size → shrink to I48(48).  Chain I4 + I48.
  verifier.assert_node_counts({48, 1, 0, 1, 0});
  verifier.assert_shrinking_inodes({0, 0, 0, 1});
}

// -------------------------------------------------------------------
// Group 6c: Full remove — all keys removed through each bottom inode
// -------------------------------------------------------------------

/// Insert 3 keys into chain (bottom I4), remove all.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, ChainRemoveAllFromI4) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  for (std::uint64_t i = 1; i <= 3; ++i)
    verifier.insert(make_key(enc, 0x42, i), val);
  for (std::uint64_t i = 1; i <= 3; ++i)
    verifier.remove(make_key(enc, 0x42, i));
  verifier.assert_empty();
}

/// Insert 5 keys into chain (bottom I16), remove all.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, ChainRemoveAllFromI16) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  for (std::uint64_t i = 1; i <= 5; ++i)
    verifier.insert(make_key(enc, 0x42, i), val);
  for (std::uint64_t i = 1; i <= 5; ++i)
    verifier.remove(make_key(enc, 0x42, i));
  verifier.assert_empty();
}

/// Insert 17 keys into chain (bottom I48), remove all.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, ChainRemoveAllFromI48) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  for (std::uint64_t i = 1; i <= 17; ++i)
    verifier.insert(make_key(enc, 0x42, i), val);
  for (std::uint64_t i = 1; i <= 17; ++i)
    verifier.remove(make_key(enc, 0x42, i));
  verifier.assert_empty();
}

/// Insert 49 keys into chain (bottom I256), remove all.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, ChainRemoveAllFromI256) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  for (std::uint64_t i = 1; i <= 49; ++i)
    verifier.insert(make_key(enc, 0x42, i), val);
  for (std::uint64_t i = 1; i <= 49; ++i)
    verifier.remove(make_key(enc, 0x42, i));
  verifier.assert_empty();
}

// -------------------------------------------------------------------
// Group 6d: Cascade — chain under parent at min_size, removing chain
// triggers parent shrinkage
//
// Each test creates a parent inode at its min_size, where one child
// slot points to a chain (2 keys with tag=0x42 sharing 8 bytes) and
// the remaining slots are direct leaves (distinct tag bytes).
// Removing both chain keys should: reclaim the chain, then shrink
// the parent through the normal shrinkage path.
// -------------------------------------------------------------------

/// Chain under I4(2 children).  Remove chain → I4 collapses via
/// leave_last_child → root becomes the surviving leaf.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, CascadeChainUnderI4) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  // Insert chain keys first so the chain forms at root level, then
  // insert a short key that splits the root prefix → parent I4.
  verifier.insert(make_key(enc, 0x42, 1), val);
  verifier.insert(make_key(enc, 0x42, 2), val);
  verifier.insert(make_short_key(enc, 0x01), val);
  // root I4(2: 0x42→chain, 0x01→leaf) + chain I4 + bottom I4 + 3 leaves
  verifier.assert_node_counts({3, 3, 0, 0, 0});

  verifier.remove(make_key(enc, 0x42, 1));
  // Bottom I4 collapsed via leave_last_child.  Chain I4 has 1 child (leaf).
  // Root I4 still has 2 children.
  verifier.assert_node_counts({2, 2, 0, 0, 0});

  verifier.remove(make_key(enc, 0x42, 2));
  verifier.check_present_values();
  // Chain fully reclaimed.  Root I4 at min_size(2) loses a child →
  // leave_last_child → root becomes the surviving leaf.
  verifier.assert_node_counts({1, 0, 0, 0, 0});
}

/// Chain under I16(5 children).  Remove chain → I16 shrinks to I4.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, CascadeChainUnderI16) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  // Chain keys first, then 4 short keys → root I16(5 children).
  verifier.insert(make_key(enc, 0x42, 1), val);
  verifier.insert(make_key(enc, 0x42, 2), val);
  for (std::uint8_t t = 0x01; t <= 0x04; ++t)
    verifier.insert(make_short_key(enc, t), val);
  // root I16(5) + chain I4 + bottom I4 + 6 leaves
  verifier.assert_node_counts({6, 2, 1, 0, 0});

  verifier.remove(make_key(enc, 0x42, 1));
  verifier.remove(make_key(enc, 0x42, 2));
  verifier.check_present_values();
  // Chain reclaimed.  I16(5) → remove chain slot → is_min_size →
  // shrink to I4(4).
  verifier.assert_node_counts({4, 1, 0, 0, 0});
}

/// Chain under I48(17 children).  Remove chain → I48 shrinks to I16.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, CascadeChainUnderI48) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  // Chain keys first, then 16 short keys → root I48(17 children).
  verifier.insert(make_key(enc, 0x42, 1), val);
  verifier.insert(make_key(enc, 0x42, 2), val);
  for (std::uint8_t t = 0x01; t <= 0x10; ++t)
    verifier.insert(make_short_key(enc, t), val);
  // root I48(17) + chain I4 + bottom I4 + 18 leaves
  verifier.assert_node_counts({18, 2, 0, 1, 0});

  verifier.remove(make_key(enc, 0x42, 1));
  verifier.remove(make_key(enc, 0x42, 2));
  verifier.check_present_values();
  // Chain reclaimed.  I48(17) → remove chain slot → shrink to I16(16).
  verifier.assert_node_counts({16, 0, 1, 0, 0});
}

/// Chain under I256(49 children).  Remove chain → I256 shrinks to I48.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, CascadeChainUnderI256) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  // Chain keys first, then 48 short keys → root I256(49 children).
  verifier.insert(make_key(enc, 0x42, 1), val);
  verifier.insert(make_key(enc, 0x42, 2), val);
  for (std::uint8_t t = 0x01; t <= 0x30; ++t)
    verifier.insert(make_short_key(enc, t), val);
  // root I256(49) + chain I4 + bottom I4 + 50 leaves
  verifier.assert_node_counts({50, 2, 0, 0, 1});

  verifier.remove(make_key(enc, 0x42, 1));
  verifier.remove(make_key(enc, 0x42, 2));
  verifier.check_present_values();
  // Chain reclaimed.  I256(49) → remove chain slot → shrink to I48(48).
  verifier.assert_node_counts({48, 0, 0, 1, 0});
}

// -------------------------------------------------------------------
// Group 6e: Multi-level chain removal
// -------------------------------------------------------------------

/// Two 17-byte keys (2 chain I4s + bottom I4), remove both.
UNODB_TYPED_TEST(ARTKeyViewCorrectnessTest, MultiLevelChainRemoveAll) {
  unodb::test::tree_verifier<TypeParam> verifier;
  unodb::key_encoder enc;
  const auto val = unodb::test::test_values[0];

  auto make17 = [&](std::uint8_t last) {
    enc.reset();
    for (unsigned i = 0; i < 16; ++i) enc.encode(std::uint8_t{0xAA});
    enc.encode(last);
    return enc.get_key_view();
  };
  verifier.insert(make17(0x01), val);
  verifier.insert(make17(0x02), val);
  verifier.assert_node_counts({2, 3, 0, 0, 0});

  verifier.remove(make17(0x01));
  // Bottom I4 collapsed.  Two chain I4s remain, last one has 1 child (leaf).
  verifier.assert_node_counts({1, 2, 0, 0, 0});

  verifier.remove(make17(0x02));
  verifier.assert_empty();
}

#endif  // UNODB_DETAIL_WITH_STATS

}  // namespace
