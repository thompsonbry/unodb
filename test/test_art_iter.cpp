// Copyright 2019-2024 Laurynas Biveinis

// IWYU pragma: no_include <array>
// IWYU pragma: no_include <string>
// IWYU pragma: no_include "gtest/gtest.h"

#include "global.hpp"

#include <cstddef>
#include <cstdint>
#include <limits>
#include <stdexcept>
#include <tuple>

#include <gtest/gtest.h>

#include "art.hpp"
#include "art_common.hpp"
#include "db_test_utils.hpp"
#include "gtest_utils.hpp"
#include "mutex_art.hpp"
#include "olc_art.hpp"
#include "test_utils.hpp"
#include "thread_sync.hpp"

namespace {
using unodb::detail::thread_syncs;
using unodb::test::test_values;

// Test suite for an ART iterator.
template <class Db>
class ARTIteratorTest : public ::testing::Test {
 public:
  using Test::Test;
};

using ARTTypes = ::testing::Types<unodb::db>/*, unodb::mutex_db, unodb::olc_db>*/;     // FIXME Restore all ART types.

UNODB_TYPED_TEST_SUITE(ARTIteratorTest, ARTTypes)

UNODB_START_TYPED_TESTS()

//
// FIXME unit tests, etc.
//
// FIXME unit tests for gsl::span<std::byte>
//
// FIXME Thread safety unit tests.
//
// FIXME Develop a thread-safe version of the iterator based on mutex (trivial) and OLC.
//
// FIXME Microbenchmark for parallel scaling with and w/o mutation.
//

// A unit test for an iterator on an empty tree.
TYPED_TEST(ARTIteratorTest, EmptyTree) {
  unodb::test::tree_verifier<TypeParam> verifier;
  verifier.check_absent_keys({0});
  const TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  auto it = db.iterator(); // obtain iterator.
  UNODB_EXPECT_TRUE( ! it.valid() );
  UNODB_EXPECT_TRUE( ! it.get_key() );
  UNODB_EXPECT_TRUE( ! it.get_val() );
  UNODB_EXPECT_TRUE( ! it.next() );
  UNODB_EXPECT_TRUE( ! it.find(0, unodb::find_enum::LTE) );
  UNODB_EXPECT_TRUE( ! it.find(0, unodb::find_enum::EQ) );
  UNODB_EXPECT_TRUE( ! it.find(0, unodb::find_enum::GTE) );
  UNODB_EXPECT_TRUE( ! it.valid() );
  UNODB_EXPECT_TRUE( ! it.find(1, unodb::find_enum::LTE) );
  UNODB_EXPECT_TRUE( ! it.find(1, unodb::find_enum::EQ) );
  UNODB_EXPECT_TRUE( ! it.find(1, unodb::find_enum::GTE) );
  UNODB_EXPECT_TRUE( ! it.valid() );
  UNODB_EXPECT_TRUE( ! it.first() );
  UNODB_EXPECT_TRUE( ! it.valid() );
  UNODB_EXPECT_TRUE( ! it.last() );
  UNODB_EXPECT_TRUE( ! it.valid() );
}

// FIXME Unit test the first() and last() methods for the various node
// types so we can then rely on their correct behavior here.  That
// simplifies the test coverage required to ensure that first(),
// last(), etc. work for any tree structure.
TYPED_TEST(ARTIteratorTest, SingleLeafTree) {
  unodb::test::tree_verifier<TypeParam> verifier;
  verifier.check_absent_keys({1});
  verifier.insert( 1, unodb::test::test_values[1] );
  const TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  auto it = db.iterator(); // obtain iterator.
  // check when iterator is not positioned on any leaf.
  std::cerr<<"Check of initial invalid iterator"<<std::endl;
  UNODB_EXPECT_TRUE( ! it.valid() );
  UNODB_EXPECT_TRUE( ! it.get_key() );
  UNODB_EXPECT_TRUE( ! it.get_val() );
  UNODB_EXPECT_TRUE( ! it.next() );
  // position the iterator on the first leaf and check behavior.
  std::cerr<<"Positioning iterator on first leaf"<<std::endl;
  UNODB_EXPECT_TRUE( it.first() );
  UNODB_EXPECT_TRUE( it.valid() );
  std::cerr<<"Checking key"<<std::endl;
  UNODB_EXPECT_EQ( 1, it.get_key().value() );
  std::cerr<<"Checking val"<<std::endl;
  UNODB_EXPECT_EQ( unodb::test::test_values[1], it.get_val().value() );
  UNODB_EXPECT_TRUE( ! it.next() );
  UNODB_EXPECT_TRUE( it.valid() );
  UNODB_EXPECT_TRUE( ! it.prior() );
  UNODB_EXPECT_TRUE( it.valid() );
  // position the iterator on the last leaf and check behavior.
  std::cerr<<"Positioning iterator on last leaf"<<std::endl;
  UNODB_EXPECT_TRUE( it.last() );
  UNODB_EXPECT_TRUE( it.valid() );
  UNODB_EXPECT_EQ( 1, it.get_key().value() );
  UNODB_EXPECT_EQ( unodb::test::test_values[1], it.get_val().value() );
  UNODB_EXPECT_TRUE( ! it.next() );
  UNODB_EXPECT_TRUE( it.valid() );
  UNODB_EXPECT_TRUE( ! it.prior() );
  UNODB_EXPECT_TRUE( it.valid() );
  // // exact search for [0], not found.
  // std::cerr<<"Exact search for [0] - not found"<<std::endl;
  // UNODB_EXPECT_TRUE( ! it.find(0, find_enum::EQ) );
  // UNODB_EXPECT_TRUE( ! it.valid() );
  // // prefix search for [0], positions on the first key GTE [0], which is [1].
  // std::cerr<<"Prefix search for [0] - found"<<std::endl;
  // UNODB_EXPECT_TRUE( ! it.find(0, find_enum );
  // UNODB_EXPECT_TRUE( ! it.valid() );
  // UNODB_EXPECT_EQ( 1, it.get_key() );
  // UNODB_EXPECT_EQ( unodb::test::test_values[1], it.get_val() );
  // UNODB_EXPECT_TRUE( ! it.next() );
  // UNODB_EXPECT_TRUE( it.valid() );
  // UNODB_EXPECT_TRUE( ! it.prior() );
  // UNODB_EXPECT_TRUE( it.valid() );
  // // exact search for [1], found.
  // std::cerr<<"Exact search for [1] - found"<<std::endl;
  // UNODB_EXPECT_TRUE( ! it.find(1, true/*exact*/) );
  // UNODB_EXPECT_TRUE( it.valid() );
  // UNODB_EXPECT_EQ( 1, it.get_key() );
  // UNODB_EXPECT_EQ( unodb::test::test_values[1], it.get_val() );
  // UNODB_EXPECT_TRUE( ! it.next() );
  // UNODB_EXPECT_TRUE( it.valid() );
  // UNODB_EXPECT_TRUE( ! it.prior() );
  // UNODB_EXPECT_TRUE( it.valid() );
  // // prefix search for first key GTE [1], found.
  // std::cerr<<"Prefix search for [1] - found"<<std::endl;
  // UNODB_EXPECT_TRUE( ! it.find(1, false/*exact*/) );
  // UNODB_EXPECT_TRUE( ! it.valid() );
  // UNODB_EXPECT_EQ( 1, it.get_key() );
  // UNODB_EXPECT_EQ( unodb::test::test_values[1], it.get_val() );
  // UNODB_EXPECT_TRUE( ! it.next() );
  // UNODB_EXPECT_TRUE( it.valid() );
  // UNODB_EXPECT_TRUE( ! it.prior() );
  // UNODB_EXPECT_TRUE( it.valid() );
}

TYPED_TEST(ARTIteratorTest, ThreeLeafTreeForwardScan) {
  unodb::test::tree_verifier<TypeParam> verifier;
  verifier.insert( 0, unodb::test::test_values[0] );
  verifier.insert( 1, unodb::test::test_values[1] );
  verifier.insert( 2, unodb::test::test_values[2] );
  const TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  auto it = db.iterator(); // obtain iterator.
  // check when iterator is not positioned on any leaf.
  std::cerr<<"Check of initial invalid iterator"<<std::endl;
  UNODB_EXPECT_TRUE( ! it.valid() );
  UNODB_EXPECT_TRUE( ! it.get_key() );
  UNODB_EXPECT_TRUE( ! it.get_val() );
  UNODB_EXPECT_TRUE( ! it.next() );
  // position the iterator on the first leaf and do forward scan. 
  std::cerr<<"Positioning iterator on first leaf"<<std::endl;
  UNODB_EXPECT_TRUE( it.first() );
  UNODB_EXPECT_TRUE( it.valid() );
  UNODB_EXPECT_EQ( 0, it.get_key().value() );
  UNODB_EXPECT_EQ( unodb::test::test_values[0], it.get_val().value() );
  // next()
  UNODB_EXPECT_TRUE( it.next() );
  UNODB_EXPECT_TRUE( it.valid() );
  UNODB_EXPECT_EQ( 1, it.get_key().value() );
  UNODB_EXPECT_EQ( unodb::test::test_values[1], it.get_val().value() );
  // next()
  UNODB_EXPECT_TRUE( it.next() );
  UNODB_EXPECT_TRUE( it.valid() );
  UNODB_EXPECT_EQ( 2, it.get_key().value() );
  UNODB_EXPECT_EQ( unodb::test::test_values[2], it.get_val().value() );
  // next() - nothing left.
  UNODB_EXPECT_TRUE( ! it.next() );
  UNODB_EXPECT_TRUE( it.valid() );  // iterator remains valid.
}

// Unit test for a reverse scan starting from the last leaf in the
// index.
TYPED_TEST(ARTIteratorTest, ThreeLeafTreeReverse) {
  unodb::test::tree_verifier<TypeParam> verifier;
  verifier.insert( 0, unodb::test::test_values[0] );
  verifier.insert( 1, unodb::test::test_values[1] );
  verifier.insert( 2, unodb::test::test_values[2] );
  const TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  auto it = db.iterator(); // obtain iterator.
  // check when iterator is not positioned on any leaf.
  std::cerr<<"Check of initial invalid iterator"<<std::endl;
  UNODB_EXPECT_TRUE( ! it.valid() );
  UNODB_EXPECT_TRUE( ! it.get_key() );
  UNODB_EXPECT_TRUE( ! it.get_val() );
  UNODB_EXPECT_TRUE( ! it.next() );
  // position the iterator on the last leaf and do reverse scan. 
  std::cerr<<"Positioning iterator on last leaf"<<std::endl;
  UNODB_EXPECT_TRUE( it.last() );
  UNODB_EXPECT_TRUE( it.valid() );
  UNODB_EXPECT_EQ( 2, it.get_key().value() );
  UNODB_EXPECT_EQ( unodb::test::test_values[2], it.get_val().value() );
  // prior()
  UNODB_EXPECT_TRUE( it.prior() );
  UNODB_EXPECT_TRUE( it.valid() );
  UNODB_EXPECT_EQ( 1, it.get_key().value() );
  UNODB_EXPECT_EQ( unodb::test::test_values[1], it.get_val().value() );
  // prior()
  UNODB_EXPECT_TRUE( it.prior() );
  UNODB_EXPECT_TRUE( it.valid() );
  UNODB_EXPECT_EQ( 0, it.get_key().value() );
  UNODB_EXPECT_EQ( unodb::test::test_values[0], it.get_val().value() );
  // prior() - nothing left.
  UNODB_EXPECT_TRUE( ! it.prior() );
  UNODB_EXPECT_TRUE( it.valid() );  // iterator remains valid.
}

TYPED_TEST(ARTIteratorTest, ThreeLeafTreeFindEQ) {
  unodb::test::tree_verifier<TypeParam> verifier;
  verifier.insert( 0, unodb::test::test_values[0] );
  verifier.insert( 1, unodb::test::test_values[1] );
  verifier.insert( 2, unodb::test::test_values[2] );
  const TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  auto it = db.iterator(); // obtain iterator.
  // find [0]
  UNODB_EXPECT_TRUE( it.find( 0, unodb::find_enum::EQ ) );
  UNODB_EXPECT_TRUE( it.valid() );
  UNODB_EXPECT_EQ( 0, it.get_key().value() );
  UNODB_EXPECT_EQ( unodb::test::test_values[0], it.get_val().value() );
  // find [1]
  UNODB_EXPECT_TRUE( it.find( 1, unodb::find_enum::EQ ) );
  UNODB_EXPECT_TRUE( it.valid() );
  UNODB_EXPECT_EQ( 1, it.get_key().value() );
  UNODB_EXPECT_EQ( unodb::test::test_values[1], it.get_val().value() );
  // find [2]
  UNODB_EXPECT_TRUE( it.find( 2, unodb::find_enum::EQ ) );
  UNODB_EXPECT_TRUE( it.valid() );
  UNODB_EXPECT_EQ( 2, it.get_key().value() );
  UNODB_EXPECT_EQ( unodb::test::test_values[2], it.get_val().value() );
  // find [3] - fails.
  UNODB_EXPECT_TRUE( ! it.find( 3, unodb::find_enum::EQ ) );
  UNODB_EXPECT_TRUE( ! it.valid() );
}

TYPED_TEST(ARTIteratorTest, ThreeLeafTreeFindLTE) {
  FAIL()<<"Write test for find(LTE)";
}

TYPED_TEST(ARTIteratorTest, ThreeLeafTreeFindGTE) {
  FAIL()<<"Write test for find(GTE)";
}

// TYPED_TEST(ARTCorrectnessTest, SingleNodeTreeNonemptyValue) {
//   unodb::test::tree_verifier<TypeParam> verifier;
//   verifier.insert(1, unodb::test::test_values[2]);
//   verifier.assert_node_counts({1, 0, 0, 0, 0});
//   verifier.assert_growing_inodes({0, 0, 0, 0});

//   verifier.check_present_values();
//   verifier.check_absent_keys({0, 2});
// }

// UNODB_DETAIL_DISABLE_MSVC_WARNING(6326)
// TYPED_TEST(ARTCorrectnessTest, TooLongValue) {
//   constexpr std::byte fake_val{0x00};
//   const unodb::value_view too_long{
//       &fake_val,
//       static_cast<std::uint64_t>(std::numeric_limits<std::uint32_t>::max()) +
//           1U};

//   unodb::test::tree_verifier<TypeParam> verifier;

//   UNODB_ASSERT_THROW(std::ignore = verifier.get_db().insert(1, too_long),
//                      std::length_error);

//   verifier.check_absent_keys({1});
//   verifier.assert_empty();
//   verifier.assert_growing_inodes({0, 0, 0, 0});
// }
// UNODB_DETAIL_RESTORE_MSVC_WARNINGS()

// TYPED_TEST(ARTCorrectnessTest, ExpandLeafToNode4) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert(0, unodb::test::test_values[1]);
//   verifier.assert_node_counts({1, 0, 0, 0, 0});
//   verifier.assert_growing_inodes({0, 0, 0, 0});

//   verifier.insert(1, unodb::test::test_values[2]);
//   verifier.assert_node_counts({2, 1, 0, 0, 0});
//   verifier.assert_growing_inodes({1, 0, 0, 0});

//   verifier.check_present_values();
//   verifier.check_absent_keys({2});
// }

// UNODB_DETAIL_DISABLE_MSVC_WARNING(6326)
// TYPED_TEST(ARTCorrectnessTest, DuplicateKey) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert(0, unodb::test::test_values[0]);
//   verifier.assert_node_counts({1, 0, 0, 0, 0});

//   const auto mem_use_before = verifier.get_db().get_current_memory_use();
//   unodb::test::must_not_allocate([&verifier] {
//     UNODB_ASSERT_FALSE(
//         verifier.get_db().insert(0, unodb::test::test_values[3]));
//   });
//   UNODB_EXPECT_EQ(mem_use_before, verifier.get_db().get_current_memory_use());

//   verifier.assert_node_counts({1, 0, 0, 0, 0});
//   verifier.assert_growing_inodes({0, 0, 0, 0});
//   verifier.check_present_values();
// }
// UNODB_DETAIL_RESTORE_MSVC_WARNINGS()

// TYPED_TEST(ARTCorrectnessTest, InsertToFullNode4) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert_key_range(0, 4);
//   verifier.assert_node_counts({4, 1, 0, 0, 0});
//   verifier.assert_growing_inodes({1, 0, 0, 0});

//   verifier.check_present_values();
//   verifier.check_absent_keys({5, 4});
// }

// TYPED_TEST(ARTCorrectnessTest, Node4InsertFFByte) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert_key_range(0xFC, 4);

//   verifier.assert_node_counts({4, 1, 0, 0, 0});
//   verifier.assert_growing_inodes({1, 0, 0, 0});
//   verifier.check_present_values();
//   verifier.check_absent_keys({0, 0xFB});
// }

// TYPED_TEST(ARTCorrectnessTest, TwoNode4) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert(1, unodb::test::test_values[0]);
//   verifier.insert(3, unodb::test::test_values[2]);
//   verifier.assert_growing_inodes({1, 0, 0, 0});

//   // Insert a value that does not share full prefix with the current Node4
//   verifier.insert(0xFF01, unodb::test::test_values[3]);
//   verifier.assert_node_counts({3, 2, 0, 0, 0});
//   verifier.assert_growing_inodes({2, 0, 0, 0});
//   verifier.assert_key_prefix_splits(1);

//   verifier.check_present_values();
//   verifier.check_absent_keys({0xFF00, 2});
// }

// TYPED_TEST(ARTCorrectnessTest, DbInsertNodeRecursion) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert(1, unodb::test::test_values[0]);
//   verifier.insert(3, unodb::test::test_values[2]);
//   // Insert a value that does not share full prefix with the current Node4
//   verifier.insert(0xFF0001, unodb::test::test_values[3]);
//   verifier.assert_growing_inodes({2, 0, 0, 0});
//   verifier.assert_key_prefix_splits(1);

//   // Then insert a value that shares full prefix with the above node and will
//   // ask for a recursive insertion there
//   verifier.insert(0xFF0101, unodb::test::test_values[1]);
//   verifier.assert_node_counts({4, 3, 0, 0, 0});
//   verifier.assert_growing_inodes({3, 0, 0, 0});
//   verifier.assert_key_prefix_splits(1);

//   verifier.check_present_values();
//   verifier.check_absent_keys({0xFF0100, 0xFF0000, 2});
// }

// TYPED_TEST(ARTCorrectnessTest, Node16) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert_key_range(0, 4);
//   verifier.check_present_values();
//   verifier.insert(5, unodb::test::test_values[0]);
//   verifier.assert_node_counts({5, 0, 1, 0, 0});
//   verifier.assert_growing_inodes({1, 1, 0, 0});

//   verifier.check_present_values();
//   verifier.check_absent_keys({6, 0x0100, 0xFFFFFFFFFFFFFFFFULL});
// }

// TYPED_TEST(ARTCorrectnessTest, FullNode16) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert_key_range(0, 16);
//   verifier.assert_node_counts({16, 0, 1, 0, 0});
//   verifier.assert_growing_inodes({1, 1, 0, 0});

//   verifier.check_absent_keys({16});
//   verifier.check_present_values();
// }

// TYPED_TEST(ARTCorrectnessTest, Node16KeyPrefixSplit) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert_key_range(10, 5);

//   // Insert a value that does share full prefix with the current Node16
//   verifier.insert(0x1020, unodb::test::test_values[0]);
//   verifier.assert_node_counts({6, 1, 1, 0, 0});
//   verifier.assert_growing_inodes({2, 1, 0, 0});
//   verifier.assert_key_prefix_splits(1);

//   verifier.check_present_values();
//   verifier.check_absent_keys({9, 0x10FF});
// }

// TYPED_TEST(ARTCorrectnessTest, Node16KeyInsertOrderDescending) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert(5, unodb::test::test_values[0]);
//   verifier.insert(4, unodb::test::test_values[1]);
//   verifier.insert(3, unodb::test::test_values[2]);
//   verifier.insert(2, unodb::test::test_values[3]);
//   verifier.insert(1, unodb::test::test_values[4]);
//   verifier.insert(0, unodb::test::test_values[0]);
//   verifier.assert_node_counts({6, 0, 1, 0, 0});

//   verifier.check_present_values();
//   verifier.check_absent_keys({6});
// }

// TYPED_TEST(ARTCorrectnessTest, Node16ConstructWithFFKeyByte) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert_key_range(0xFB, 4);
//   verifier.assert_node_counts({4, 1, 0, 0, 0});

//   verifier.insert(0xFF, unodb::test::test_values[0]);

//   verifier.assert_node_counts({5, 0, 1, 0, 0});
//   verifier.assert_growing_inodes({1, 1, 0, 0});

//   verifier.check_present_values();
//   verifier.check_absent_keys({0, 0xFA});
// }

// TYPED_TEST(ARTCorrectnessTest, Node48) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert_key_range(0, 17);
//   verifier.assert_node_counts({17, 0, 0, 1, 0});
//   verifier.assert_growing_inodes({1, 1, 1, 0});

//   verifier.check_present_values();
//   verifier.check_absent_keys({17});
// }

// TYPED_TEST(ARTCorrectnessTest, FullNode48) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert_key_range(0, 48);
//   verifier.assert_node_counts({48, 0, 0, 1, 0});
//   verifier.assert_growing_inodes({1, 1, 1, 0});

//   verifier.check_present_values();
//   verifier.check_absent_keys({49});
// }

// TYPED_TEST(ARTCorrectnessTest, Node48KeyPrefixSplit) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert_key_range(10, 17);
//   verifier.assert_node_counts({17, 0, 0, 1, 0});
//   verifier.assert_growing_inodes({1, 1, 1, 0});
//   verifier.assert_key_prefix_splits(0);

//   // Insert a value that does share full prefix with the current Node48
//   verifier.insert(0x100020, unodb::test::test_values[0]);
//   verifier.assert_node_counts({18, 1, 0, 1, 0});
//   verifier.assert_growing_inodes({2, 1, 1, 0});
//   verifier.assert_key_prefix_splits(1);

//   verifier.check_present_values();
//   verifier.check_absent_keys({9, 27, 0x100019, 0x100100, 0x110000});
// }

// TYPED_TEST(ARTCorrectnessTest, Node256) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert_key_range(1, 49);
//   verifier.assert_node_counts({49, 0, 0, 0, 1});
//   verifier.assert_growing_inodes({1, 1, 1, 1});

//   verifier.check_present_values();
//   verifier.check_absent_keys({50});
// }

// TYPED_TEST(ARTCorrectnessTest, FullNode256) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert_key_range(0, 256);
//   verifier.assert_node_counts({256, 0, 0, 0, 1});
//   verifier.assert_growing_inodes({1, 1, 1, 1});

//   verifier.check_present_values();
//   verifier.check_absent_keys({256});
// }

// TYPED_TEST(ARTCorrectnessTest, Node256KeyPrefixSplit) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert_key_range(20, 49);
//   verifier.assert_node_counts({49, 0, 0, 0, 1});
//   verifier.assert_growing_inodes({1, 1, 1, 1});
//   verifier.assert_key_prefix_splits(0);

//   // Insert a value that does share full prefix with the current Node256
//   verifier.insert(0x100020, unodb::test::test_values[0]);
//   verifier.assert_node_counts({50, 1, 0, 0, 1});
//   verifier.assert_growing_inodes({2, 1, 1, 1});
//   verifier.assert_key_prefix_splits(1);

//   verifier.check_present_values();
//   verifier.check_absent_keys({19, 69, 0x100019, 0x100100, 0x110000});
// }

// TYPED_TEST(ARTCorrectnessTest, TryDeleteFromEmpty) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   unodb::test::must_not_allocate(
//       [&verifier] { verifier.attempt_remove_missing_keys({1}); });

//   verifier.assert_empty();
//   verifier.check_absent_keys({1});
// }

// TYPED_TEST(ARTCorrectnessTest, SingleNodeTreeDelete) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert(1, unodb::test::test_values[0]);

//   unodb::test::must_not_allocate([&verifier] { verifier.remove(1); });

//   verifier.assert_empty();
//   verifier.check_absent_keys({1});
//   verifier.attempt_remove_missing_keys({1});
//   verifier.check_absent_keys({1});
// }

// TYPED_TEST(ARTCorrectnessTest, SingleNodeTreeAttemptDeleteAbsent) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert(2, unodb::test::test_values[1]);

//   unodb::test::must_not_allocate([&verifier] {
//     verifier.attempt_remove_missing_keys({1, 3, 0xFF02});
//   });

//   verifier.check_present_values();
//   verifier.assert_node_counts({1, 0, 0, 0, 0});
//   verifier.check_absent_keys({1, 3, 0xFF02});
// }

// TYPED_TEST(ARTCorrectnessTest, Node4AttemptDeleteAbsent) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert_key_range(1, 4);

//   unodb::test::must_not_allocate([&verifier] {
//     verifier.attempt_remove_missing_keys({0, 6, 0xFF000001});
//   });

//   verifier.assert_node_counts({4, 1, 0, 0, 0});

//   verifier.check_absent_keys({0, 6, 0xFF00000});
// }

// TYPED_TEST(ARTCorrectnessTest, Node4FullDeleteMiddleAndBeginning) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert_key_range(1, 4);

//   // Delete from Node4 middle
//   unodb::test::must_not_allocate([&verifier] { verifier.remove(2); });

//   verifier.check_present_values();
//   verifier.check_absent_keys({0, 2, 5});

//   // Delete from Node4 beginning
//   unodb::test::must_not_allocate([&verifier] { verifier.remove(1); });

//   verifier.check_present_values();
//   verifier.check_absent_keys({1, 0, 2, 5});

//   verifier.assert_node_counts({2, 1, 0, 0, 0});
// }

// TYPED_TEST(ARTCorrectnessTest, Node4FullDeleteEndAndMiddle) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert_key_range(1, 4);

//   // Delete from Node4 end
//   unodb::test::must_not_allocate([&verifier] { verifier.remove(4); });

//   verifier.check_present_values();
//   verifier.check_absent_keys({4, 0, 5});

//   // Delete from Node4 middle
//   unodb::test::must_not_allocate([&verifier] { verifier.remove(2); });

//   verifier.check_present_values();
//   verifier.check_absent_keys({2, 4, 0, 5});

//   verifier.assert_node_counts({2, 1, 0, 0, 0});
// }

// TYPED_TEST(ARTCorrectnessTest, Node4ShrinkToSingleLeaf) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert_key_range(1, 2);
//   verifier.assert_shrinking_inodes({0, 0, 0, 0});

//   unodb::test::must_not_allocate([&verifier] { verifier.remove(1); });

//   verifier.assert_shrinking_inodes({1, 0, 0, 0});
//   verifier.check_present_values();
//   verifier.check_absent_keys({1});
//   verifier.assert_node_counts({1, 0, 0, 0, 0});
// }

// TYPED_TEST(ARTCorrectnessTest, Node4DeleteLowerNode) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert_key_range(0, 2);
//   // Insert a value that does not share full prefix with the current Node4
//   verifier.insert(0xFF00, unodb::test::test_values[3]);
//   verifier.assert_shrinking_inodes({0, 0, 0, 0});
//   verifier.assert_key_prefix_splits(1);

//   // Make the lower Node4 shrink to a single value leaf
//   unodb::test::must_not_allocate([&verifier] { verifier.remove(0); });

//   verifier.assert_shrinking_inodes({1, 0, 0, 0});
//   verifier.assert_key_prefix_splits(1);

//   verifier.check_present_values();
//   verifier.check_absent_keys({0, 2, 0xFF01});
//   verifier.assert_node_counts({2, 1, 0, 0, 0});
// }

// TYPED_TEST(ARTCorrectnessTest, Node4DeleteKeyPrefixMerge) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert_key_range(0x8001, 2);
//   // Insert a value that does not share full prefix with the current Node4
//   verifier.insert(0x90AA, unodb::test::test_values[3]);
//   verifier.assert_key_prefix_splits(1);
//   verifier.assert_node_counts({3, 2, 0, 0, 0});

//   // And delete it
//   unodb::test::must_not_allocate([&verifier] { verifier.remove(0x90AA); });

//   verifier.assert_key_prefix_splits(1);
//   verifier.assert_node_counts({2, 1, 0, 0, 0});
//   verifier.assert_shrinking_inodes({1, 0, 0, 0});
//   verifier.check_present_values();
//   verifier.check_absent_keys({0x90AA, 0x8003});
// }

// TYPED_TEST(ARTCorrectnessTest, Node4DeleteKeyPrefixMerge2) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert(0x0000000003020102, unodb::test::test_values[0]);
//   verifier.insert(0x0000000003030302, unodb::test::test_values[1]);
//   verifier.insert(0x0000000100010102, unodb::test::test_values[2]);

//   unodb::test::must_not_allocate([&verifier] {
//     verifier.remove(0x0000000100010102);
//     verifier.remove(0x0000000003020102);
//   });

//   verifier.check_present_values();
// }

// TYPED_TEST(ARTCorrectnessTest, Node16DeleteBeginningMiddleEnd) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert_key_range(1, 16);

//   unodb::test::must_not_allocate([&verifier] {
//     verifier.remove(5);
//     verifier.remove(1);
//     verifier.remove(16);
//   });

//   verifier.check_present_values();
//   verifier.check_absent_keys({0, 1, 5, 16, 17});
//   verifier.assert_node_counts({13, 0, 1, 0, 0});
// }

// TYPED_TEST(ARTCorrectnessTest, Node16ShrinkToNode4DeleteMiddle) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert_key_range(1, 5);
//   verifier.assert_node_counts({5, 0, 1, 0, 0});

//   verifier.remove(2);
//   verifier.assert_shrinking_inodes({0, 1, 0, 0});
//   verifier.assert_node_counts({4, 1, 0, 0, 0});

//   verifier.check_present_values();
//   verifier.check_absent_keys({0, 2, 6});
// }

// TYPED_TEST(ARTCorrectnessTest, Node16ShrinkToNode4DeleteBeginning) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert_key_range(1, 5);
//   verifier.assert_node_counts({5, 0, 1, 0, 0});

//   verifier.remove(1);
//   verifier.assert_shrinking_inodes({0, 1, 0, 0});
//   verifier.assert_node_counts({4, 1, 0, 0, 0});

//   verifier.check_present_values();
//   verifier.check_absent_keys({0, 1, 6});
// }

// TYPED_TEST(ARTCorrectnessTest, Node16ShrinkToNode4DeleteEnd) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert_key_range(1, 5);
//   verifier.assert_node_counts({5, 0, 1, 0, 0});

//   verifier.remove(5);
//   verifier.assert_shrinking_inodes({0, 1, 0, 0});
//   verifier.assert_node_counts({4, 1, 0, 0, 0});

//   verifier.check_present_values();
//   verifier.check_absent_keys({0, 5, 6});
// }

// TYPED_TEST(ARTCorrectnessTest, Node16KeyPrefixMerge) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert_key_range(10, 5);
//   // Insert a value that does not share full prefix with the current Node16
//   verifier.insert(0x1020, unodb::test::test_values[0]);
//   verifier.assert_node_counts({6, 1, 1, 0, 0});
//   verifier.assert_key_prefix_splits(1);

//   // And delete it, so that upper level Node4 key prefix gets merged with
//   // Node16 one
//   unodb::test::must_not_allocate([&verifier] { verifier.remove(0x1020); });

//   verifier.assert_shrinking_inodes({1, 0, 0, 0});
//   verifier.assert_node_counts({5, 0, 1, 0, 0});
//   verifier.check_present_values();
//   verifier.check_absent_keys({9, 16, 0x1020});
// }

// TYPED_TEST(ARTCorrectnessTest, Node48DeleteBeginningMiddleEnd) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert_key_range(1, 48);

//   unodb::test::must_not_allocate([&verifier] {
//     verifier.remove(30);
//     verifier.remove(48);
//     verifier.remove(1);
//   });

//   verifier.check_present_values();
//   verifier.check_absent_keys({0, 1, 30, 48, 49});
//   verifier.assert_node_counts({45, 0, 0, 1, 0});
// }

// TYPED_TEST(ARTCorrectnessTest, Node48ShrinkToNode16DeleteMiddle) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert_key_range(0x80, 17);
//   verifier.assert_node_counts({17, 0, 0, 1, 0});

//   verifier.remove(0x85);
//   verifier.assert_shrinking_inodes({0, 0, 1, 0});
//   verifier.assert_node_counts({16, 0, 1, 0, 0});

//   verifier.check_present_values();
//   verifier.check_absent_keys({0x7F, 0x85, 0x91});
// }

// TYPED_TEST(ARTCorrectnessTest, Node48ShrinkToNode16DeleteBeginning) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert_key_range(1, 17);
//   verifier.assert_node_counts({17, 0, 0, 1, 0});

//   verifier.remove(1);
//   verifier.assert_shrinking_inodes({0, 0, 1, 0});
//   verifier.assert_node_counts({16, 0, 1, 0, 0});

//   verifier.check_present_values();
//   verifier.check_absent_keys({0, 1, 18});
// }

// TYPED_TEST(ARTCorrectnessTest, Node48ShrinkToNode16DeleteEnd) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert_key_range(1, 17);
//   verifier.assert_node_counts({17, 0, 0, 1, 0});

//   verifier.remove(17);
//   verifier.assert_shrinking_inodes({0, 0, 1, 0});
//   verifier.assert_node_counts({16, 0, 1, 0, 0});

//   verifier.check_present_values();
//   verifier.check_absent_keys({0, 17, 18});
// }

// TYPED_TEST(ARTCorrectnessTest, Node48KeyPrefixMerge) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert_key_range(10, 17);
//   // Insert a value that does not share full prefix with the current Node48
//   verifier.insert(0x2010, unodb::test::test_values[1]);
//   verifier.assert_node_counts({18, 1, 0, 1, 0});

//   // And delete it, so that upper level Node4 key prefix gets merged with
//   // Node48 one
//   unodb::test::must_not_allocate([&verifier] { verifier.remove(0x2010); });

//   verifier.assert_shrinking_inodes({1, 0, 0, 0});
//   verifier.assert_node_counts({17, 0, 0, 1, 0});

//   verifier.check_present_values();
//   verifier.check_absent_keys({9, 0x2010, 28});
// }

// TYPED_TEST(ARTCorrectnessTest, Node256DeleteBeginningMiddleEnd) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert_key_range(1, 256);

//   unodb::test::must_not_allocate([&verifier] {
//     verifier.remove(180);
//     verifier.remove(1);
//     verifier.remove(256);
//   });

//   verifier.check_present_values();
//   verifier.check_absent_keys({0, 1, 180, 256});
//   verifier.assert_node_counts({253, 0, 0, 0, 1});
// }

// TYPED_TEST(ARTCorrectnessTest, Node256ShrinkToNode48DeleteMiddle) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert_key_range(1, 49);
//   verifier.assert_node_counts({49, 0, 0, 0, 1});

//   verifier.remove(25);
//   verifier.assert_shrinking_inodes({0, 0, 0, 1});
//   verifier.assert_node_counts({48, 0, 0, 1, 0});

//   verifier.check_present_values();
//   verifier.check_absent_keys({0, 25, 50});
// }

// TYPED_TEST(ARTCorrectnessTest, Node256ShrinkToNode48DeleteBeginning) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert_key_range(1, 49);
//   verifier.assert_node_counts({49, 0, 0, 0, 1});

//   verifier.remove(1);
//   verifier.assert_shrinking_inodes({0, 0, 0, 1});
//   verifier.assert_node_counts({48, 0, 0, 1, 0});

//   verifier.check_present_values();
//   verifier.check_absent_keys({0, 1, 50});
// }

// TYPED_TEST(ARTCorrectnessTest, Node256ShrinkToNode48DeleteEnd) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert_key_range(1, 49);
//   verifier.assert_node_counts({49, 0, 0, 0, 1});

//   verifier.remove(49);
//   verifier.assert_shrinking_inodes({0, 0, 0, 1});
//   verifier.assert_node_counts({48, 0, 0, 1, 0});

//   verifier.check_present_values();
//   verifier.check_absent_keys({0, 49, 50});
// }

// TYPED_TEST(ARTCorrectnessTest, Node256KeyPrefixMerge) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert_key_range(10, 49);
//   // Insert a value that does not share full prefix with the current Node256
//   verifier.insert(0x2010, unodb::test::test_values[1]);
//   verifier.assert_node_counts({50, 1, 0, 0, 1});

//   // And delete it, so that upper level Node4 key prefix gets merged with
//   // Node256 one
//   unodb::test::must_not_allocate([&verifier] { verifier.remove(0x2010); });

//   verifier.assert_shrinking_inodes({1, 0, 0, 0});
//   verifier.assert_node_counts({49, 0, 0, 0, 1});
//   verifier.check_present_values();
//   verifier.check_absent_keys({9, 0x2010, 60});
// }

// TYPED_TEST(ARTCorrectnessTest, MissingKeyWithPresentPrefix) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert(0x010000, unodb::test::test_values[0]);
//   verifier.insert(0x000001, unodb::test::test_values[1]);
//   verifier.insert(0x010001, unodb::test::test_values[2]);

//   unodb::test::must_not_allocate([&verifier] {
//     verifier.attempt_remove_missing_keys({0x000002, 0x010100, 0x010002});
//   });
// }

// TYPED_TEST(ARTCorrectnessTest, MissingKeyMatchingInodePath) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert(0x0100, unodb::test::test_values[0]);
//   verifier.insert(0x0200, unodb::test::test_values[1]);

//   unodb::test::must_not_allocate([&verifier] {
//     verifier.attempt_remove_missing_keys({0x0101, 0x0202});
//   });
// }

// UNODB_DETAIL_DISABLE_MSVC_WARNING(6326)
// TYPED_TEST(ARTCorrectnessTest, MemoryAccountingDuplicateKeyInsert) {
//   unodb::test::tree_verifier<TypeParam> verifier;
//   verifier.insert(0, unodb::test::test_values[0]);
//   unodb::test::must_not_allocate([&verifier] {
//     UNODB_ASSERT_FALSE(
//         verifier.get_db().insert(0, unodb::test::test_values[1]));
//   });
//   verifier.remove(0);
//   UNODB_EXPECT_EQ(verifier.get_db().get_current_memory_use(), 0);
// }
// UNODB_DETAIL_RESTORE_MSVC_WARNINGS()

// TYPED_TEST(ARTCorrectnessTest, Node48InsertIntoDeletedSlot) {
//   unodb::test::tree_verifier<TypeParam> verifier;
//   verifier.insert(16865361447928765957ULL, unodb::test::test_values[0]);
//   verifier.insert(7551546784238320931ULL, test_values[1]);
//   verifier.insert(10913915230368519832ULL, test_values[2]);
//   verifier.insert(3754602112003529886ULL, test_values[3]);
//   verifier.insert(15202487832924025715ULL, test_values[4]);
//   verifier.insert(501264303707694295ULL, test_values[0]);
//   verifier.insert(9228847637821057196ULL, test_values[1]);
//   verifier.insert(4772373217231458680ULL, test_values[2]);
//   verifier.insert(10396278540561456315ULL, test_values[3]);
//   verifier.insert(16646085826334346534ULL, test_values[4]);
//   verifier.insert(3854084731240466350ULL, test_values[0]);
//   verifier.insert(12957550352669724359ULL, test_values[1]);
//   verifier.insert(6583227679421302512ULL, test_values[2]);
//   verifier.insert(6829398721825682578ULL, test_values[3]);
//   verifier.insert(11455392605080430684ULL, test_values[4]);
//   verifier.insert(10176313584012002900ULL, test_values[0]);
//   verifier.insert(13700634388772836888ULL, test_values[1]);
//   verifier.insert(17872125209760305988ULL, test_values[2]);

//   unodb::test::must_not_allocate(
//       [&verifier] { verifier.remove(6583227679421302512ULL); });
//   verifier.insert(0, test_values[0]);

//   verifier.check_present_values();
//   verifier.assert_node_counts({18, 0, 0, 1, 0});
// }

// TYPED_TEST(ARTCorrectnessTest, ClearOnEmpty) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   unodb::test::must_not_allocate([&verifier] { verifier.clear(); });

//   verifier.assert_node_counts({0, 0, 0, 0, 0});
// }

// TYPED_TEST(ARTCorrectnessTest, Clear) {
//   unodb::test::tree_verifier<TypeParam> verifier;

//   verifier.insert(1, test_values[0]);
//   verifier.assert_node_counts({1, 0, 0, 0, 0});

//   unodb::test::must_not_allocate([&verifier] { verifier.clear(); });

//   verifier.check_absent_keys({1});
//   verifier.assert_node_counts({0, 0, 0, 0, 0});
// }

// TYPED_TEST(ARTCorrectnessTest, TwoInstances) {
//   unodb::test::tree_verifier<TypeParam> v1;
//   unodb::test::tree_verifier<TypeParam> v2;

//   unodb::test::thread<TypeParam> second_thread([&v2] {
//     thread_syncs[0].notify();
//     thread_syncs[1].wait();

//     v2.insert(0, unodb::test::test_values[0]);
//     v2.check_present_values();
//   });

//   thread_syncs[0].wait();
//   thread_syncs[1].notify();

//   v1.insert(0, unodb::test::test_values[1]);
//   v1.check_present_values();

//   second_thread.join();
// }

UNODB_END_TESTS()

}  // namespace
