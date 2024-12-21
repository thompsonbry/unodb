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
// FIXME Extend [verifier] to support scans.
//
// FIXME unit tests for gsl::span<std::byte>
//
// FIXME Microbenchmarks for iterator.
//
// FIXME Develop a thread-safe version of the iterator based on mutex (trivial) and OLC and extend microbenchmarks and unit tests
//
// FIXME Microbenchmark for parallel scaling with and w/o mutation.
//

// unit test with an empty tree.
TYPED_TEST(ARTIteratorTest, empty_tree) {
  unodb::test::tree_verifier<TypeParam> verifier;
  verifier.check_absent_keys({0});
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  auto b = db.begin(); // obtain iterators.
  const auto e = db.end();
  UNODB_EXPECT_TRUE( b == e );
  UNODB_EXPECT_TRUE( ! b.get_key() );
  UNODB_EXPECT_TRUE( ! b.get_val() );
}

// unit test where the root is a single leaf.
TYPED_TEST(ARTIteratorTest, single_leaf_iterator_one_value) {
  unodb::test::tree_verifier<TypeParam> verifier;
  verifier.check_absent_keys({0});
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert( 0, unodb::test::test_values[0] );
  auto b = db.begin(); // obtain iterators.
  const auto e = db.end();
  UNODB_EXPECT_TRUE( b != e );
  UNODB_EXPECT_TRUE( b.get_key() && b.get_key().value() == 0 );
  UNODB_EXPECT_TRUE( b.get_val() && b.get_val().value() == unodb::test::test_values[0] );
  UNODB_EXPECT_TRUE( b.next() == e ); // nothing more in the iterator.
}

// unit test where the root is an I4 with two leafs under it.
TYPED_TEST(ARTIteratorTest, I4_and_two_leaves) {
  unodb::test::tree_verifier<TypeParam> verifier;
  verifier.check_absent_keys({0});
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert( 0, unodb::test::test_values[0] );
  verifier.insert( 1, unodb::test::test_values[1] );
  //std::cerr<<"db state::\n"; db.dump(std::cerr);
  auto b = db.begin(); // obtain iterators.
  const auto e = db.end();
  UNODB_EXPECT_TRUE( b != e );
  //std::cerr<<"begin()::\n"; b.dump(std::cerr);
  UNODB_EXPECT_TRUE( b.get_key() && b.get_key().value() == 0 );
  UNODB_EXPECT_TRUE( b.get_val() && b.get_val().value() == unodb::test::test_values[0] );
  UNODB_EXPECT_TRUE( b.next() != e );
  //std::cerr<<"b.next()::\n"; b.dump(std::cerr);
  UNODB_EXPECT_TRUE( b.get_key() && b.get_key().value() == 1 );
  UNODB_EXPECT_TRUE( b.get_val() && b.get_val().value() == unodb::test::test_values[1] );
  UNODB_EXPECT_TRUE( b.next() == e ); // nothing more in the iterator.
  //std::cerr<<"b.next()::\n"; b.dump(std::cerr);
}

// unit test for the following tree structure, which is setup by how we choose the keys.
//
//       I4
//   I4     L2
// L0 L1
TYPED_TEST(ARTIteratorTest, iterator_three_values_left_axis_two_deep_right_axis_one_deep) {
  unodb::test::tree_verifier<TypeParam> verifier;
  verifier.check_absent_keys({0});
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert( 0xaa00, unodb::test::test_values[0] );
  verifier.insert( 0xaa01, unodb::test::test_values[1] );
  verifier.insert( 0xab00, unodb::test::test_values[2] );
  auto b = db.begin(); // obtain iterators.
  const auto e = db.end();
  UNODB_EXPECT_TRUE( b != e );
  UNODB_EXPECT_TRUE( b.get_key() && b.get_key().value() == 0xaa00 );
  UNODB_EXPECT_TRUE( b.get_val() && b.get_val().value() == unodb::test::test_values[0] );
  UNODB_EXPECT_TRUE( b.next() != e );
  UNODB_EXPECT_TRUE( b.get_key() && b.get_key().value() == 0xaa01 );
  UNODB_EXPECT_TRUE( b.get_val() && b.get_val().value() == unodb::test::test_values[1] );
  UNODB_EXPECT_TRUE( b.next() != e );
  UNODB_EXPECT_TRUE( b.get_key() && b.get_key().value() == 0xab00 );
  UNODB_EXPECT_TRUE( b.get_val() && b.get_val().value() == unodb::test::test_values[2] );
  UNODB_EXPECT_TRUE( b.next() == e ); // nothing more in the iterator.
}

// unit test for the following tree structure, which is setup by how we choose the keys.
//
//       I4
//   L0     I4
//        L1 L2
TYPED_TEST(ARTIteratorTest, single_node_iterators_three_values_left_axis_one_deep_right_axis_two_deep) {
  unodb::test::tree_verifier<TypeParam> verifier;
  verifier.check_absent_keys({0});
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert( 0xaa00, unodb::test::test_values[0] );
  verifier.insert( 0xab0c, unodb::test::test_values[1] );
  verifier.insert( 0xab0d, unodb::test::test_values[2] );
  auto b = db.begin(); // obtain iterators.
  const auto e = db.end();
  UNODB_EXPECT_TRUE( b != e );
  UNODB_EXPECT_TRUE( b.get_key() && b.get_key().value() == 0xaa00 );
  UNODB_EXPECT_TRUE( b.get_val() && b.get_val().value() == unodb::test::test_values[0] );
  UNODB_EXPECT_TRUE( b.next() != e );
  UNODB_EXPECT_TRUE( b.get_key() && b.get_key().value() == 0xab0c );
  UNODB_EXPECT_TRUE( b.get_val() && b.get_val().value() == unodb::test::test_values[1] );
  UNODB_EXPECT_TRUE( b.next() != e );
  UNODB_EXPECT_TRUE( b.get_key() && b.get_key().value() == 0xab0d );
  UNODB_EXPECT_TRUE( b.get_val() && b.get_val().value() == unodb::test::test_values[2] );
  UNODB_EXPECT_TRUE( b.next() == e ); // nothing more in the iterator.
}

//
// iterator scan() tests.
//

TYPED_TEST(ARTIteratorTest, scan_empty_tree) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  uint64_t n = 0;
  auto fn = [&n](unodb::db::iterator&) {n++; return false;};
  db.scan( fn );
  UNODB_EXPECT_EQ( 0, n );
}

// Scan one leaf, verifying that we visit the leaf and can access its key and value.
TYPED_TEST(ARTIteratorTest, scan_one_leaf) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert( 0, unodb::test::test_values[0] );
  uint64_t n = 0;
  unodb::key visited_key{~0ULL};
  unodb::value_view visited_val{};
  auto fn = [&n,&visited_key,&visited_val](unodb::db::iterator& it) {
    n++;
    visited_key = it.get_key().value();
    visited_val = it.get_val().value();
    return false;
  };
  db.scan( fn );
  UNODB_EXPECT_EQ( 1, n );
  UNODB_EXPECT_EQ( 0, visited_key );
  UNODB_EXPECT_EQ( unodb::test::test_values[0], visited_val );
}

TYPED_TEST(ARTIteratorTest, scan_two_leaves) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert( 0, unodb::test::test_values[0] );
  verifier.insert( 1, unodb::test::test_values[1] );
  uint64_t n = 0;
  auto fn = [&n](unodb::db::iterator&) {n++; return false;};
  db.scan( fn );
  UNODB_EXPECT_EQ( 2, n );
}

TYPED_TEST(ARTIteratorTest, scan_three_leaves) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert( 0, unodb::test::test_values[0] );
  verifier.insert( 1, unodb::test::test_values[1] );
  verifier.insert( 2, unodb::test::test_values[2] );
  uint64_t n = 0;
  auto fn = [&n](unodb::db::iterator&) {n++; return false;};
  db.scan( fn );
  UNODB_EXPECT_EQ( 3, n );
}

TYPED_TEST(ARTIteratorTest, scan_four_leaves) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert( 0, unodb::test::test_values[0] );
  verifier.insert( 1, unodb::test::test_values[1] );
  verifier.insert( 2, unodb::test::test_values[2] );
  verifier.insert( 3, unodb::test::test_values[3] );
  uint64_t n = 0;
  auto fn = [&n](unodb::db::iterator&) {n++; return false;};
  db.scan( fn );
  UNODB_EXPECT_EQ( 4, n );
}

TYPED_TEST(ARTIteratorTest, scan_five_leaves) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert( 0, unodb::test::test_values[0] );
  verifier.insert( 1, unodb::test::test_values[1] );
  verifier.insert( 2, unodb::test::test_values[2] );
  verifier.insert( 3, unodb::test::test_values[3] );
  verifier.insert( 4, unodb::test::test_values[4] );
  uint64_t n = 0;
  auto fn = [&n](unodb::db::iterator&) {n++; return false;};
  db.scan( fn );
  UNODB_EXPECT_EQ( 5, n );
}

TYPED_TEST(ARTIteratorTest, scan_five_leaves_halt_early) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert( 0, unodb::test::test_values[0] );
  verifier.insert( 1, unodb::test::test_values[1] );
  verifier.insert( 2, unodb::test::test_values[2] );
  verifier.insert( 3, unodb::test::test_values[3] );
  verifier.insert( 4, unodb::test::test_values[4] );
  uint64_t n = 0;
  auto fn = [&n](unodb::db::iterator&) {n++; return n==1;};  // halt early!
  db.scan( fn );
  UNODB_EXPECT_EQ( 1, n );
}

// iterator scan test on a larger tree.
TYPED_TEST(ARTIteratorTest, scan_100_entries) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert_key_range( 0, 100 );
  uint64_t n = 0;
  auto fn = [&n](unodb::db::iterator&) {n++; return false;};
  db.scan( fn );
  UNODB_EXPECT_EQ( 100, n );
}

// iterator scan test on a larger tree.
TYPED_TEST(ARTIteratorTest, scan_1000_entries) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert_key_range( 0, 1000 );
  uint64_t n = 0;
  auto fn = [&n](unodb::db::iterator&) {n++; return false;};
  db.scan( fn );
  UNODB_EXPECT_EQ( 1000, n );
}

UNODB_END_TESTS()

}  // namespace
