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
// FIXME unit tests for gsl::span<std::byte>
//
// FIXME Develop a thread-safe version of the iterator based on mutex
// and OLC and extend microbenchmarks and unit tests.  For OLC, do a
// microbenchmark for parallel scaling with and w/o mutation.
//

// unit test with an empty tree.
TYPED_TEST(ARTIteratorTest, empty_tree__forward_scan) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  auto b = db.begin(); // obtain iterators.
  const auto e = db.end();
  UNODB_EXPECT_TRUE( b == e );
  UNODB_EXPECT_TRUE( ! b.get_key() );
  UNODB_EXPECT_TRUE( ! b.get_val() );
}

// unit test with an empty tree.
TYPED_TEST(ARTIteratorTest, empty_tree__reverse_scan) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  auto b = db.last(); // obtain iterators.
  const auto e = db.end();
  UNODB_EXPECT_TRUE( b == e );
  UNODB_EXPECT_TRUE( ! b.get_key() );
  UNODB_EXPECT_TRUE( ! b.get_val() );
}

// unit test where the root is a single leaf.
TYPED_TEST(ARTIteratorTest, single_leaf_iterator_one_value) {
  unodb::test::tree_verifier<TypeParam> verifier;
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
TYPED_TEST(ARTIteratorTest, I4_and_two_leaves__forward_scan) {
  unodb::test::tree_verifier<TypeParam> verifier;
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

// unit test where the root is an I4 with two leafs under it.
TYPED_TEST(ARTIteratorTest, I4_and_two_leaves__reverse_scan) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert( 0, unodb::test::test_values[0] );
  verifier.insert( 1, unodb::test::test_values[1] );
  //std::cerr<<"db state::\n"; db.dump(std::cerr);
  auto b = db.last(); // obtain iterators.
  const auto e = db.end();
  UNODB_EXPECT_TRUE( b != e );
  //std::cerr<<"begin()::\n"; b.dump(std::cerr);
  UNODB_EXPECT_TRUE( b.get_key() && b.get_key().value() == 1 );
  UNODB_EXPECT_TRUE( b.get_val() && b.get_val().value() == unodb::test::test_values[1] );
  UNODB_EXPECT_TRUE( b.prior() != e );
  //std::cerr<<"b.next()::\n"; b.dump(std::cerr);
  UNODB_EXPECT_TRUE( b.get_key() && b.get_key().value() == 0 );
  UNODB_EXPECT_TRUE( b.get_val() && b.get_val().value() == unodb::test::test_values[0] );
  UNODB_EXPECT_TRUE( b.prior() == e ); // nothing more in the iterator.
  //std::cerr<<"b.next()::\n"; b.dump(std::cerr);
}

// unit test for the following tree structure, which is setup by how we choose the keys.
//
//       I4
//   I4     L2
// L0 L1
TYPED_TEST(ARTIteratorTest, iterator_three_values_left_axis_two_deep_right_axis_one_deep__forward_scan) {
  unodb::test::tree_verifier<TypeParam> verifier;
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
//   I4     L2
// L0 L1
TYPED_TEST(ARTIteratorTest, iterator_three_values_left_axis_two_deep_right_axis_one_deep__reverse_scan) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert( 0xaa00, unodb::test::test_values[0] );
  verifier.insert( 0xaa01, unodb::test::test_values[1] );
  verifier.insert( 0xab00, unodb::test::test_values[2] );
  auto b = db.last(); // obtain iterators.
  const auto e = db.end();
  UNODB_EXPECT_TRUE( b != e );
  UNODB_EXPECT_TRUE( b.get_key() && b.get_key().value() == 0xab00 );
  UNODB_EXPECT_TRUE( b.get_val() && b.get_val().value() == unodb::test::test_values[2] );
  UNODB_EXPECT_TRUE( b.prior() != e );
  UNODB_EXPECT_TRUE( b.get_key() && b.get_key().value() == 0xaa01 );
  UNODB_EXPECT_TRUE( b.get_val() && b.get_val().value() == unodb::test::test_values[1] );
  UNODB_EXPECT_TRUE( b.prior() != e );
  UNODB_EXPECT_TRUE( b.get_key() && b.get_key().value() == 0xaa00 );
  UNODB_EXPECT_TRUE( b.get_val() && b.get_val().value() == unodb::test::test_values[0] );
  UNODB_EXPECT_TRUE( b.prior() == e ); // nothing more in the iterator.
}

// unit test for the following tree structure, which is setup by how we choose the keys.
//
//       I4
//   L0     I4
//        L1 L2
TYPED_TEST(ARTIteratorTest, single_node_iterators_three_values_left_axis_one_deep_right_axis_two_deep__forward_scan) {
  unodb::test::tree_verifier<TypeParam> verifier;
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

// unit test for the following tree structure, which is setup by how we choose the keys.
//
//       I4
//   L0     I4
//        L1 L2
TYPED_TEST(ARTIteratorTest, single_node_iterators_three_values_left_axis_one_deep_right_axis_two_deep__reverse_scan) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert( 0xaa00, unodb::test::test_values[0] );
  verifier.insert( 0xab0c, unodb::test::test_values[1] );
  verifier.insert( 0xab0d, unodb::test::test_values[2] );
  auto b = db.last(); // obtain iterators.
  const auto e = db.end();
  UNODB_EXPECT_TRUE( b != e );
  UNODB_EXPECT_TRUE( b.get_key() && b.get_key().value() == 0xab0d );
  UNODB_EXPECT_TRUE( b.get_val() && b.get_val().value() == unodb::test::test_values[2] );
  UNODB_EXPECT_TRUE( b.prior() != e );
  UNODB_EXPECT_TRUE( b.get_key() && b.get_key().value() == 0xab0c );
  UNODB_EXPECT_TRUE( b.get_val() && b.get_val().value() == unodb::test::test_values[1] );
  UNODB_EXPECT_TRUE( b.prior() != e );
  UNODB_EXPECT_TRUE( b.get_key() && b.get_key().value() == 0xaa00 );
  UNODB_EXPECT_TRUE( b.get_val() && b.get_val().value() == unodb::test::test_values[0] );
  UNODB_EXPECT_TRUE( b.prior() == e ); // nothing more in the iterator.
}

//
// seek()
//

// unit test with an empty tree.
TYPED_TEST(ARTIteratorTest, empty_tree__seek) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  const auto e = db.end();
  bool match = false;
  UNODB_EXPECT_TRUE( db.seek( 0/*key*/, match, true/*fwd*/ ) == e );
  UNODB_EXPECT_EQ( match, false );
  UNODB_EXPECT_TRUE( db.seek( 0/*key*/, match, false/*fwd*/ ) == e );
  UNODB_EXPECT_EQ( match, false );
}

// unit test where the root is a single leaf.
TYPED_TEST(ARTIteratorTest, single_leaf__seek) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert( 1, unodb::test::test_values[1] );
  //std::cerr<<"db state::\n"; db.dump(std::cerr);
  const auto e = db.end();
  { // exact match, forward traversal (GTE)
    bool match = false;
    auto it = db.seek( 1/*key*/, match, true/*fwd*/ );
    UNODB_EXPECT_TRUE( it != e );
    UNODB_EXPECT_EQ( match, true );
    UNODB_EXPECT_TRUE( it.get_key() && it.get_key().value() == 1 );
    UNODB_EXPECT_TRUE( it.get_val() && it.get_val().value() == unodb::test::test_values[1] );
    UNODB_EXPECT_TRUE( it.next() == e ); // nothing more in the iterator.
  }
  { // exact match, reverse traversal (LTE)
    bool match = false;
    auto it = db.seek( 1/*key*/, match, false/*fwd*/ );  
    UNODB_EXPECT_TRUE( it != e );
    UNODB_EXPECT_EQ( match, true );
    UNODB_EXPECT_TRUE( it.get_key() && it.get_key().value() == 1 );
    UNODB_EXPECT_TRUE( it.get_val() && it.get_val().value() == unodb::test::test_values[1] );
    UNODB_EXPECT_TRUE( it.next() == e ); // nothing more in the iterator.
  }
  { // forward traversal, before the first key in the data.
    // match=false and iterator is positioned on the first key in the
    // data.
    bool match = true;
    auto it = db.seek( 0/*key*/, match, true/*fwd*/ );
    //std::cerr<<"db.seek(0,&match,true)::\n"; it.dump(std::cerr);
    UNODB_EXPECT_TRUE( it != e );
    UNODB_EXPECT_EQ( match, false );
    UNODB_EXPECT_TRUE( it.get_key() && it.get_key().value() == 1 );
    UNODB_EXPECT_TRUE( it.get_val() && it.get_val().value() == unodb::test::test_values[1] );
    UNODB_EXPECT_TRUE( it.next() == e ); // nothing more in the iterator.
  }
  { // forward traversal, after the last key in the data.  match=false
    // and iterator is positioned at end().
    bool match = true;
    auto it = db.seek( 2/*key*/, match, true/*fwd*/ );
    UNODB_EXPECT_TRUE( it == e );
    UNODB_EXPECT_EQ( match, false );
  }
  { // reverse traversal, before the first key in the data.
    // match=false and iterator is positioned at end().
    bool match = true;
    auto it = db.seek( 0/*key*/, match, false/*fwd*/ );
    UNODB_EXPECT_TRUE( it == e );
    UNODB_EXPECT_EQ( match, false );
  }
  { // reverse traversal, after the last key in the data.  match=false
    // and iterator is positioned at the last key.
    bool match = true;
    auto it = db.seek( 2/*key*/, match, false/*fwd*/ );
    //std::cerr<<"db.seek(2,&match,false)::\n"; it.dump(std::cerr);
    UNODB_EXPECT_TRUE( it != e );
    UNODB_EXPECT_EQ( match, false );
    UNODB_EXPECT_TRUE( it.get_key() && it.get_key().value() == 1 );
    UNODB_EXPECT_TRUE( it.get_val() && it.get_val().value() == unodb::test::test_values[1] );
    UNODB_EXPECT_TRUE( it.next() == e ); // nothing more in the iterator.
  }
}

// unit test for the following tree structure, which is setup by how we choose the keys.
//
//       I4
//   I4     L2
// L0 L1
TYPED_TEST(ARTIteratorTest, seek_three_values_left_axis_two_deep_right_axis_one_deep) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  const unodb::key k0 = 0xaa00;
  const unodb::key k1 = 0xaa10;
  const unodb::key k2 = 0xab10;
  verifier.insert( k0, unodb::test::test_values[0] );
  verifier.insert( k1, unodb::test::test_values[1] );
  verifier.insert( k2, unodb::test::test_values[2] );
  //std::cerr<<"db state::\n"; db.dump(std::cerr);
  const auto e = db.end();
  { // exact match, forward traversal
    { // exact match, forward traversal (GTE), first key.
      bool match = false;
      auto it = db.seek( k0, match, true/*fwd*/ );
      UNODB_EXPECT_TRUE( it != e );
      UNODB_EXPECT_EQ( match, true );
      UNODB_EXPECT_TRUE( it.get_key() && it.get_key().value() == k0 );
      UNODB_EXPECT_TRUE( it.get_val() && it.get_val().value() == unodb::test::test_values[0] );
    }
    { // exact match, forward traversal (GTE), middle key.
      bool match = false;
      auto it = db.seek( k1, match, true/*fwd*/ );
      UNODB_EXPECT_TRUE( it != e );
      UNODB_EXPECT_EQ( match, true );
      UNODB_EXPECT_TRUE( it.get_key() && it.get_key().value() == k1 );
      UNODB_EXPECT_TRUE( it.get_val() && it.get_val().value() == unodb::test::test_values[1] );
    }
    { // exact match, forward traversal (GTE), last key.
      bool match = false;
      auto it = db.seek( k2, match, true/*fwd*/ );
      UNODB_EXPECT_TRUE( it != e );
      UNODB_EXPECT_EQ( match, true );
      UNODB_EXPECT_TRUE( it.get_key() && it.get_key().value() == k2 );
      UNODB_EXPECT_TRUE( it.get_val() && it.get_val().value() == unodb::test::test_values[2] );
    }
  }
  { // exact match, reverse traversal
    { // exact match, reverse traversal (LTE), first key.
      bool match = false;
      auto it = db.seek( k0, match, false/*fwd*/ );
      UNODB_EXPECT_TRUE( it != e );
      UNODB_EXPECT_EQ( match, true );
      UNODB_EXPECT_TRUE( it.get_key() && it.get_key().value() == k0 );
      UNODB_EXPECT_TRUE( it.get_val() && it.get_val().value() == unodb::test::test_values[0] );
    }
    { // exact match, reverse traversal (LTE), middle key.
      bool match = false;
      auto it = db.seek( k1, match, false/*fwd*/ );  
      UNODB_EXPECT_TRUE( it != e );
      UNODB_EXPECT_EQ( match, true );
      UNODB_EXPECT_TRUE( it.get_key() && it.get_key().value() == k1 );
      UNODB_EXPECT_TRUE( it.get_val() && it.get_val().value() == unodb::test::test_values[1] );
    }
    { // exact match, reverse traversal (LTE), last key.
      bool match = false;
      auto it = db.seek( k2, match, false/*fwd*/ );  
      UNODB_EXPECT_TRUE( it != e );
      UNODB_EXPECT_EQ( match, true );
      UNODB_EXPECT_TRUE( it.get_key() && it.get_key().value() == k2 );
      UNODB_EXPECT_TRUE( it.get_val() && it.get_val().value() == unodb::test::test_values[2] );
    }
  }
  { // before and after the first and last key
    { // forward traversal, before the first key in the data.
      // match=false and iterator is positioned on the first key in the
      // data.
      bool match = true;
      auto it = db.seek( 0/*key*/, match, true/*fwd*/ );
      //std::cerr<<"db.seek(0,&match,true)::\n"; it.dump(std::cerr);
      UNODB_EXPECT_TRUE( it != e );
      UNODB_EXPECT_EQ( match, false );
      UNODB_EXPECT_TRUE( it.get_key() && it.get_key().value() == k0 );
      UNODB_EXPECT_TRUE( it.get_val() && it.get_val().value() == unodb::test::test_values[0] );
    }
    { // forward traversal, after the last key in the data.  match=false
      // and iterator is positioned at end().
      bool match = true;
      auto it = db.seek( 0xffff/*key*/, match, true/*fwd*/ );
      //std::cerr<<"db.seek(0xffff,&match,true)::\n"; it.dump(std::cerr);
      UNODB_EXPECT_TRUE( it == e );
      UNODB_EXPECT_EQ( match, false );
    }
    { // reverse traversal, before the first key in the data.
      // match=false and iterator is positioned at end().
      bool match = true;
      auto it = db.seek( 0/*key*/, match, false/*fwd*/ );
      UNODB_EXPECT_TRUE( it == e );
      UNODB_EXPECT_EQ( match, false );
    }
    { // reverse traversal, after the last key in the data.  match=false
      // and iterator is positioned at the last key.
      bool match = true;
      auto it = db.seek( 0xffff/*key*/, match, false/*fwd*/ );
      //std::cerr<<"db.seek(2,&match,false)::\n"; it.dump(std::cerr);
      UNODB_EXPECT_TRUE( it != e );
      UNODB_EXPECT_EQ( match, false );
      UNODB_EXPECT_TRUE( it.get_key() && it.get_key().value() == k2 );
      UNODB_EXPECT_TRUE( it.get_val() && it.get_val().value() == unodb::test::test_values[2] );
      UNODB_EXPECT_TRUE( it.next() == e ); // nothing more in the iterator.
    }
  }
}

//    I4
// L0 L1 L2
//
TYPED_TEST(ARTIteratorTest, seek_three_leaves_under_the_root) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  const unodb::key k0 = 0xaa10;
  const unodb::key k1 = 0xaa20;
  const unodb::key k2 = 0xaa30;
  verifier.insert( k0, unodb::test::test_values[0] );
  verifier.insert( k1, unodb::test::test_values[1] );
  verifier.insert( k2, unodb::test::test_values[2] );
  std::cerr<<"db state::\n"; db.dump(std::cerr);
  const auto e = db.end();
  { // exact match, forward traversal
    { // exact match, forward traversal (GTE), first key.
      bool match = false;
      auto it = db.seek( k0, match, true/*fwd*/ );
      UNODB_EXPECT_TRUE( it != e );
      UNODB_EXPECT_EQ( match, true );
      UNODB_EXPECT_TRUE( it.get_key() && it.get_key().value() == k0 );
      UNODB_EXPECT_TRUE( it.get_val() && it.get_val().value() == unodb::test::test_values[0] );
    }
    { // exact match, forward traversal (GTE), middle key.
      bool match = false;
      auto it = db.seek( k1, match, true/*fwd*/ );
      UNODB_EXPECT_TRUE( it != e );
      UNODB_EXPECT_EQ( match, true );
      UNODB_EXPECT_TRUE( it.get_key() && it.get_key().value() == k1 );
      UNODB_EXPECT_TRUE( it.get_val() && it.get_val().value() == unodb::test::test_values[1] );
    }
    { // exact match, forward traversal (GTE), last key.
      bool match = false;
      auto it = db.seek( k2, match, true/*fwd*/ );
      UNODB_EXPECT_TRUE( it != e );
      UNODB_EXPECT_EQ( match, true );
      UNODB_EXPECT_TRUE( it.get_key() && it.get_key().value() == k2 );
      UNODB_EXPECT_TRUE( it.get_val() && it.get_val().value() == unodb::test::test_values[2] );
    }
  }
  { // exact match, reverse traversal
    { // exact match, reverse traversal (LTE), first key.
      bool match = false;
      auto it = db.seek( k0, match, false/*fwd*/ );
      UNODB_EXPECT_TRUE( it != e );
      UNODB_EXPECT_EQ( match, true );
      UNODB_EXPECT_TRUE( it.get_key() && it.get_key().value() == k0 );
      UNODB_EXPECT_TRUE( it.get_val() && it.get_val().value() == unodb::test::test_values[0] );
    }
    { // exact match, reverse traversal (LTE), middle key.
      bool match = false;
      auto it = db.seek( k1, match, false/*fwd*/ );  
      UNODB_EXPECT_TRUE( it != e );
      UNODB_EXPECT_EQ( match, true );
      UNODB_EXPECT_TRUE( it.get_key() && it.get_key().value() == k1 );
      UNODB_EXPECT_TRUE( it.get_val() && it.get_val().value() == unodb::test::test_values[1] );
    }
    { // exact match, reverse traversal (LTE), last key.
      bool match = false;
      auto it = db.seek( k2, match, false/*fwd*/ );  
      UNODB_EXPECT_TRUE( it != e );
      UNODB_EXPECT_EQ( match, true );
      UNODB_EXPECT_TRUE( it.get_key() && it.get_key().value() == k2 );
      UNODB_EXPECT_TRUE( it.get_val() && it.get_val().value() == unodb::test::test_values[2] );
    }
  }
  { // before and after the first and last key
    { // forward traversal, before the first key in the data.
      // match=false and iterator is positioned on the first key in the
      // data.
      bool match = true;
      auto it = db.seek( 0/*key*/, match, true/*fwd*/ );
      //std::cerr<<"db.seek(0,&match,true)::\n"; it.dump(std::cerr);
      UNODB_EXPECT_TRUE( it != e );
      UNODB_EXPECT_EQ( match, false );
      UNODB_EXPECT_TRUE( it.get_key() && it.get_key().value() == k0 );
      UNODB_EXPECT_TRUE( it.get_val() && it.get_val().value() == unodb::test::test_values[0] );
    }
    { // forward traversal, after the last key in the data.  match=false
      // and iterator is positioned at end().
      bool match = true;
      auto it = db.seek( 0xffff/*key*/, match, true/*fwd*/ );
      std::cerr<<"db.seek(0xffff,&match,true)::\n"; it.dump(std::cerr);
      UNODB_EXPECT_TRUE( it == e );
      UNODB_EXPECT_EQ( match, false );
    }
    { // reverse traversal, before the first key in the data.
      // match=false and iterator is positioned at end().
      bool match = true;
      auto it = db.seek( 0/*key*/, match, false/*fwd*/ );
      std::cerr<<"db.seek(0,&match,true)::\n"; it.dump(std::cerr);
      UNODB_EXPECT_TRUE( it == e );
      UNODB_EXPECT_EQ( match, false );
    }
    { // reverse traversal, after the last key in the data.  match=false
      // and iterator is positioned at the last key.
      bool match = true;
      auto it = db.seek( 0xffff/*key*/, match, false/*fwd*/ );
      std::cerr<<"db.seek(0xffff,&match,false)::\n"; it.dump(std::cerr);
      UNODB_EXPECT_TRUE( it != e );
      UNODB_EXPECT_EQ( match, false );
      UNODB_EXPECT_TRUE( it.get_key() && it.get_key().value() == k2 );
      UNODB_EXPECT_TRUE( it.get_val() && it.get_val().value() == unodb::test::test_values[2] );
      UNODB_EXPECT_TRUE( it.next() == e ); // nothing more in the iterator.
    }
  }
}

// FIXME (***) CONTINUE TO AT LEAST HEIGHT TWO TREES WITH SPECIFIC
//             TESTS.
//


//
// ==================== MORE SCAN TESTS HERE ====================
//
// FIXME (***) Tests for edge cases for scan() including: empty tree,
// first key missing, last key missing, both end keys missing, both
// end keys are the same (and both exist or one exists or both are
// missing), etc.

// FIXME (***) DO GENERAL CHECKS FOR LARGER TREES. For example, we
// could generate trees with a space between each pair of keys and use
// that to examine the before/after semantics of seek() for both
// forward and reverse traversal.

//
// forward scan
//

TYPED_TEST(ARTIteratorTest, scan_forward__empty_tree) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  uint64_t n = 0;
  auto fn = [&n](unodb::db::iterator&) {n++; return false;};
  db.scan( fn );
  UNODB_EXPECT_EQ( 0, n );
}

// Scan one leaf, verifying that we visit the leaf and can access its key and value.
TYPED_TEST(ARTIteratorTest, scan_forward__one_leaf) {
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

TYPED_TEST(ARTIteratorTest, scan_forward__two_leaves) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert( 0, unodb::test::test_values[0] );
  verifier.insert( 1, unodb::test::test_values[1] );
  uint64_t n = 0;
  std::vector<std::pair<unodb::key,unodb::value_view>> visited {};
  auto fn = [&n,&visited](unodb::db::iterator& it) {
    n++;
    auto key = it.get_key().value();
    auto val = it.get_val().value();
    visited.emplace_back( key, val );
    return false;
  };
  db.scan( fn, true/*fwd*/ );
  UNODB_EXPECT_EQ( 2, n );
  UNODB_EXPECT_EQ( 2, visited.size() );  
  UNODB_EXPECT_EQ( 0, visited[0].first ); // make sure we visited things in forward order.
  UNODB_EXPECT_EQ( 1, visited[1].first );
}

TYPED_TEST(ARTIteratorTest, scan_forward__three_leaves) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert( 0, unodb::test::test_values[0] );
  verifier.insert( 1, unodb::test::test_values[1] );
  verifier.insert( 2, unodb::test::test_values[2] );
  uint64_t n = 0;
  uint64_t expected = 0;
  auto fn = [&n,&expected](unodb::db::iterator& it) {
    n++;
    auto key = it.get_key().value();
    UNODB_EXPECT_EQ( expected, key );
    expected++;
    return false;
  };
  db.scan( fn, true/*fwd*/ );
  UNODB_EXPECT_EQ( 3, n );
}

TYPED_TEST(ARTIteratorTest, scan_forward__four_leaves) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert( 0, unodb::test::test_values[0] );
  verifier.insert( 1, unodb::test::test_values[1] );
  verifier.insert( 2, unodb::test::test_values[2] );
  verifier.insert( 3, unodb::test::test_values[3] );
  uint64_t n = 0;
  uint64_t expected = 0;
  auto fn = [&n,&expected](unodb::db::iterator& it) {
    n++;
    auto key = it.get_key().value();
    UNODB_EXPECT_EQ( expected, key );
    expected++;
    return false;
  };
  db.scan( fn );
  UNODB_EXPECT_EQ( 4, n );
}

TYPED_TEST(ARTIteratorTest, scan_forward__five_leaves) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert( 0, unodb::test::test_values[0] );
  verifier.insert( 1, unodb::test::test_values[1] );
  verifier.insert( 2, unodb::test::test_values[2] );
  verifier.insert( 3, unodb::test::test_values[3] );
  verifier.insert( 4, unodb::test::test_values[4] );
  uint64_t n = 0;
  uint64_t expected = 0;
  auto fn = [&n,&expected](unodb::db::iterator& it) {
    n++;
    auto key = it.get_key().value();
    UNODB_EXPECT_EQ( expected, key );
    expected++;
    return false;
  };
  db.scan( fn );
  UNODB_EXPECT_EQ( 5, n );
}

TYPED_TEST(ARTIteratorTest, scan_forward__five_leaves_halt_early) {
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
TYPED_TEST(ARTIteratorTest, scan_forward__100_entries) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert_key_range( 0, 100 );
  uint64_t n = 0;
  uint64_t expected = 0;
  auto fn = [&n,&expected](unodb::db::iterator& it) {
    n++;
    auto key = it.get_key().value();
    UNODB_EXPECT_EQ( expected, key );
    expected++;
    return false;
  };
  db.scan( fn );
  UNODB_EXPECT_EQ( 100, n );
}

// iterator scan test on a larger tree.
TYPED_TEST(ARTIteratorTest, scan_forward__1000_entries) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert_key_range( 0, 1000 );
  uint64_t n = 0;
  uint64_t expected = 0;
  auto fn = [&n,&expected](unodb::db::iterator& it) {
    n++;
    auto key = it.get_key().value();
    UNODB_EXPECT_EQ( expected, key );
    expected++;
    return false;
  };
  db.scan( fn );
  UNODB_EXPECT_EQ( 1000, n );
}

//
// reverse scan
//

TYPED_TEST(ARTIteratorTest, scan_reverse__empty_tree) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  uint64_t n = 0;
  auto fn = [&n](unodb::db::iterator&) {n++; return false;};
  db.scan( fn, false/*fwd*/ );
  UNODB_EXPECT_EQ( 0, n );
}

// Scan one leaf, verifying that we visit the leaf and can access its key and value.
TYPED_TEST(ARTIteratorTest, scan_reverse__one_leaf) {
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
  db.scan( fn, false/*fwd*/ );
  UNODB_EXPECT_EQ( 1, n );
  UNODB_EXPECT_EQ( 0, visited_key );
  UNODB_EXPECT_EQ( unodb::test::test_values[0], visited_val );
}

TYPED_TEST(ARTIteratorTest, scan_reverse__two_leaves) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert( 0, unodb::test::test_values[0] );
  verifier.insert( 1, unodb::test::test_values[1] );
  uint64_t n = 0;
  std::vector<std::pair<unodb::key,unodb::value_view>> visited {};
  auto fn = [&n,&visited](unodb::db::iterator& it) {
    n++;
    auto key = it.get_key().value();
    auto val = it.get_val().value();
    visited.emplace_back( key, val );
    return false;
  };
  db.scan( fn, false/*fwd*/ );
  UNODB_EXPECT_EQ( 2, n );
  UNODB_EXPECT_EQ( 2, visited.size() );  
  UNODB_EXPECT_EQ( 1, visited[0].first ); // make sure we visited things in reverse order.
  UNODB_EXPECT_EQ( 0, visited[1].first );
}

TYPED_TEST(ARTIteratorTest, scan_reverse__three_leaves) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert( 0, unodb::test::test_values[0] );
  verifier.insert( 1, unodb::test::test_values[1] );
  verifier.insert( 2, unodb::test::test_values[2] );
  uint64_t n = 0;
  uint64_t expected = 2;
  auto fn = [&n,&expected](unodb::db::iterator& it) {
    n++;
    auto key = it.get_key().value();
    UNODB_EXPECT_EQ( expected, key );
    expected--;
    return false;
  };
  db.scan( fn, false/*fwd*/ );
  UNODB_EXPECT_EQ( 3, n );
}

TYPED_TEST(ARTIteratorTest, scan_reverse__four_leaves) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert( 0, unodb::test::test_values[0] );
  verifier.insert( 1, unodb::test::test_values[1] );
  verifier.insert( 2, unodb::test::test_values[2] );
  verifier.insert( 3, unodb::test::test_values[3] );
  uint64_t n = 0;
  uint64_t expected = 3;
  auto fn = [&n,&expected](unodb::db::iterator& it) {
    n++;
    auto key = it.get_key().value();
    UNODB_EXPECT_EQ( expected, key );
    expected--;
    return false;
  };
  db.scan( fn, false/*fwd*/ );
  UNODB_EXPECT_EQ( 4, n );
}

TYPED_TEST(ARTIteratorTest, scan_reverse__five_leaves) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert( 0, unodb::test::test_values[0] );
  verifier.insert( 1, unodb::test::test_values[1] );
  verifier.insert( 2, unodb::test::test_values[2] );
  verifier.insert( 3, unodb::test::test_values[3] );
  verifier.insert( 4, unodb::test::test_values[4] );
  uint64_t n = 0;
  uint64_t expected = 4;
  auto fn = [&n,&expected](unodb::db::iterator& it) {
    n++;
    auto key = it.get_key().value();
    UNODB_EXPECT_EQ( expected, key );
    expected--;
    return false;
  };
  db.scan( fn, false/*fwd*/ );
  UNODB_EXPECT_EQ( 5, n );
}

TYPED_TEST(ARTIteratorTest, scan_reverse__five_leaves_halt_early) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert( 0, unodb::test::test_values[0] );
  verifier.insert( 1, unodb::test::test_values[1] );
  verifier.insert( 2, unodb::test::test_values[2] );
  verifier.insert( 3, unodb::test::test_values[3] );
  verifier.insert( 4, unodb::test::test_values[4] );
  uint64_t n = 0;
  auto fn = [&n](unodb::db::iterator&) {n++; return n==1;};  // halt early!
  db.scan( fn, false/*fwd*/ );
  UNODB_EXPECT_EQ( 1, n );
}

// iterator scan test on a larger tree.
TYPED_TEST(ARTIteratorTest, scan_reverse__100_entries) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert_key_range( 0, 100 );
  uint64_t n = 0;
  uint64_t expected = 99;
  auto fn = [&n,&expected](unodb::db::iterator& it) {
    n++;
    auto key = it.get_key().value();
    UNODB_EXPECT_EQ( expected, key );
    expected--;
    return false;
  };
  db.scan( fn, false/*fwd*/ );
  UNODB_EXPECT_EQ( 100, n );
}

// iterator scan test on a larger tree.
TYPED_TEST(ARTIteratorTest, scan_reverse__1000_entries) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert_key_range( 0, 1000 );
  uint64_t n = 0;
  uint64_t expected = 999;
  auto fn = [&n,&expected](unodb::db::iterator& it) {
    n++;
    auto key = it.get_key().value();
    UNODB_EXPECT_EQ( expected, key );
    expected--;
    return false;
  };
  db.scan( fn, false/*fwd*/ );
  UNODB_EXPECT_EQ( 1000, n );
}

UNODB_END_TESTS()

}  // namespace
