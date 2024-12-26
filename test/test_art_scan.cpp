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

// Test suite for scan() API for the ART.
template <class Db>
class ARTScanTest : public ::testing::Test {
 public:
  using Test::Test;
};


// Test help creates an index and populates it with the ODD keys in
// [0:limit-1].  It then verifies the correct behavior of
// scan(fromKey,toKey) against that index.  Since the data only
// contains the ODD keys, you can probe with EVEN keys and verify that
// the scan() is carried out from the appropriate key in the data.
template <typename TypeParam>
void doScanTest(const uint64_t limit, const unodb::key fromKey, const unodb::key toKey) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  // Insert odd keys into the database.
  for ( uint64_t i = 1; i < limit; i+=2 ) {
    verifier.insert( i, unodb::test::test_values[0] );
  }
  const uint64_t nexpected = (toKey - fromKey) / 2; // expected number to visit.
  uint64_t nactual { 0 };  // actual number visited.
  auto fn = [&nactual,fromKey,toKey](unodb::db::visitor& v) {
    const auto key = v.get_key();
    EXPECT_EQ( nactual*2+fromKey, key ) << "nactual="<<nactual<<", fromKey="<<fromKey<<", toKey="<<toKey<<", key="<<key;
    EXPECT_TRUE( toKey != key ) << "nactual="<<nactual<<", fromKey="<<fromKey<<", toKey="<<toKey<<", key="<<key;  // we should never visit the toKey
    nactual++;
    return false;
  };
  db.scan( fromKey, toKey, fn );
  UNODB_EXPECT_EQ( nactual, nexpected );
}

//
// template meta parameters.
//
using ARTTypes = ::testing::Types<unodb::db>/*, unodb::mutex_db, unodb::olc_db>*/;     // FIXME Restore all ART types.

UNODB_TYPED_TEST_SUITE(ARTScanTest, ARTTypes)

UNODB_START_TYPED_TESTS()

//
// FIXME unit tests for gsl::span<std::byte>
//
// FIXME Develop a thread-safe version of the iterator based on mutex
// and OLC and extend microbenchmarks and unit tests.  For OLC, do a
// microbenchmark for parallel scaling with and w/o mutation.
//
//
//
// ==================== MORE SCAN TESTS HERE ====================
//
// FIXME (***) Tests for edge cases for scan() including: empty tree,
// first key missing, last key missing, both end keys missing, both
// end keys are the same (and both exist or one exists or both are
// missing), etc.
//
// FIXME There are three scan() variants.  Each of them needs to be
// tested since they are independent.  The existing test coverage is
// enough to make sure that each of them compiles.
//
// FIXME Tests which focus on scan(fromKey,toKey) and insure proper
// upper bound and reordering of the keys to determine forward or
// reverse traversal.

//
// forward scan
//

TYPED_TEST(ARTScanTest, scan_forward__empty_tree_keys_and_values) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  {
    uint64_t n = 0;
    auto fn = [&n](unodb::db::visitor&) {n++; return false;};
    db.scan( fn );
    UNODB_EXPECT_EQ( 0, n );
  }
  {
    uint64_t n = 0;
    auto fn = [&n](unodb::db::visitor&) {n++; return false;};
    db.scan( 0x0000, fn );
    UNODB_EXPECT_EQ( 0, n );
  }
  {
    uint64_t n = 0;
    auto fn = [&n](unodb::db::visitor&) {n++; return false;};
    db.scan( 0x0000, 0xffff, fn );
    UNODB_EXPECT_EQ( 0, n );
  }
}

// Scan one leaf, verifying that we visit the leaf and can access its key and value.
TYPED_TEST(ARTScanTest, scan_forward__one_leaf) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert( 0, unodb::test::test_values[0] );
  uint64_t n = 0;
  unodb::key visited_key{~0ULL};
  unodb::value_view visited_val{};
  auto fn = [&n,&visited_key,&visited_val](unodb::db::visitor& v) {
    n++;
    visited_key = v.get_key();
    visited_val = v.get_value();
    return false;
  };
  db.scan( fn );
  UNODB_EXPECT_EQ( 1, n );
  UNODB_EXPECT_EQ( 0, visited_key );
  UNODB_EXPECT_EQ( unodb::test::test_values[0], visited_val );
}

TYPED_TEST(ARTScanTest, scan_forward__two_leaves) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert( 0, unodb::test::test_values[0] );
  verifier.insert( 1, unodb::test::test_values[1] );
  uint64_t n = 0;
  std::vector<std::pair<unodb::key,unodb::value_view>> visited {};
  auto fn = [&n,&visited](unodb::db::visitor& v) {
    n++;
    visited.emplace_back( v.get_key(), v.get_value() );
    return false;
  };
  db.scan( fn, true/*fwd*/ );
  UNODB_EXPECT_EQ( 2, n );
  UNODB_EXPECT_EQ( 2, visited.size() );  
  UNODB_EXPECT_EQ( 0, visited[0].first ); // make sure we visited things in forward order.
  UNODB_EXPECT_EQ( 1, visited[1].first );
}

TYPED_TEST(ARTScanTest, scan_forward__three_leaves) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert( 0, unodb::test::test_values[0] );
  verifier.insert( 1, unodb::test::test_values[1] );
  verifier.insert( 2, unodb::test::test_values[2] );
  uint64_t n = 0;
  uint64_t expected = 0;
  auto fn = [&n,&expected](unodb::db::visitor& v) {
    n++;
    auto key = v.get_key();
    UNODB_EXPECT_EQ( expected, key );
    expected++;
    return false;
  };
  db.scan( fn, true/*fwd*/ );
  UNODB_EXPECT_EQ( 3, n );
}

TYPED_TEST(ARTScanTest, scan_forward__four_leaves) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert( 0, unodb::test::test_values[0] );
  verifier.insert( 1, unodb::test::test_values[1] );
  verifier.insert( 2, unodb::test::test_values[2] );
  verifier.insert( 3, unodb::test::test_values[3] );
  uint64_t n = 0;
  uint64_t expected = 0;
  auto fn = [&n,&expected](unodb::db::visitor& v) {
    n++;
    auto key = v.get_key();
    UNODB_EXPECT_EQ( expected, key );
    expected++;
    return false;
  };
  db.scan( fn );
  UNODB_EXPECT_EQ( 4, n );
}

TYPED_TEST(ARTScanTest, scan_forward__five_leaves) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert( 0, unodb::test::test_values[0] );
  verifier.insert( 1, unodb::test::test_values[1] );
  verifier.insert( 2, unodb::test::test_values[2] );
  verifier.insert( 3, unodb::test::test_values[3] );
  verifier.insert( 4, unodb::test::test_values[4] );
  uint64_t n = 0;
  uint64_t expected = 0;
  auto fn = [&n,&expected](unodb::db::visitor& v) {
    n++;
    auto key = v.get_key();
    UNODB_EXPECT_EQ( expected, key );
    expected++;
    return false;
  };
  db.scan( fn );
  UNODB_EXPECT_EQ( 5, n );
}

TYPED_TEST(ARTScanTest, scan_forward__five_leaves_halt_early) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert( 0, unodb::test::test_values[0] );
  verifier.insert( 1, unodb::test::test_values[1] );
  verifier.insert( 2, unodb::test::test_values[2] );
  verifier.insert( 3, unodb::test::test_values[3] );
  verifier.insert( 4, unodb::test::test_values[4] );
  uint64_t n = 0;
  auto fn = [&n](unodb::db::visitor&) {n++; return n==1;};  // halt early!
  db.scan( fn );
  UNODB_EXPECT_EQ( 1, n );
}

// iterator scan test on a larger tree.
TYPED_TEST(ARTScanTest, scan_forward__100_entries) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert_key_range( 0, 100 );
  uint64_t n = 0;
  uint64_t expected = 0;
  auto fn = [&n,&expected](unodb::db::visitor& v) {
    n++;
    auto key = v.get_key();
    UNODB_EXPECT_EQ( expected, key );
    expected++;
    return false;
  };
  db.scan( fn );
  UNODB_EXPECT_EQ( 100, n );
}

// iterator scan test on a larger tree.
TYPED_TEST(ARTScanTest, scan_forward__1000_entries) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert_key_range( 0, 1000 );
  uint64_t n = 0;
  uint64_t expected = 0;
  auto fn = [&n,&expected](unodb::db::visitor& v) {
    n++;
    auto key = v.get_key();
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

TYPED_TEST(ARTScanTest, scan_reverse__empty_tree) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  uint64_t n = 0;
  auto fn = [&n](unodb::db::visitor&) {n++; return false;};
  db.scan( fn, false/*fwd*/ );
  UNODB_EXPECT_EQ( 0, n );
}

// Scan one leaf, verifying that we visit the leaf and can access its key and value.
TYPED_TEST(ARTScanTest, scan_reverse__one_leaf) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert( 0, unodb::test::test_values[0] );
  uint64_t n = 0;
  unodb::key visited_key{~0ULL};
  unodb::value_view visited_val{};
  auto fn = [&n,&visited_key,&visited_val](unodb::db::visitor& v) {
    n++;
    visited_key = v.get_key();
    visited_val = v.get_value();
    return false;
  };
  db.scan( fn, false/*fwd*/ );
  UNODB_EXPECT_EQ( 1, n );
  UNODB_EXPECT_EQ( 0, visited_key );
  UNODB_EXPECT_EQ( unodb::test::test_values[0], visited_val );
}

TYPED_TEST(ARTScanTest, scan_reverse__two_leaves) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert( 0, unodb::test::test_values[0] );
  verifier.insert( 1, unodb::test::test_values[1] );
  uint64_t n = 0;
  std::vector<std::pair<unodb::key,unodb::value_view>> visited {};
  auto fn = [&n,&visited](unodb::db::visitor& v) {
    n++;
    visited.emplace_back( v.get_key(), v.get_value() );
    return false;
  };
  db.scan( fn, false/*fwd*/ );
  UNODB_EXPECT_EQ( 2, n );
  UNODB_EXPECT_EQ( 2, visited.size() );  
  UNODB_EXPECT_EQ( 1, visited[0].first ); // make sure we visited things in reverse order.
  UNODB_EXPECT_EQ( 0, visited[1].first );
}

TYPED_TEST(ARTScanTest, scan_reverse__three_leaves) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert( 0, unodb::test::test_values[0] );
  verifier.insert( 1, unodb::test::test_values[1] );
  verifier.insert( 2, unodb::test::test_values[2] );
  uint64_t n = 0;
  uint64_t expected = 2;
  auto fn = [&n,&expected](unodb::db::visitor& v) {
    n++;
    auto key = v.get_key();
    UNODB_EXPECT_EQ( expected, key );
    expected--;
    return false;
  };
  db.scan( fn, false/*fwd*/ );
  UNODB_EXPECT_EQ( 3, n );
}

TYPED_TEST(ARTScanTest, scan_reverse__four_leaves) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert( 0, unodb::test::test_values[0] );
  verifier.insert( 1, unodb::test::test_values[1] );
  verifier.insert( 2, unodb::test::test_values[2] );
  verifier.insert( 3, unodb::test::test_values[3] );
  uint64_t n = 0;
  uint64_t expected = 3;
  auto fn = [&n,&expected](unodb::db::visitor& v) {
    n++;
    auto key = v.get_key();
    UNODB_EXPECT_EQ( expected, key );
    expected--;
    return false;
  };
  db.scan( fn, false/*fwd*/ );
  UNODB_EXPECT_EQ( 4, n );
}

TYPED_TEST(ARTScanTest, scan_reverse__five_leaves) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert( 0, unodb::test::test_values[0] );
  verifier.insert( 1, unodb::test::test_values[1] );
  verifier.insert( 2, unodb::test::test_values[2] );
  verifier.insert( 3, unodb::test::test_values[3] );
  verifier.insert( 4, unodb::test::test_values[4] );
  uint64_t n = 0;
  uint64_t expected = 4;
  auto fn = [&n,&expected](unodb::db::visitor& v) {
    n++;
    auto key = v.get_key();
    UNODB_EXPECT_EQ( expected, key );
    expected--;
    return false;
  };
  db.scan( fn, false/*fwd*/ );
  UNODB_EXPECT_EQ( 5, n );
}

TYPED_TEST(ARTScanTest, scan_reverse__five_leaves_halt_early) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert( 0, unodb::test::test_values[0] );
  verifier.insert( 1, unodb::test::test_values[1] );
  verifier.insert( 2, unodb::test::test_values[2] );
  verifier.insert( 3, unodb::test::test_values[3] );
  verifier.insert( 4, unodb::test::test_values[4] );
  uint64_t n = 0;
  auto fn = [&n](unodb::db::visitor&) {n++; return n==1;};  // halt early!
  db.scan( fn, false/*fwd*/ );
  UNODB_EXPECT_EQ( 1, n );
}

// iterator scan test on a larger tree.
TYPED_TEST(ARTScanTest, scan_reverse__100_entries) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert_key_range( 0, 100 );
  uint64_t n = 0;
  uint64_t expected = 99;
  auto fn = [&n,&expected](unodb::db::visitor& v) {
    n++;
    auto key = v.get_key();
    UNODB_EXPECT_EQ( expected, key );
    expected--;
    return false;
  };
  db.scan( fn, false/*fwd*/ );
  UNODB_EXPECT_EQ( 100, n );
}

// iterator scan test on a larger tree.
TYPED_TEST(ARTScanTest, scan_reverse__1000_entries) {
  unodb::test::tree_verifier<TypeParam> verifier;
  TypeParam& db = verifier.get_db(); // reference to the database instance under test.
  verifier.insert_key_range( 0, 1000 );
  uint64_t n = 0;
  uint64_t expected = 999;
  auto fn = [&n,&expected](unodb::db::visitor& v) {
    n++;
    auto key = v.get_key();
    UNODB_EXPECT_EQ( expected, key );
    expected--;
    return false;
  };
  db.scan( fn, false/*fwd*/ );
  UNODB_EXPECT_EQ( 1000, n );
}

//
// FIXME (***) DO GENERAL CHECKS FOR LARGER TREES. For example, we
// could generate trees with a space between each pair of keys and use
// that to examine the before/after semantics of seek() for both
// forward and reverse traversal.
//
// TODO Do reverse traversal checks.
//
// TODO Do scan(fromKey,dir) checks.

TYPED_TEST(ARTScanTest, scan_from__10_entries__fromKey_0__toKey_10) {doScanTest<TypeParam>( 10, 1, 10 );}

TYPED_TEST(ARTScanTest, scan_from__1000_entries__fromKey_1__toKey_999) {doScanTest<TypeParam>( 1000, 1, 999 );}

UNODB_END_TESTS()

}  // namespace
