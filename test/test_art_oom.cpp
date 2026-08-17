// Copyright 2022-2026 UnoDB contributors

#ifndef NDEBUG

// Should be the first include
#include "global.hpp"  // IWYU pragma: keep

// IWYU pragma: no_include <array>
// IWYU pragma: no_include <string>

#include <cstdint>
#include <utility>
#include <vector>

#include <gtest/gtest.h>

#include "art_common.hpp"
#include "art_test_data.hpp"
#include "db_test_utils.hpp"
#include "gtest_utils.hpp"
#include "test_heap.hpp"
#include "test_utils.hpp"

// The OOM tests are dependent on the number of heap allocations in the test,
// that's brittle and hardcoded. Suppose some op takes 5 heap allocations. The
// tests is written in that it knows that the test should fail on OOMs injected
// on the 1st-5th allocation and pass on the 6th one. The allocations done by
// libstdc++ are included.
//
// Changing the data structure in the main code or the test suite might perturb
// this, causing tests to fail. If this happens you need to decide whether the
// change in behavior was for a valid reason or not.
//
// oom_scan_test and bulk_load_oom_test fail differently: there fail_limit is
// only an upper bound, so their UNODB_ASSERT_LE / FAIL() forms always mean
// increment, and a too-high limit is silently tolerated.
namespace {

/// Exercise \a test at each expected allocation-failure point.
///
/// The assertions hold only when the operation makes exactly fail_limit - 1
/// injectable allocations, so recalibrate from that invariant rather than from
/// a lookup table. A mid-loop failure, "Value of: ... throws_bad_alloc(...) /
/// Actual: false / Expected: true", means the operation now makes fewer
/// allocations than the limit assumes - a decrement. A failure on the last
/// iteration, which expected false and got true, means the operation still
/// reaches its fail_limit-th allocation - an increment. Neither message names
/// the failing iteration, but the two shapes are monotone in fail_limit and
/// mutually exclusive, so stepping or bisecting on them converges.
template <class TypeParam, typename Init, typename Test, typename CheckAfterOOM,
          typename CheckAfterSuccess>
void oom_test(unsigned fail_limit, Init init, Test test,
              CheckAfterOOM check_after_oom,
              CheckAfterSuccess check_after_success) {
  unsigned fail_n;
  for (fail_n = 1; fail_n < fail_limit; ++fail_n) {
    unodb::test::tree_verifier<TypeParam> verifier;
    init(verifier);

    UNODB_ASSERT_TRUE(unodb::test::throws_bad_alloc(
        fail_n, [&test, &verifier] { test(verifier); }));

    verifier.check_present_values();
    check_after_oom(verifier);
  }

  unodb::test::tree_verifier<TypeParam> verifier;
  init(verifier);

  UNODB_ASSERT_FALSE(unodb::test::throws_bad_alloc(
      fail_n, [&test, &verifier] { test(verifier); }));

  verifier.check_present_values();
  check_after_success(verifier);
}

template <class TypeParam, typename Init, typename CheckAfterSuccess>
void oom_insert_test(unsigned fail_limit, Init init, std::uint64_t k,
                     unodb::value_view v,
                     CheckAfterSuccess check_after_success) {
  oom_test<TypeParam>(
      fail_limit, init,
      [k, v](unodb::test::tree_verifier<TypeParam>& verifier) {
        verifier.insert(k, v);
      },
      [k](unodb::test::tree_verifier<TypeParam>& verifier) {
        verifier.check_absent_keys({k});
      },
      check_after_success);
}

template <class TypeParam, typename Init, typename CheckAfterSuccess>
void oom_remove_test(unsigned fail_limit, Init init, std::uint64_t k,
                     CheckAfterSuccess check_after_success) {
  oom_test<TypeParam>(
      fail_limit, init,
      [k](unodb::test::tree_verifier<TypeParam>& verifier) {
        verifier.remove(k);
      },
      [](unodb::test::tree_verifier<TypeParam>&) {},
      [k,
       check_after_success](unodb::test::tree_verifier<TypeParam>& verifier) {
        verifier.check_absent_keys({k});
        check_after_success(verifier);
      });
}

/// Exercise a scan across its implementation-defined allocation points.
///
/// The count cannot be hardcoded: it comes from the iterator's std::stack/deque
/// and key buffer, whose allocation counts are standard-library-dependent
/// (libc++ vs libstdc++ debug mode). So fail_limit is only an upper bound:
/// inject at each point until the scan completes without OOM. The scan is
/// read-only, so the tree must be intact after every injection point, whether
/// that iteration threw (the strong guarantee) or completed.
///
/// UNODB_ASSERT_GT(fail_n, 1U) is the exception to the upper-bound adjustment
/// rule: reported as "Expected: (fail_n) > (1U), actual: 1 vs 1", it can only
/// fire when the scan makes no injectable allocation at all, so the test
/// exercises nothing. No fail_limit value repairs that - fix the scan, not the
/// limit.
template <class TypeParam, typename ScanOp>
void oom_scan_test(unsigned fail_limit, const ScanOp& scan_op) {
  unodb::test::tree_verifier<TypeParam> verifier;
  verifier.insert_key_range(0, 16);

  unsigned fail_n = 1;
  for (; fail_n <= fail_limit; ++fail_n) {
    const bool completed = !unodb::test::throws_bad_alloc(
        fail_n, [&scan_op, &verifier] { scan_op(verifier.get_db()); });
    verifier.check_present_values();
    // Scan completed without OOM: past all of its allocations.
    if (completed) break;
  }
  // Scan completed within fail_limit, making >= 1 injectable allocation.
  UNODB_ASSERT_LE(fail_n, fail_limit);
  UNODB_ASSERT_GT(fail_n, 1U);
}

template <class Db>
class ARTOOMTest : public ::testing::Test {
 public:
  using Test::Test;
};

using ARTTypes =
    ::testing::Types<unodb::test::u64_db, unodb::test::u64_mutex_db,
                     unodb::test::u64_olc_db>;

UNODB_TYPED_TEST_SUITE(ARTOOMTest, ARTTypes)

// The guard must be declared before the tree so that reverse destruction order
// leaves the destructor inside the armed window; swapping the two lines still
// compiles and passes while pinning nothing at all - the constructor would run
// before the guard arms, and the destructor after the guard's own destructor
// disarmed. Note that the destructor half is enforced differently: the
// destructors of all three tested types are noexcept, so a violation there
// terminates the process rather than failing this test, per the noexcept-frame
// warning on fail_on_nth_allocation_guard.
UNODB_TYPED_TEST(ARTOOMTest, CtorAndDtorDoNotAllocate) {
  UNODB_DETAIL_FAIL_ON_NTH_ALLOCATION_GUARD(1);
  const TypeParam tree;
}

UNODB_TYPED_TEST(ARTOOMTest, SingleNodeTreeEmptyValue) {
  oom_insert_test<TypeParam>(
      2,
      [](unodb::test::tree_verifier<TypeParam>&
#ifdef UNODB_DETAIL_WITH_STATS
             verifier
#endif  // UNODB_DETAIL_WITH_STATS
      ) {
#ifdef UNODB_DETAIL_WITH_STATS
        verifier.assert_node_counts({0, 0, 0, 0, 0});
        verifier.assert_growing_inodes({0, 0, 0, 0});
#endif  // UNODB_DETAIL_WITH_STATS
      },
      1, {},
      [](unodb::test::tree_verifier<TypeParam>&
#ifdef UNODB_DETAIL_WITH_STATS
             verifier
#endif  // UNODB_DETAIL_WITH_STATS
      ) {
#ifdef UNODB_DETAIL_WITH_STATS
        verifier.assert_node_counts({1, 0, 0, 0, 0});
        verifier.assert_growing_inodes({0, 0, 0, 0});
#endif
      });
}

UNODB_TYPED_TEST(ARTOOMTest, SingleNodeTreeNonemptyValue) {
  oom_insert_test<TypeParam>(
      2,
      [](unodb::test::tree_verifier<TypeParam>&
#ifdef UNODB_DETAIL_WITH_STATS
             verifier
#endif  // UNODB_DETAIL_WITH_STATS
      ) {
#ifdef UNODB_DETAIL_WITH_STATS
        verifier.assert_node_counts({0, 0, 0, 0, 0});
        verifier.assert_growing_inodes({0, 0, 0, 0});
#endif  // UNODB_DETAIL_WITH_STATS
      },
      1, unodb::test_data::test_values[2],
      [](unodb::test::tree_verifier<TypeParam>&
#ifdef UNODB_DETAIL_WITH_STATS
             verifier
#endif  // UNODB_DETAIL_WITH_STATS
      ) {
#ifdef UNODB_DETAIL_WITH_STATS
        verifier.assert_node_counts({1, 0, 0, 0, 0});
        verifier.assert_growing_inodes({0, 0, 0, 0});
#endif  // UNODB_DETAIL_WITH_STATS
      });
}

UNODB_TYPED_TEST(ARTOOMTest, ExpandLeafToNode4) {
  oom_insert_test<TypeParam>(
      3,
      [](unodb::test::tree_verifier<TypeParam>& verifier) {
        verifier.insert(0, unodb::test_data::test_values[1]);
#ifdef UNODB_DETAIL_WITH_STATS
        verifier.assert_node_counts({1, 0, 0, 0, 0});
        verifier.assert_growing_inodes({0, 0, 0, 0});
#endif  // UNODB_DETAIL_WITH_STATS
      },
      1, unodb::test_data::test_values[2],
      [](unodb::test::tree_verifier<TypeParam>&
#ifdef UNODB_DETAIL_WITH_STATS
             verifier
#endif  // UNODB_DETAIL_WITH_STATS
      ) {
#ifdef UNODB_DETAIL_WITH_STATS
        verifier.assert_node_counts({2, 1, 0, 0, 0});
        verifier.assert_growing_inodes({1, 0, 0, 0});
#endif  // UNODB_DETAIL_WITH_STATS
      });
}

UNODB_TYPED_TEST(ARTOOMTest, TwoNode4) {
  oom_insert_test<TypeParam>(
      3,
      [](unodb::test::tree_verifier<TypeParam>& verifier) {
        verifier.insert(1, unodb::test_data::test_values[0]);
        verifier.insert(3, unodb::test_data::test_values[2]);
#ifdef UNODB_DETAIL_WITH_STATS
        verifier.assert_growing_inodes({1, 0, 0, 0});
        verifier.assert_node_counts({2, 1, 0, 0, 0});
        verifier.assert_key_prefix_splits(0);
#endif  // UNODB_DETAIL_WITH_STATS
      },
      // Insert a value that does not share full prefix with the current Node4
      0xFF01, unodb::test_data::test_values[3],
      [](unodb::test::tree_verifier<TypeParam>&
#ifdef UNODB_DETAIL_WITH_STATS
             verifier
#endif  // UNODB_DETAIL_WITH_STATS
      ) {
#ifdef UNODB_DETAIL_WITH_STATS
        verifier.assert_node_counts({3, 2, 0, 0, 0});
        verifier.assert_growing_inodes({2, 0, 0, 0});
        verifier.assert_key_prefix_splits(1);
#endif  // UNODB_DETAIL_WITH_STATS
      });
}

UNODB_TYPED_TEST(ARTOOMTest, DbInsertNodeRecursion) {
  oom_insert_test<TypeParam>(
      3,
      [](unodb::test::tree_verifier<TypeParam>& verifier) {
        verifier.insert(1, unodb::test_data::test_values[0]);
        verifier.insert(3, unodb::test_data::test_values[2]);
        // Insert a value that does not share full prefix with the current Node4
        verifier.insert(0xFF0001, unodb::test_data::test_values[3]);
#ifdef UNODB_DETAIL_WITH_STATS
        verifier.assert_node_counts({3, 2, 0, 0, 0});
        verifier.assert_growing_inodes({2, 0, 0, 0});
        verifier.assert_key_prefix_splits(1);
#endif  // UNODB_DETAIL_WITH_STATS
      },
      // Then insert a value that shares full prefix with the above node and
      // will ask for a recursive insertion there
      0xFF0101, unodb::test_data::test_values[1],
      [](unodb::test::tree_verifier<TypeParam>&
#ifdef UNODB_DETAIL_WITH_STATS
             verifier
#endif  // UNODB_DETAIL_WITH_STATS
      ) {
#ifdef UNODB_DETAIL_WITH_STATS
        verifier.assert_node_counts({4, 3, 0, 0, 0});
        verifier.assert_growing_inodes({3, 0, 0, 0});
#endif  // UNODB_DETAIL_WITH_STATS
      });
}

UNODB_TYPED_TEST(ARTOOMTest, Node16) {
  oom_insert_test<TypeParam>(
      3,
      [](unodb::test::tree_verifier<TypeParam>& verifier) {
        verifier.insert_key_range(0, 4);
#ifdef UNODB_DETAIL_WITH_STATS
        verifier.assert_node_counts({4, 1, 0, 0, 0});
        verifier.assert_growing_inodes({1, 0, 0, 0});
#endif  // UNODB_DETAIL_WITH_STATS
      },
      5, unodb::test_data::test_values[0],
      [](unodb::test::tree_verifier<TypeParam>&
#ifdef UNODB_DETAIL_WITH_STATS
             verifier
#endif  // UNODB_DETAIL_WITH_STATS
      ) {
#ifdef UNODB_DETAIL_WITH_STATS
        verifier.assert_node_counts({5, 0, 1, 0, 0});
        verifier.assert_growing_inodes({1, 1, 0, 0});
#endif  // UNODB_DETAIL_WITH_STATS
      });
}

UNODB_TYPED_TEST(ARTOOMTest, Node16KeyPrefixSplit) {
  oom_insert_test<TypeParam>(
      3,
      [](unodb::test::tree_verifier<TypeParam>& verifier) {
        verifier.insert_key_range(10, 5);
#ifdef UNODB_DETAIL_WITH_STATS
        verifier.assert_node_counts({5, 0, 1, 0, 0});
        verifier.assert_growing_inodes({1, 1, 0, 0});
        verifier.assert_key_prefix_splits(0);
#endif  // UNODB_DETAIL_WITH_STATS
      },
      // Insert a value that does share full prefix with the current Node16
      0x1020, unodb::test_data::test_values[0],
      [](unodb::test::tree_verifier<TypeParam>&
#ifdef UNODB_DETAIL_WITH_STATS
             verifier
#endif  // UNODB_DETAIL_WITH_STATS
      ) {
#ifdef UNODB_DETAIL_WITH_STATS
        verifier.assert_node_counts({6, 1, 1, 0, 0});
        verifier.assert_growing_inodes({2, 1, 0, 0});
        verifier.assert_key_prefix_splits(1);
#endif  // UNODB_DETAIL_WITH_STATS
      });
}

UNODB_TYPED_TEST(ARTOOMTest, Node48) {
  oom_insert_test<TypeParam>(
      3,
      [](unodb::test::tree_verifier<TypeParam>& verifier) {
        verifier.insert_key_range(0, 16);
#ifdef UNODB_DETAIL_WITH_STATS
        verifier.assert_node_counts({16, 0, 1, 0, 0});
        verifier.assert_growing_inodes({1, 1, 0, 0});
#endif  // UNODB_DETAIL_WITH_STATS
      },
      16, unodb::test_data::test_values[0],
      [](unodb::test::tree_verifier<TypeParam>&
#ifdef UNODB_DETAIL_WITH_STATS
             verifier
#endif  // UNODB_DETAIL_WITH_STATS
      ) {
#ifdef UNODB_DETAIL_WITH_STATS
        verifier.assert_node_counts({17, 0, 0, 1, 0});
        verifier.assert_growing_inodes({1, 1, 1, 0});
#endif  // UNODB_DETAIL_WITH_STATS
      });
}

UNODB_TYPED_TEST(ARTOOMTest, Node48KeyPrefixSplit) {
  oom_insert_test<TypeParam>(
      3,
      [](unodb::test::tree_verifier<TypeParam>& verifier) {
        verifier.insert_key_range(10, 17);
#ifdef UNODB_DETAIL_WITH_STATS
        verifier.assert_node_counts({17, 0, 0, 1, 0});
        verifier.assert_growing_inodes({1, 1, 1, 0});
        verifier.assert_key_prefix_splits(0);
#endif  // UNODB_DETAIL_WITH_STATS
      },
      // Insert a value that does share full prefix with the current Node48
      0x100020, unodb::test_data::test_values[0],
      [](unodb::test::tree_verifier<TypeParam>&
#ifdef UNODB_DETAIL_WITH_STATS
             verifier
#endif  // UNODB_DETAIL_WITH_STATS
      ) {
#ifdef UNODB_DETAIL_WITH_STATS
        verifier.assert_node_counts({18, 1, 0, 1, 0});
        verifier.assert_growing_inodes({2, 1, 1, 0});
        verifier.assert_key_prefix_splits(1);
#endif  // UNODB_DETAIL_WITH_STATS
      });
}

UNODB_TYPED_TEST(ARTOOMTest, Node256) {
  oom_insert_test<TypeParam>(
      3,
      [](unodb::test::tree_verifier<TypeParam>& verifier) {
        verifier.insert_key_range(0, 48);
#ifdef UNODB_DETAIL_WITH_STATS
        verifier.assert_node_counts({48, 0, 0, 1, 0});
        verifier.assert_growing_inodes({1, 1, 1, 0});
#endif  // UNODB_DETAIL_WITH_STATS
      },
      49, unodb::test_data::test_values[0],
      [](unodb::test::tree_verifier<TypeParam>&
#ifdef UNODB_DETAIL_WITH_STATS
             verifier
#endif  // UNODB_DETAIL_WITH_STATS
      ) {
#ifdef UNODB_DETAIL_WITH_STATS
        verifier.assert_node_counts({49, 0, 0, 0, 1});
        verifier.assert_growing_inodes({1, 1, 1, 1});
#endif  // UNODB_DETAIL_WITH_STATS
      });
}

UNODB_TYPED_TEST(ARTOOMTest, Node256KeyPrefixSplit) {
  oom_insert_test<TypeParam>(
      3,
      [](unodb::test::tree_verifier<TypeParam>& verifier) {
        verifier.insert_key_range(20, 49);
#ifdef UNODB_DETAIL_WITH_STATS
        verifier.assert_node_counts({49, 0, 0, 0, 1});
        verifier.assert_growing_inodes({1, 1, 1, 1});
        verifier.assert_key_prefix_splits(0);
#endif  // UNODB_DETAIL_WITH_STATS
      },
      // Insert a value that does share full prefix with the current Node48
      0x100020, unodb::test_data::test_values[0],
      [](unodb::test::tree_verifier<TypeParam>&
#ifdef UNODB_DETAIL_WITH_STATS
             verifier
#endif  // UNODB_DETAIL_WITH_STATS
      ) {
#ifdef UNODB_DETAIL_WITH_STATS
        verifier.assert_node_counts({50, 1, 0, 0, 1});
        verifier.assert_growing_inodes({2, 1, 1, 1});
        verifier.assert_key_prefix_splits(1);
#endif  // UNODB_DETAIL_WITH_STATS
      });
}

UNODB_TYPED_TEST(ARTOOMTest, Node16ShrinkToNode4) {
  oom_remove_test<TypeParam>(
      2,
      [](unodb::test::tree_verifier<TypeParam>& verifier) {
        verifier.insert_key_range(1, 5);
#ifdef UNODB_DETAIL_WITH_STATS
        verifier.assert_node_counts({5, 0, 1, 0, 0});
        verifier.assert_shrinking_inodes({0, 0, 0, 0});
#endif  // UNODB_DETAIL_WITH_STATS
      },
      2,
      [](unodb::test::tree_verifier<TypeParam>&
#ifdef UNODB_DETAIL_WITH_STATS
             verifier
#endif  // UNODB_DETAIL_WITH_STATS
      ) {
#ifdef UNODB_DETAIL_WITH_STATS
        verifier.assert_shrinking_inodes({0, 1, 0, 0});
        verifier.assert_node_counts({4, 1, 0, 0, 0});
#endif  // UNODB_DETAIL_WITH_STATS
      });
}

UNODB_TYPED_TEST(ARTOOMTest, Node48ShrinkToNode16) {
  oom_remove_test<TypeParam>(
      2,
      [](unodb::test::tree_verifier<TypeParam>& verifier) {
        verifier.insert_key_range(0x80, 17);
#ifdef UNODB_DETAIL_WITH_STATS
        verifier.assert_node_counts({17, 0, 0, 1, 0});
        verifier.assert_shrinking_inodes({0, 0, 0, 0});
#endif  // UNODB_DETAIL_WITH_STATS
      },
      0x85,
      [](unodb::test::tree_verifier<TypeParam>&
#ifdef UNODB_DETAIL_WITH_STATS
             verifier
#endif  // UNODB_DETAIL_WITH_STATS
      ) {
#ifdef UNODB_DETAIL_WITH_STATS
        verifier.assert_shrinking_inodes({0, 0, 1, 0});
        verifier.assert_node_counts({16, 0, 1, 0, 0});
#endif  // UNODB_DETAIL_WITH_STATS
      });
}

UNODB_TYPED_TEST(ARTOOMTest, Node256ShrinkToNode48) {
  oom_remove_test<TypeParam>(
      2,
      [](unodb::test::tree_verifier<TypeParam>& verifier) {
        verifier.insert_key_range(1, 49);
#ifdef UNODB_DETAIL_WITH_STATS
        verifier.assert_node_counts({49, 0, 0, 0, 1});
        verifier.assert_shrinking_inodes({0, 0, 0, 0});
#endif  // UNODB_DETAIL_WITH_STATS
      },
      25,
      [](unodb::test::tree_verifier<TypeParam>&
#ifdef UNODB_DETAIL_WITH_STATS
             verifier
#endif  // UNODB_DETAIL_WITH_STATS
      ) {
#ifdef UNODB_DETAIL_WITH_STATS
        verifier.assert_shrinking_inodes({0, 0, 0, 1});
        verifier.assert_node_counts({48, 0, 0, 1, 0});
#endif  // UNODB_DETAIL_WITH_STATS
      });
}

// No-op scan visitor: lets a scan run to completion without perturbing the
// allocation count. Generic so it deduces the right visitor<iterator>& for
// every DB type.
constexpr auto oom_scan_noop_visitor = [](const auto&) noexcept {
  return false;
};

// Upper bound on the heap allocations a scan of the 16-key test tree makes (see
// oom_scan_test); not an exact count.
constexpr unsigned oom_scan_fail_limit = 20;

UNODB_TYPED_TEST(ARTOOMTest, Scan) {
  oom_scan_test<TypeParam>(oom_scan_fail_limit, [](TypeParam& db) {
    db.scan(oom_scan_noop_visitor);
  });
}

// ===================================================================
// key_view OOM tests: exercise build_chain allocation failure paths.
// build_chain is only invoked when full_key_in_inode_path is true
// (i.e., Key = key_view) and the key is long enough to need chain I4
// nodes beyond the dispatch byte.
//
// Allocation counts differ between VIS (no leaf allocation) and leaf-based
// paths.  VIS packs the value into the child slot; leaf-based allocates a
// leaf node.  The fail_limit must be exactly (allocations needed + 1).
//
// Nonfull: VIS = chain I4 only (1 alloc, limit 2)
//          Leaf = leaf + chain I4 (2 allocs, limit 3)
// Grow:    VIS = I16 create + chain I4 (2 allocs, limit 3)
//          Leaf = leaf + I16 create + chain I4 (3 allocs, limit 4)
// Prefix split: VIS = I4 create + chain I4 (2 allocs, limit 3)
//               Leaf = leaf + I4 create + chain I4 (3 allocs, limit 4)
template <class Db>
constexpr unsigned chain_oom_limit(unsigned vis_allocs) {
  if constexpr (std::is_same_v<typename Db::value_type, unodb::value_view>)
    return vis_allocs + 2;  // +1 for leaf, +1 for success iteration
  else
    return vis_allocs + 1;  // +1 for success iteration
}
// ===================================================================

template <class Db>
class ARTKeyViewOOMTest : public ::testing::Test {
 public:
  using Test::Test;
};

using ARTKeyViewTypes =
    ::testing::Types<unodb::test::key_view_u64val_db, unodb::test::key_view_db,
                     unodb::test::key_view_u64val_olc_db,
                     unodb::test::key_view_olc_db>;

UNODB_TYPED_TEST_SUITE(ARTKeyViewOOMTest, ARTKeyViewTypes)

// Insert 3 short (1-byte) keys into I4, then insert a long (9-byte) key.
// The I4 has room (nonfull path). build_chain allocates chain I4 node(s).
// OOM during build_chain must leave tree consistent.
UNODB_TYPED_TEST(ARTKeyViewOOMTest, BuildChainNonfull) {
  const auto v = unodb::test::get_test_value<TypeParam>(0);
  const auto v_long = unodb::test::get_test_value<TypeParam>(1);

  unodb::key_encoder enc1;
  unodb::key_encoder enc2;
  unodb::key_encoder enc3;
  unodb::key_encoder enc_long;
  const auto short1 = unodb::test_data::make_short_key(enc1, 1);
  const auto short2 = unodb::test_data::make_short_key(enc2, 2);
  const auto short3 = unodb::test_data::make_short_key(enc3, 3);
  const auto long_key = unodb::test_data::make_key(enc_long, 0x10, 1);

  oom_test<TypeParam>(
      chain_oom_limit<TypeParam>(1),
      [&](unodb::test::tree_verifier<TypeParam>& verifier) {
        verifier.insert(short1, v);
        verifier.insert(short2, v);
        verifier.insert(short3, v);
      },
      [&](unodb::test::tree_verifier<TypeParam>& verifier) {
        verifier.insert(long_key, v_long);
      },
      [&](unodb::test::tree_verifier<TypeParam>& verifier) {
        // After OOM, the tree should be unchanged — the long key should
        // not be present, and the tree should be fully consistent.
        // With the current bug, the bare child is left in the tree,
        // corrupting memory accounting.
        UNODB_ASSERT_FALSE(verifier.get_db().get(long_key).has_value());
      },
      [](unodb::test::tree_verifier<TypeParam>&) {});
}

// Insert 4 short (1-byte) keys filling I4, then insert a long (9-byte) key.
// Triggers I4→I16 grow, then build_chain on the new child slot.
// OOM during build_chain must leave tree consistent.
UNODB_TYPED_TEST(ARTKeyViewOOMTest, BuildChainGrow) {
  const auto v = unodb::test::get_test_value<TypeParam>(0);
  const auto v_long = unodb::test::get_test_value<TypeParam>(1);

  unodb::key_encoder enc1;
  unodb::key_encoder enc2;
  unodb::key_encoder enc3;
  unodb::key_encoder enc4;
  unodb::key_encoder enc_long;
  const auto short1 = unodb::test_data::make_short_key(enc1, 1);
  const auto short2 = unodb::test_data::make_short_key(enc2, 2);
  const auto short3 = unodb::test_data::make_short_key(enc3, 3);
  const auto short4 = unodb::test_data::make_short_key(enc4, 4);
  const auto long_key = unodb::test_data::make_key(enc_long, 0x10, 1);

  oom_test<TypeParam>(
      chain_oom_limit<TypeParam>(2),
      [&](unodb::test::tree_verifier<TypeParam>& verifier) {
        verifier.insert(short1, v);
        verifier.insert(short2, v);
        verifier.insert(short3, v);
        verifier.insert(short4, v);
      },
      [&](unodb::test::tree_verifier<TypeParam>& verifier) {
        verifier.insert(long_key, v_long);
      },
      [&](unodb::test::tree_verifier<TypeParam>& verifier) {
        UNODB_ASSERT_FALSE(verifier.get_db().get(long_key).has_value());
      },
      [](unodb::test::tree_verifier<TypeParam>&) {});
}

// Insert one 9-byte key, then insert another 9-byte key that diverges within
// the chain prefix. Triggers prefix split → new I4 → build_chain.
// OOM during build_chain must leave tree consistent.
//
// key1: 0x42 0x00 ... 0x01 (tag + uint64{1})
// key2: 0x42 0x80 ... 0x01 (tag + uint64 with high bit set in first byte)
// They share only the tag byte; diverge at byte 1 (within the chain prefix).
UNODB_TYPED_TEST(ARTKeyViewOOMTest, BuildChainPrefixSplit) {
  const auto v1 = unodb::test::get_test_value<TypeParam>(0);
  const auto v2 = unodb::test::get_test_value<TypeParam>(1);

  unodb::key_encoder enc1;
  unodb::key_encoder enc2;
  const auto key1 = unodb::test_data::make_key(enc1, 0x42, 1);
  // uint64 value with high bit set → first encoded byte is 0x80, diverges
  // at byte 1 from key1's 0x00.
  const auto key2 =
      unodb::test_data::make_key(enc2, 0x42, 0x8000000000000001ULL);

  oom_test<TypeParam>(
      chain_oom_limit<TypeParam>(2),
      [&](unodb::test::tree_verifier<TypeParam>& verifier) {
        verifier.insert(key1, v1);
      },
      [&](unodb::test::tree_verifier<TypeParam>& verifier) {
        verifier.insert(key2, v2);
      },
      [&](unodb::test::tree_verifier<TypeParam>& verifier) {
        UNODB_ASSERT_FALSE(verifier.get_db().get(key2).has_value());
      },
      [](unodb::test::tree_verifier<TypeParam>&) {});
}

// Multi-node chain: key long enough to produce 2 chain I4 nodes.
// Exercises the build_chain loop (owns_current=true) cleanup path.
// Encoded key: uint8{0x10} + uint64{1} + uint64{2} = 17 bytes.
// Chain starts at depth 1 → 16 bytes → 2 chain I4 nodes.
UNODB_TYPED_TEST(ARTKeyViewOOMTest, BuildChainMultiNode) {
  const auto v = unodb::test::get_test_value<TypeParam>(0);
  const auto v_long = unodb::test::get_test_value<TypeParam>(1);

  unodb::key_encoder enc1;
  unodb::key_encoder enc2;
  unodb::key_encoder enc3;
  unodb::key_encoder enc_long;
  const auto short1 = unodb::test_data::make_short_key(enc1, 1);
  const auto short2 = unodb::test_data::make_short_key(enc2, 2);
  const auto short3 = unodb::test_data::make_short_key(enc3, 3);
  const auto long_key = enc_long.encode(std::uint8_t{0x10})
                            .encode(std::uint64_t{1})
                            .encode(std::uint64_t{2})
                            .get_key_view();

  oom_test<TypeParam>(
      chain_oom_limit<TypeParam>(2),
      [&](unodb::test::tree_verifier<TypeParam>& verifier) {
        verifier.insert(short1, v);
        verifier.insert(short2, v);
        verifier.insert(short3, v);
      },
      [&](unodb::test::tree_verifier<TypeParam>& verifier) {
        verifier.insert(long_key, v_long);
      },
      [&](unodb::test::tree_verifier<TypeParam>& verifier) {
        UNODB_ASSERT_FALSE(verifier.get_db().get(long_key).has_value());
      },
      [](unodb::test::tree_verifier<TypeParam>&) {});
}

// ===================================================================
// bulk_load OOM tests — strong exception guarantee: tree stays empty
// ===================================================================

template <class TypeParam>
void bulk_load_oom_test(
    unsigned fail_limit,
    const std::vector<std::pair<std::uint64_t, unodb::value_view>>& kv) {
  unsigned fail_n;
  for (fail_n = 1; fail_n <= fail_limit; ++fail_n) {
    TypeParam test_db;

    const bool loaded = !unodb::test::throws_bad_alloc(
        fail_n, [&test_db, &kv] { test_db.bulk_load(kv.begin(), kv.end()); });
    if (loaded) {  // Success: we've found the limit
      UNODB_ASSERT_FALSE(test_db.empty());
      for (const auto& [k, v] : kv) {
        const auto result = test_db.get(k);
        UNODB_ASSERT_TRUE(TypeParam::key_found(result));
        unodb::test::detail::assert_value_eq<TypeParam>(result, v);
      }
      return;
    }
    // Strong guarantee: tree must be empty after failed bulk_load
    UNODB_ASSERT_TRUE(test_db.empty());
#ifdef UNODB_DETAIL_WITH_STATS
    UNODB_ASSERT_EQ(test_db.get_current_memory_use(), 0);
#endif
  }
  FAIL() << "bulk_load did not succeed within " << fail_limit << " allocations";
}

// Small tree (single leaf → one allocation)
UNODB_TYPED_TEST(ARTOOMTest, BulkLoadSingleKey) {
  constexpr auto val = unodb::test_data::test_values[0];
  const std::vector<std::pair<std::uint64_t, unodb::value_view>> kv{{42, val}};
  bulk_load_oom_test<TypeParam>(5, kv);
}

// Tree that creates one inode4 (4 leaves + 1 inode4)
UNODB_TYPED_TEST(ARTOOMTest, BulkLoadInode4) {
  std::vector<std::pair<std::uint64_t, unodb::value_view>> kv;
  kv.reserve(4);
  for (std::uint64_t i = 0; i < 4; ++i)
    kv.emplace_back(i << 56U, unodb::test::get_test_value<TypeParam>(i));
  bulk_load_oom_test<TypeParam>(10, kv);
}

// Tree that creates an inode16 (10 leaves + 1 inode16)
UNODB_TYPED_TEST(ARTOOMTest, BulkLoadInode16) {
  std::vector<std::pair<std::uint64_t, unodb::value_view>> kv;
  kv.reserve(10);
  for (std::uint64_t i = 0; i < 10; ++i)
    kv.emplace_back(i << 56U, unodb::test::get_test_value<TypeParam>(i));
  bulk_load_oom_test<TypeParam>(15, kv);
}

// Tree that creates an inode48 (20 leaves + 1 inode48)
UNODB_TYPED_TEST(ARTOOMTest, BulkLoadInode48) {
  std::vector<std::pair<std::uint64_t, unodb::value_view>> kv;
  kv.reserve(20);
  for (std::uint64_t i = 0; i < 20; ++i)
    kv.emplace_back(i << 56U, unodb::test::get_test_value<TypeParam>(i));
  bulk_load_oom_test<TypeParam>(30, kv);
}

// Tree with nested inodes (two inode4s under one root inode4)
UNODB_TYPED_TEST(ARTOOMTest, BulkLoadNested) {
  std::vector<std::pair<std::uint64_t, unodb::value_view>> kv;
  kv.reserve(8);
  for (std::uint64_t i = 0; i < 4; ++i)
    kv.emplace_back((1ULL << 56U) | (i << 48U),
                    unodb::test::get_test_value<TypeParam>(i));
  for (std::uint64_t i = 0; i < 4; ++i)
    kv.emplace_back((2ULL << 56U) | (i << 48U),
                    unodb::test::get_test_value<TypeParam>(i + 4));
  bulk_load_oom_test<TypeParam>(20, kv);
}

}  // namespace

#endif  // #ifndef NDEBUG
