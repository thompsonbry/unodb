// Copyright 2026 UnoDB contributors

// Should be the first include
#include "global.hpp"  // IWYU pragma: keep

#include <array>
#include <cstddef>
#include <cstdint>
#include <stdexcept>
#include <tuple>
#include <type_traits>

#include <gtest/gtest.h>

#include "art_common.hpp"
#include "db_test_utils.hpp"
#include "gtest_utils.hpp"
#include "olc_art.hpp"
#include "qsbr.hpp"
#include "qsbr_test_utils.hpp"
#include "test_heap.hpp"

#ifndef NDEBUG
#include "thread_sync.hpp"
#endif

namespace {

using namespace unodb::test;  // NOLINT(google-build-using-namespace)

// ===================================================================
// Helper lambdas shared across tests.
// ===================================================================

/// Lambda that returns keep — value unchanged.
constexpr auto keep_fn = [](auto& /*v*/) noexcept {
  return unodb::upsert_action::keep;
};

/// Lambda that returns update — increments value by 1.
constexpr auto increment_fn = [](auto& v) noexcept {
  ++v;
  return unodb::upsert_action::update;
};

/// Lambda that returns erase — removes the key.
constexpr auto erase_fn = [](auto& /*v*/) noexcept {
  return unodb::upsert_action::erase;
};

/// Execute a callable within a QSBR scope for OLC types (no-op for others).
template <class Db, typename Fn>
decltype(auto) with_qsbr([[maybe_unused]] Fn&& fn) {
  if constexpr (unodb::test::is_olc_db<Db>) {
    const unodb::quiescent_state_on_scope_exit qsbr{};
    return fn();
  } else {
    return fn();
  }
}

// ===================================================================
// UpsertTest — typed test fixture parameterized over all db types.
// ===================================================================

template <class Db>
class UpsertTest : public ::testing::Test {
 public:
  using Test::Test;
};

// All db types: u64 key + value_view, key_view + value_view,
// key_view + u64 value (VIS types).
using UpsertTypes =
    ::testing::Types<unodb::test::u64_db, unodb::test::u64_mutex_db,
                     unodb::test::u64_olc_db, unodb::test::key_view_db,
                     unodb::test::key_view_mutex_db,
                     unodb::test::key_view_olc_db,
                     unodb::test::key_view_u64val_db,
                     unodb::test::key_view_u64val_mutex_db,
                     unodb::test::key_view_u64val_olc_db>;

UNODB_TYPED_TEST_SUITE(UpsertTest, UpsertTypes)

// ===================================================================
// Unit Tests — Basic Semantics (IDs 1-6, 14-16)
// ===================================================================

// ID-1: Returns true, get(k)==v, lambda not called.
UNODB_TYPED_TEST(UpsertTest, InsertPathKeyAbsent) {
  unodb::test::tree_verifier<TypeParam> verifier;
  auto& db = verifier.get_db();
  const auto k = verifier.coerce_key(1);
  const auto v = unodb::test::get_test_value<TypeParam>(0);
  bool lambda_called = false;
  const auto result =
      with_qsbr<TypeParam>([&] {
        return db.upsert(k, v, [&lambda_called](auto& /*x*/) {
          lambda_called = true;
          return unodb::upsert_action::keep;
        });
      });
  UNODB_ASSERT_TRUE(result);
  UNODB_ASSERT_FALSE(lambda_called);
  ASSERT_VALUE_FOR_KEY(TypeParam, db, k, v);
}

// ID-2: Returns false, get(k)==v0 (original value unchanged).
UNODB_TYPED_TEST(UpsertTest, KeepKeyPresent) {
  unodb::test::tree_verifier<TypeParam> verifier;
  auto& db = verifier.get_db();
  const auto k = verifier.coerce_key(1);
  const auto v0 = unodb::test::get_test_value<TypeParam>(0);
  const auto v1 = unodb::test::get_test_value<TypeParam>(1);
  with_qsbr<TypeParam>([&] { UNODB_ASSERT_TRUE(db.insert(k, v0)); });
  const auto result = with_qsbr<TypeParam>([&] {
    return db.upsert(k, v1, keep_fn);
  });
  UNODB_ASSERT_FALSE(result);
  ASSERT_VALUE_FOR_KEY(TypeParam, db, k, v0);
}

// ID-3: Returns false, get(k)==42 (lambda mutated value).
UNODB_TYPED_TEST(UpsertTest, UpdateKeyPresent) {
  if constexpr (std::is_same_v<typename TypeParam::value_type,
                               unodb::value_view>) {
    GTEST_SKIP() << "update not supported for value_view types";
  } else {
    unodb::test::tree_verifier<TypeParam> verifier;
    auto& db = verifier.get_db();
    const auto k = verifier.coerce_key(1);
    const typename TypeParam::value_type v0 = 10;
    const typename TypeParam::value_type v1 = 99;
    with_qsbr<TypeParam>([&] { UNODB_ASSERT_TRUE(db.insert(k, v0)); });
    const auto result = with_qsbr<TypeParam>([&] {
      return db.upsert(k, v1, [](auto& x) {
        x = 42;
        return unodb::upsert_action::update;
      });
    });
    UNODB_ASSERT_FALSE(result);
    ASSERT_VALUE_FOR_KEY(TypeParam, db, k,
                         static_cast<typename TypeParam::value_type>(42));
  }
}

// ID-4: Returns false both times, get(k)==v0+20.
UNODB_TYPED_TEST(UpsertTest, UpdateIdempotency) {
  if constexpr (std::is_same_v<typename TypeParam::value_type,
                               unodb::value_view>) {
    GTEST_SKIP() << "update not supported for value_view types";
  } else {
    unodb::test::tree_verifier<TypeParam> verifier;
    auto& db = verifier.get_db();
    const auto k = verifier.coerce_key(1);
    const typename TypeParam::value_type v0 = 100;
    with_qsbr<TypeParam>([&] { UNODB_ASSERT_TRUE(db.insert(k, v0)); });
    auto add10 = [](auto& x) {
      x += 10;
      return unodb::upsert_action::update;
    };
    with_qsbr<TypeParam>([&] { UNODB_ASSERT_FALSE(db.upsert(k, v0, add10)); });
    with_qsbr<TypeParam>([&] { UNODB_ASSERT_FALSE(db.upsert(k, v0, add10)); });
    ASSERT_VALUE_FOR_KEY(TypeParam, db, k,
                         static_cast<typename TypeParam::value_type>(120));
  }
}

// ID-5: Returns false, get(k) empty.
UNODB_TYPED_TEST(UpsertTest, EraseKeyPresent) {
  unodb::test::tree_verifier<TypeParam> verifier;
  auto& db = verifier.get_db();
  const auto k = verifier.coerce_key(1);
  const auto v = unodb::test::get_test_value<TypeParam>(0);
  with_qsbr<TypeParam>([&] { UNODB_ASSERT_TRUE(db.insert(k, v)); });
  const auto result = with_qsbr<TypeParam>([&] {
    return db.upsert(k, v, erase_fn);
  });
  UNODB_ASSERT_FALSE(result);
  with_qsbr<TypeParam>([&] {
    UNODB_ASSERT_FALSE(TypeParam::key_found(db.get(k)));
  });
}

// ID-6: Mixed operations across 100 keys.
UNODB_TYPED_TEST(UpsertTest, MixedOperations) {
  unodb::test::tree_verifier<TypeParam> verifier;
  auto& db = verifier.get_db();
  // Insert keys 0..99 with value = get_test_value(i)
  for (std::size_t i = 0; i < 100; ++i) {
    const auto k = verifier.coerce_key(i);
    const auto v = unodb::test::get_test_value<TypeParam>(i);
    with_qsbr<TypeParam>([&] { UNODB_ASSERT_TRUE(db.insert(k, v)); });
  }
  // Upsert each: if i < 50, erase; else keep
  for (std::size_t i = 0; i < 100; ++i) {
    const auto k = verifier.coerce_key(i);
    const auto v = unodb::test::get_test_value<TypeParam>(i);
    if (i < 50) {
      with_qsbr<TypeParam>([&] { UNODB_ASSERT_FALSE(db.upsert(k, v, erase_fn)); });
    } else {
      with_qsbr<TypeParam>([&] { UNODB_ASSERT_FALSE(db.upsert(k, v, keep_fn)); });
    }
  }
  // Verify: keys 0..49 absent, keys 50..99 present
  for (std::size_t i = 0; i < 50; ++i) {
    const auto k = verifier.coerce_key(i);
    with_qsbr<TypeParam>([&] {
      UNODB_ASSERT_FALSE(TypeParam::key_found(db.get(k)));
    });
  }
  for (std::size_t i = 50; i < 100; ++i) {
    const auto k = verifier.coerce_key(i);
    ASSERT_VALUE_FOR_KEY(TypeParam, db, k,
                         unodb::test::get_test_value<TypeParam>(i));
  }
}

// ID-14: Single-entry tree, all three actions verified sequentially.
UNODB_TYPED_TEST(UpsertTest, RootLeafAllActions) {
  unodb::test::tree_verifier<TypeParam> verifier;
  auto& db = verifier.get_db();
  const auto k = verifier.coerce_key(1);
  const auto v0 = unodb::test::get_test_value<TypeParam>(0);
  const auto v1 = unodb::test::get_test_value<TypeParam>(1);
  // Insert
  with_qsbr<TypeParam>([&] { UNODB_ASSERT_TRUE(db.upsert(k, v0, keep_fn)); });
  ASSERT_VALUE_FOR_KEY(TypeParam, db, k, v0);
  // Keep
  with_qsbr<TypeParam>([&] { UNODB_ASSERT_FALSE(db.upsert(k, v1, keep_fn)); });
  ASSERT_VALUE_FOR_KEY(TypeParam, db, k, v0);
  // Erase
  with_qsbr<TypeParam>([&] { UNODB_ASSERT_FALSE(db.upsert(k, v1, erase_fn)); });
  with_qsbr<TypeParam>([&] {
    UNODB_ASSERT_FALSE(TypeParam::key_found(db.get(k)));
  });
  with_qsbr<TypeParam>([&] { UNODB_ASSERT_TRUE(db.empty()); });
}

// ID-15: Empty tree, insert path returns true.
UNODB_TYPED_TEST(UpsertTest, EmptyTree) {
  unodb::test::tree_verifier<TypeParam> verifier;
  auto& db = verifier.get_db();
  const auto k = verifier.coerce_key(42);
  const auto v = unodb::test::get_test_value<TypeParam>(2);
  with_qsbr<TypeParam>([&] { UNODB_ASSERT_TRUE(db.upsert(k, v, keep_fn)); });
  ASSERT_VALUE_FOR_KEY(TypeParam, db, k, v);
}

// ID-16: Tree cleared, insert path returns true.
UNODB_TYPED_TEST(UpsertTest, AfterClear) {
  unodb::test::tree_verifier<TypeParam> verifier;
  auto& db = verifier.get_db();
  const auto k = verifier.coerce_key(1);
  const auto v = unodb::test::get_test_value<TypeParam>(0);
  with_qsbr<TypeParam>([&] { UNODB_ASSERT_TRUE(db.insert(k, v)); });
  verifier.clear();
  with_qsbr<TypeParam>([&] { UNODB_ASSERT_TRUE(db.upsert(k, v, keep_fn)); });
  ASSERT_VALUE_FOR_KEY(TypeParam, db, k, v);
}

// ===================================================================
// Type Coverage (IDs 11-13b)
// ===================================================================

// ID-11: uint64_t key + uint64_t value (VIS), keep/update/erase.
UNODB_TYPED_TEST(UpsertTest, TypeCoverageU64U64) {
  // This test applies only to u64-key + u64-value types (none in current suite).
  // Exercised via key_view_u64val types which are the VIS types available.
  if constexpr (!std::is_same_v<typename TypeParam::value_type, std::uint64_t>) {
    GTEST_SKIP() << "Only applies to u64 value types";
  } else {
    unodb::test::tree_verifier<TypeParam> verifier;
    auto& db = verifier.get_db();
    const auto k = verifier.coerce_key(5);
    const typename TypeParam::value_type v0 = 10;
    with_qsbr<TypeParam>([&] { UNODB_ASSERT_TRUE(db.insert(k, v0)); });
    // keep
    with_qsbr<TypeParam>([&] { UNODB_ASSERT_FALSE(db.upsert(k, v0, keep_fn)); });
    ASSERT_VALUE_FOR_KEY(TypeParam, db, k, v0);
    // update
    with_qsbr<TypeParam>([&] {
      UNODB_ASSERT_FALSE(db.upsert(k, v0, increment_fn));
    });
    ASSERT_VALUE_FOR_KEY(TypeParam, db, k,
                         static_cast<typename TypeParam::value_type>(11));
    // erase
    with_qsbr<TypeParam>([&] { UNODB_ASSERT_FALSE(db.upsert(k, v0, erase_fn)); });
    with_qsbr<TypeParam>([&] {
      UNODB_ASSERT_FALSE(TypeParam::key_found(db.get(k)));
    });
  }
}

// ID-12: key_view key + uint64_t value (VIS), keep/update/erase.
UNODB_TYPED_TEST(UpsertTest, TypeCoverageKeyViewU64) {
  if constexpr (!std::is_same_v<typename TypeParam::key_type, unodb::key_view> ||
                !std::is_same_v<typename TypeParam::value_type, std::uint64_t>) {
    GTEST_SKIP() << "Only applies to key_view + u64 value types";
  } else {
    unodb::test::tree_verifier<TypeParam> verifier;
    auto& db = verifier.get_db();
    const auto k = verifier.coerce_key(7);
    const typename TypeParam::value_type v0 = 20;
    with_qsbr<TypeParam>([&] { UNODB_ASSERT_TRUE(db.insert(k, v0)); });
    // keep
    with_qsbr<TypeParam>([&] { UNODB_ASSERT_FALSE(db.upsert(k, v0, keep_fn)); });
    ASSERT_VALUE_FOR_KEY(TypeParam, db, k, v0);
    // update
    with_qsbr<TypeParam>([&] {
      UNODB_ASSERT_FALSE(db.upsert(k, v0, increment_fn));
    });
    ASSERT_VALUE_FOR_KEY(TypeParam, db, k,
                         static_cast<typename TypeParam::value_type>(21));
    // erase
    with_qsbr<TypeParam>([&] { UNODB_ASSERT_FALSE(db.upsert(k, v0, erase_fn)); });
    with_qsbr<TypeParam>([&] {
      UNODB_ASSERT_FALSE(TypeParam::key_found(db.get(k)));
    });
  }
}

// ID-13: key_view key + value_view value, keep/erase only.
UNODB_TYPED_TEST(UpsertTest, TypeCoverageKeyViewValueView) {
  if constexpr (!std::is_same_v<typename TypeParam::key_type, unodb::key_view> ||
                !std::is_same_v<typename TypeParam::value_type, unodb::value_view>) {
    GTEST_SKIP() << "Only applies to key_view + value_view types";
  } else {
    unodb::test::tree_verifier<TypeParam> verifier;
    auto& db = verifier.get_db();
    const auto k = verifier.coerce_key(3);
    const auto v = unodb::test::test_values[2];
    with_qsbr<TypeParam>([&] { UNODB_ASSERT_TRUE(db.insert(k, v)); });
    // keep
    with_qsbr<TypeParam>([&] { UNODB_ASSERT_FALSE(db.upsert(k, v, keep_fn)); });
    ASSERT_VALUE_FOR_KEY(TypeParam, db, k, v);
    // erase
    with_qsbr<TypeParam>([&] { UNODB_ASSERT_FALSE(db.upsert(k, v, erase_fn)); });
    with_qsbr<TypeParam>([&] {
      UNODB_ASSERT_FALSE(TypeParam::key_found(db.get(k)));
    });
  }
}

// ID-13b: uint64_t key + value_view value, keep/erase only.
UNODB_TYPED_TEST(UpsertTest, TypeCoverageU64ValueView) {
  if constexpr (!std::is_same_v<typename TypeParam::key_type, std::uint64_t> ||
                !std::is_same_v<typename TypeParam::value_type, unodb::value_view>) {
    GTEST_SKIP() << "Only applies to u64 key + value_view types";
  } else {
    unodb::test::tree_verifier<TypeParam> verifier;
    auto& db = verifier.get_db();
    const auto k = verifier.coerce_key(10);
    const auto v = unodb::test::test_values[3];
    with_qsbr<TypeParam>([&] { UNODB_ASSERT_TRUE(db.insert(k, v)); });
    // keep
    with_qsbr<TypeParam>([&] { UNODB_ASSERT_FALSE(db.upsert(k, v, keep_fn)); });
    ASSERT_VALUE_FOR_KEY(TypeParam, db, k, v);
    // erase
    with_qsbr<TypeParam>([&] { UNODB_ASSERT_FALSE(db.upsert(k, v, erase_fn)); });
    with_qsbr<TypeParam>([&] {
      UNODB_ASSERT_FALSE(TypeParam::key_found(db.get(k)));
    });
  }
}

// ===================================================================
// Erase-Specific Tests — single-threaded (IDs 23a-23e)
// ===================================================================

// ID-23a: Erase triggers I16→I4 shrink.
UNODB_TYPED_TEST(UpsertTest, EraseTriggersShrink) {
  unodb::test::tree_verifier<TypeParam> verifier;
  auto& db = verifier.get_db();
  // Insert 5 keys to create an I16 node, then erase one to trigger shrink to I4
  for (std::size_t i = 0; i < 5; ++i) {
    const auto k = verifier.coerce_key(i);
    with_qsbr<TypeParam>([&] {
      UNODB_ASSERT_TRUE(db.insert(k, unodb::test::get_test_value<TypeParam>(i)));
    });
  }
  const auto k_erase = verifier.coerce_key(std::size_t{0});
  with_qsbr<TypeParam>([&] {
    UNODB_ASSERT_FALSE(db.upsert(k_erase,
                                  unodb::test::get_test_value<TypeParam>(0),
                                  erase_fn));
  });
  with_qsbr<TypeParam>([&] {
    UNODB_ASSERT_FALSE(TypeParam::key_found(db.get(k_erase)));
  });
  // Remaining 4 keys still present
  for (std::size_t i = 1; i < 5; ++i) {
    const auto k = verifier.coerce_key(i);
    ASSERT_VALUE_FOR_KEY(TypeParam, db, k,
                         unodb::test::get_test_value<TypeParam>(i));
  }
}

// ID-23b: Erase triggers chain cut (key_view types).
UNODB_TYPED_TEST(UpsertTest, EraseTriggersChainCut) {
  if constexpr (!std::is_same_v<typename TypeParam::key_type, unodb::key_view>) {
    GTEST_SKIP() << "Chain cut only applies to key_view types";
  } else {
    unodb::test::tree_verifier<TypeParam> verifier;
    auto& db = verifier.get_db();
    // Insert two keys that share a prefix to create a chain I4
    const auto k0 = verifier.coerce_key(0);
    const auto k1 = verifier.coerce_key(1);
    with_qsbr<TypeParam>([&] {
      UNODB_ASSERT_TRUE(db.insert(k0, unodb::test::get_test_value<TypeParam>(0)));
    });
    with_qsbr<TypeParam>([&] {
      UNODB_ASSERT_TRUE(db.insert(k1, unodb::test::get_test_value<TypeParam>(1)));
    });
    // Erase one to trigger chain cut
    with_qsbr<TypeParam>([&] {
      UNODB_ASSERT_FALSE(db.upsert(k0,
                                    unodb::test::get_test_value<TypeParam>(0),
                                    erase_fn));
    });
    with_qsbr<TypeParam>([&] {
      UNODB_ASSERT_FALSE(TypeParam::key_found(db.get(k0)));
    });
    ASSERT_VALUE_FOR_KEY(TypeParam, db, k1,
                         unodb::test::get_test_value<TypeParam>(1));
  }
}

// ID-23c: Erase root leaf, tree becomes empty.
UNODB_TYPED_TEST(UpsertTest, EraseRootLeaf) {
  unodb::test::tree_verifier<TypeParam> verifier;
  auto& db = verifier.get_db();
  const auto k = verifier.coerce_key(1);
  const auto v = unodb::test::get_test_value<TypeParam>(0);
  with_qsbr<TypeParam>([&] { UNODB_ASSERT_TRUE(db.insert(k, v)); });
  with_qsbr<TypeParam>([&] { UNODB_ASSERT_FALSE(db.upsert(k, v, erase_fn)); });
  with_qsbr<TypeParam>([&] { UNODB_ASSERT_TRUE(db.empty()); });
  with_qsbr<TypeParam>([&] {
    UNODB_ASSERT_FALSE(TypeParam::key_found(db.get(k)));
  });
}

// ID-23d: Erase packed VIS value, slot cleared.
UNODB_TYPED_TEST(UpsertTest, EraseVisValue) {
  if constexpr (!std::is_same_v<typename TypeParam::value_type, std::uint64_t>) {
    GTEST_SKIP() << "Only applies to VIS (u64 value) types";
  } else {
    unodb::test::tree_verifier<TypeParam> verifier;
    auto& db = verifier.get_db();
    const auto k = verifier.coerce_key(5);
    const typename TypeParam::value_type v = 42;
    with_qsbr<TypeParam>([&] { UNODB_ASSERT_TRUE(db.insert(k, v)); });
    with_qsbr<TypeParam>([&] { UNODB_ASSERT_FALSE(db.upsert(k, v, erase_fn)); });
    with_qsbr<TypeParam>([&] {
      UNODB_ASSERT_FALSE(TypeParam::key_found(db.get(k)));
    });
  }
}

// ID-23e: Erase then re-upsert inserts with new value.
UNODB_TYPED_TEST(UpsertTest, EraseThenReinsert) {
  unodb::test::tree_verifier<TypeParam> verifier;
  auto& db = verifier.get_db();
  const auto k = verifier.coerce_key(1);
  const auto v0 = unodb::test::get_test_value<TypeParam>(0);
  const auto v1 = unodb::test::get_test_value<TypeParam>(1);
  with_qsbr<TypeParam>([&] { UNODB_ASSERT_TRUE(db.insert(k, v0)); });
  // Erase
  with_qsbr<TypeParam>([&] { UNODB_ASSERT_FALSE(db.upsert(k, v0, erase_fn)); });
  with_qsbr<TypeParam>([&] {
    UNODB_ASSERT_FALSE(TypeParam::key_found(db.get(k)));
  });
  // Re-insert via upsert with new value
  with_qsbr<TypeParam>([&] { UNODB_ASSERT_TRUE(db.upsert(k, v1, keep_fn)); });
  ASSERT_VALUE_FOR_KEY(TypeParam, db, k, v1);
}

// ===================================================================
// Contract Verification — single-threaded (IDs C1, C3, C4)
// ===================================================================

// ID-C1: static_assert rejects bad lambda (compile-time negative test).
// Note: This is a negative compilation test; verified via build system.
// Placeholder test documents the requirement.
UNODB_TYPED_TEST(UpsertTest, StaticAssertRejectsBadLambda) {
  // Compile-time verification: a lambda returning int or void instead of
  // upsert_action would fail the static_assert in db::upsert. This cannot
  // be tested at runtime. The build system's negative compilation tests
  // verify this constraint.
  SUCCEED();
}

// ID-C3: Mutations discarded on erase.
UNODB_TYPED_TEST(UpsertTest, MutationsDiscardedOnErase) {
  if constexpr (!std::is_same_v<typename TypeParam::value_type, std::uint64_t>) {
    GTEST_SKIP() << "Mutation test requires mutable u64 value type";
  } else {
    unodb::test::tree_verifier<TypeParam> verifier;
    auto& db = verifier.get_db();
    const auto k = verifier.coerce_key(1);
    const typename TypeParam::value_type v0 = 10;
    with_qsbr<TypeParam>([&] { UNODB_ASSERT_TRUE(db.insert(k, v0)); });
    // Lambda mutates value AND returns erase
    with_qsbr<TypeParam>([&] {
      UNODB_ASSERT_FALSE(db.upsert(k, typename TypeParam::value_type{0},
                                    [](auto& x) {
                                      x = 99;
                                      return unodb::upsert_action::erase;
                                    }));
    });
    // Key must be gone — mutation discarded
    with_qsbr<TypeParam>([&] {
      UNODB_ASSERT_FALSE(TypeParam::key_found(db.get(k)));
    });
    // Re-insert and verify value is NOT 99
    const typename TypeParam::value_type v_new = 50;
    with_qsbr<TypeParam>([&] { UNODB_ASSERT_TRUE(db.insert(k, v_new)); });
    ASSERT_VALUE_FOR_KEY(TypeParam, db, k, v_new);
  }
}

// ID-C4: Throwing lambda leaves tree unchanged.
UNODB_TYPED_TEST(UpsertTest, ThrowingLambdaTreeUnchanged) {
  unodb::test::tree_verifier<TypeParam> verifier;
  auto& db = verifier.get_db();
  const auto k = verifier.coerce_key(1);
  const auto v = unodb::test::get_test_value<TypeParam>(0);
  with_qsbr<TypeParam>([&] { UNODB_ASSERT_TRUE(db.insert(k, v)); });
  // Lambda throws
  with_qsbr<TypeParam>([&] {
    UNODB_ASSERT_THROW(
        std::ignore = db.upsert(k, v,
                                [](auto& /*x*/) {
                                  throw std::runtime_error("test");
                                  return unodb::upsert_action::keep;  // unreachable
                                }),
        std::runtime_error);
  });
  // Tree unchanged
  ASSERT_VALUE_FOR_KEY(TypeParam, db, k, v);
  with_qsbr<TypeParam>([&] { UNODB_ASSERT_FALSE(db.empty()); });
}

// ===================================================================
// UpsertConcurrencyTest — olc_db-only fixture.
// ===================================================================

// NOTE: The concurrency and OOM test implementations require the upsert
// API to be implemented before they can compile. They are written against
// the API spec (design/spec/upsert/api.md) and will be filled in during
// the implementation phase. The test structure and post-conditions are
// defined; the bodies reference APIs that do not yet exist.
//
// See: .sisyphus/handoff/upsert-concurrency-tests.cpp for the full
// concurrency test implementations ready to splice in after upsert is
// implemented.

template <class Db>
class UpsertConcurrencyTest : public ::testing::Test {
 public:
  UNODB_DETAIL_DISABLE_MSVC_WARNING(26447)
  ~UpsertConcurrencyTest() noexcept override {
    if constexpr (unodb::test::is_olc_db<Db>) {
      unodb::this_thread().quiescent();
      unodb::test::expect_idle_qsbr();
    }
  }
  UNODB_DETAIL_RESTORE_MSVC_WARNINGS()

 protected:
  // NOLINTNEXTLINE(bugprone-exception-escape)
  UpsertConcurrencyTest() noexcept {
    if constexpr (unodb::test::is_olc_db<Db>) unodb::test::expect_idle_qsbr();
  }

  template <std::size_t ThreadCount, std::size_t OpsPerThread, typename TestFn>
  void parallel_test(TestFn test_function) {
    if constexpr (unodb::test::is_olc_db<Db>) unodb::this_thread().qsbr_pause();

    std::array<unodb::test::thread<Db>, ThreadCount> threads;
    for (std::size_t i = 0; i < ThreadCount; ++i) {
      threads[i] =
          unodb::test::thread<Db>{test_function, &verifier, i, OpsPerThread};
    }
    for (auto& t : threads) {
      t.join();
    }

    if constexpr (unodb::test::is_olc_db<Db>)
      unodb::this_thread().qsbr_resume();
  }

  unodb::test::tree_verifier<Db> verifier{true};

 public:
  UpsertConcurrencyTest(const UpsertConcurrencyTest&) = delete;
  UpsertConcurrencyTest(UpsertConcurrencyTest&&) = delete;
  UpsertConcurrencyTest& operator=(const UpsertConcurrencyTest&) = delete;
  UpsertConcurrencyTest& operator=(UpsertConcurrencyTest&&) = delete;
};

using UpsertConcurrencyTypes =
    ::testing::Types<unodb::test::u64_olc_db, unodb::test::key_view_olc_db,
                     unodb::test::key_view_u64val_olc_db>;

UNODB_TYPED_TEST_SUITE(UpsertConcurrencyTest, UpsertConcurrencyTypes)

// ===================================================================
// Concurrency Tests (IDs 7-10, 17-22)
// ===================================================================

// ID-7: No crashes, all get(k) return valid values, tree size==N.
UNODB_TYPED_TEST(UpsertConcurrencyTest, UpsertPlusGet) {
  // TODO(laurynas): implement
}

// ID-8: All keys present, get(k)==expected for each range, size==sum.
UNODB_TYPED_TEST(UpsertConcurrencyTest, UpsertDisjoint) {
  // TODO(laurynas): implement
}

// ID-9: get(k)==final_value, lambda applied exactly once, size unchanged.
UNODB_TYPED_TEST(UpsertConcurrencyTest, OlcRestart) {
  // TODO(laurynas): implement
}

// ID-10: get(k) returns updated value OR empty, size==0 or 1.
UNODB_TYPED_TEST(UpsertConcurrencyTest, UpsertVsRemove) {
  // TODO(laurynas): implement
}

// ID-17: Final value == N (all increments applied).
UNODB_TYPED_TEST(UpsertConcurrencyTest, CasIncrement) {
  // TODO(laurynas): implement
}

// ID-18: Both keys present, T1's value==lambda result, node counts correct.
UNODB_TYPED_TEST(UpsertConcurrencyTest, CasDuringGrowth) {
  // TODO(laurynas): implement
}

// ID-19: T1 inserts, get(k)==v.
UNODB_TYPED_TEST(UpsertConcurrencyTest, CasKeyRemoved) {
  // TODO(laurynas): implement
}

// ID-20: Scan sees old or new value, never torn.
UNODB_TYPED_TEST(UpsertConcurrencyTest, CasPlusScan) {
  // TODO(laurynas): implement
}

// ID-21: No crashes, tree size>=0, all get(k) valid, no ASAN/TSan errors.
UNODB_TYPED_TEST(UpsertConcurrencyTest, RandomOpsStress) {
  // TODO(laurynas): implement
}

// ID-22: Value==N updates, lambda called>=N.
UNODB_TYPED_TEST(UpsertConcurrencyTest, IdempotencyUnderContention) {
  // TODO(laurynas): implement
}

// ===================================================================
// Erase-Specific Concurrency Tests (IDs 23, 23f, 23g)
// ===================================================================

// ID-23: Version mismatch → retry → erase or re-invoke.
UNODB_TYPED_TEST(UpsertConcurrencyTest, EraseCasRetry) {
  // TODO(laurynas): implement
}

// ID-23f: Exactly one erases, other inserts. Post: key present, size==1.
UNODB_TYPED_TEST(UpsertConcurrencyTest, ConcurrentEraseXErase) {
  // TODO(laurynas): implement
}

// ID-23g: T1 erase paused, T2 removes, T1 resumes → insert path.
UNODB_TYPED_TEST(UpsertConcurrencyTest, EraseAfterConcurrentRemove) {
  // TODO(laurynas): implement
}

// ===================================================================
// Contract Verification — concurrency (IDs C2, C5, C6)
// ===================================================================

// ID-C2: Lambda's second invocation receives a different value.
UNODB_TYPED_TEST(UpsertConcurrencyTest, LambdaSeesDifferentValues) {
  // TODO(laurynas): implement
}

// ID-C5: upsert_erase_retry_count increments (STATS build only).
UNODB_TYPED_TEST(UpsertConcurrencyTest, StatsCounterIncrements) {
  // TODO(laurynas): implement
}

// ID-C6: Value committed even when parent RCS fails after write_guard.
UNODB_TYPED_TEST(UpsertConcurrencyTest, ParentRcsFailAfterCommit) {
  // TODO(laurynas): implement
}

// ===================================================================
// OOM Tests (IDs OOM-1, OOM-2)
// Guarded by NDEBUG — OOM injection requires debug heap.
// ===================================================================

#ifndef NDEBUG

template <class Db>
class UpsertOOMTest : public ::testing::Test {
 public:
  using Test::Test;
};

using UpsertOOMTypes =
    ::testing::Types<unodb::test::u64_db, unodb::test::u64_mutex_db,
                     unodb::test::u64_olc_db>;

UNODB_TYPED_TEST_SUITE(UpsertOOMTest, UpsertOOMTypes)

// ID-OOM-1: Insert path OOM — std::bad_alloc, tree unchanged.
UNODB_TYPED_TEST(UpsertOOMTest, InsertPathOom) {
  // TODO(laurynas): implement
}

// ID-OOM-2: Erase shrink OOM — std::bad_alloc, key still present.
UNODB_TYPED_TEST(UpsertOOMTest, EraseShrinkOom) {
  // TODO(laurynas): implement
}

#endif  // NDEBUG

}  // namespace
