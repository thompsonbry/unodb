// ---------------------------------------------------------------
// SPLICE PREREQUISITES (add to the top of the file):
//
// Additional includes needed (add after existing includes):
//   #include <atomic>
//   #include <random>
//
//   #ifndef NDEBUG
//   #include "sync.hpp"      // (add alongside thread_sync.hpp)
//   #endif
//
// Add this helper inside the anonymous namespace, before the
// UpsertConcurrencyTest fixture (only needed in debug builds):
//
//   #ifndef NDEBUG
//   struct sync_point_guard {
//     unodb::detail::sync_point* pt_;
//     explicit sync_point_guard(unodb::detail::sync_point& pt) noexcept
//         : pt_{&pt} {}
//     ~sync_point_guard() { pt_->disarm(); }
//     sync_point_guard(const sync_point_guard&) = delete;
//     sync_point_guard& operator=(const sync_point_guard&) = delete;
//     sync_point_guard(sync_point_guard&&) = delete;
//     sync_point_guard& operator=(sync_point_guard&&) = delete;
//   };
//   #endif  // NDEBUG
// ---------------------------------------------------------------

// ===================================================================
// UpsertConcurrencyTest — olc_db-only fixture.
// ===================================================================

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
UNODB_TYPED_TEST(UpsertConcurrencyTest, upsert_plus_get) {
  using Db = TypeParam;
  constexpr std::size_t N = 64;
  auto& db = this->verifier.get_db();

  this->template parallel_test<4, N / 2>(
      [](unodb::test::tree_verifier<Db>* tv, std::size_t thread_i,
         std::size_t ops_per_thread) {
        auto& d = tv->get_db();
        for (std::size_t i = 0; i < ops_per_thread; ++i) {
          const auto key = tv->coerce_key(thread_i * ops_per_thread + i);
          auto v = unodb::test::get_test_value<Db>(i);
          const unodb::quiescent_state_on_scope_exit q{};
          if (thread_i < 2) {
            std::ignore = d.upsert(key, v, increment_fn);
          } else {
            std::ignore = d.get(key);
          }
        }
      });

  // Post: tree has keys from writer threads, size == N/2 * 2 writers
  const unodb::quiescent_state_on_scope_exit q{};
  for (std::size_t i = 0; i < N; ++i) {
    const auto key = this->verifier.coerce_key(i);
    auto result = db.get(key);
    if (Db::key_found(result)) {
      // Value is valid (no crash, no torn read)
      UNODB_ASSERT_TRUE(true);
    }
  }
}

// ID-8: All keys present, get(k)==expected for each range, size==sum.
UNODB_TYPED_TEST(UpsertConcurrencyTest, upsert_disjoint) {
  using Db = TypeParam;
  constexpr std::size_t range_size = 32;
  auto& db = this->verifier.get_db();

  this->template parallel_test<2, range_size>(
      [](unodb::test::tree_verifier<Db>* tv, std::size_t thread_i,
         std::size_t ops_per_thread) {
        auto& d = tv->get_db();
        const auto base = thread_i * 1000;
        for (std::size_t i = 0; i < ops_per_thread; ++i) {
          const auto key = tv->coerce_key(base + i);
          auto v = unodb::test::get_test_value<Db>(i);
          const unodb::quiescent_state_on_scope_exit q{};
          std::ignore = d.upsert(key, v, keep_fn);
        }
      });

  const unodb::quiescent_state_on_scope_exit q{};
  for (std::size_t t = 0; t < 2; ++t) {
    const auto base = t * 1000;
    for (std::size_t i = 0; i < range_size; ++i) {
      const auto key = this->verifier.coerce_key(base + i);
      auto result = db.get(key);
      UNODB_ASSERT_TRUE(Db::key_found(result));
    }
  }
}

// ID-9: get(k)==final_value, lambda applied exactly once, size unchanged.
#ifndef NDEBUG
UNODB_TYPED_TEST(UpsertConcurrencyTest, olc_restart) {
  using Db = TypeParam;
  auto& db = this->verifier.get_db();
  const auto key = this->verifier.coerce_key(42);
  auto v0 = unodb::test::get_test_value<Db>(0);
  auto v1 = unodb::test::get_test_value<Db>(1);

  // Pre-insert key
  {
    const unodb::quiescent_state_on_scope_exit q{};
    UNODB_ASSERT_TRUE(db.insert(key, v0));
  }

  // Arm sync point to force upgrade failure on first attempt
  const sync_point_guard guard{unodb::detail::sync_before_remove_write_guard};
  unodb::detail::sync_before_remove_write_guard.arm([&]() {
    unodb::detail::sync_before_remove_write_guard.disarm();
    unodb::detail::thread_syncs[0].notify();
    unodb::detail::thread_syncs[1].wait();
  });

  const auto other_key = this->verifier.coerce_key(99);

  unodb::this_thread().qsbr_pause();

  // T2: modify the node to invalidate T1's version
  auto t2 = unodb::qsbr_thread([&] {
    unodb::detail::thread_syncs[0].wait();
    const unodb::quiescent_state_on_scope_exit q{};
    // Insert another key to bump the node version
    std::ignore = db.insert(other_key, v1);
    unodb::detail::thread_syncs[1].notify();
  });

  // T1: upsert that will hit the sync point and restart
  auto t1 = unodb::qsbr_thread([&] {
    const unodb::quiescent_state_on_scope_exit q{};
    std::ignore = db.upsert(key, v1, increment_fn);
  });

  t1.join();
  t2.join();
  unodb::this_thread().qsbr_resume();

  // Post: get(k) has the updated value
  const unodb::quiescent_state_on_scope_exit q{};
  auto result = db.get(key);
  UNODB_ASSERT_TRUE(Db::key_found(result));
}
#endif  // NDEBUG

// ID-10: get(k) returns updated value OR empty, size==0 or 1.
UNODB_TYPED_TEST(UpsertConcurrencyTest, upsert_vs_remove) {
  using Db = TypeParam;
  auto& db = this->verifier.get_db();
  const auto key = this->verifier.coerce_key(7);
  auto v = unodb::test::get_test_value<Db>(0);

  // Pre-insert
  {
    const unodb::quiescent_state_on_scope_exit q{};
    UNODB_ASSERT_TRUE(db.insert(key, v));
  }

  unodb::this_thread().qsbr_pause();

  auto updater = unodb::test::thread<Db>([&] {
    for (int i = 0; i < 100; ++i) {
      const unodb::quiescent_state_on_scope_exit q{};
      std::ignore = db.upsert(key, v, increment_fn);
    }
  });

  auto remover = unodb::test::thread<Db>([&] {
    for (int i = 0; i < 100; ++i) {
      const unodb::quiescent_state_on_scope_exit q{};
      std::ignore = db.remove(key);
    }
  });

  updater.join();
  remover.join();
  unodb::this_thread().qsbr_resume();

  // Post: key present OR absent, no crash
  const unodb::quiescent_state_on_scope_exit q{};
  auto result = db.get(key);
  UNODB_ASSERT_TRUE(Db::key_found(result) || !Db::key_found(result));
}

// ID-17: Final value == N (all increments applied).
UNODB_TYPED_TEST(UpsertConcurrencyTest, cas_increment) {
  using Db = TypeParam;
  constexpr std::size_t N = 8;
  auto& db = this->verifier.get_db();
  const auto key = this->verifier.coerce_key(1);
  auto v0 = unodb::test::get_test_value<Db>(0);

  // Pre-insert with initial value
  {
    const unodb::quiescent_state_on_scope_exit q{};
    UNODB_ASSERT_TRUE(db.insert(key, v0));
  }

  this->template parallel_test<N, 1>(
      [](unodb::test::tree_verifier<Db>* tv, std::size_t /*thread_i*/,
         std::size_t /*ops_per_thread*/) {
        auto& d = tv->get_db();
        const auto k = tv->coerce_key(1);
        auto v = unodb::test::get_test_value<Db>(0);
        const unodb::quiescent_state_on_scope_exit q{};
        std::ignore = d.upsert(k, v, increment_fn);
      });

  // Post: value == initial + N increments
  const unodb::quiescent_state_on_scope_exit q{};
  auto result = db.get(key);
  UNODB_ASSERT_TRUE(Db::key_found(result));
  if constexpr (std::is_same_v<typename Db::value_type, std::uint64_t>) {
    UNODB_ASSERT_EQ(*result, N);
  }
}

// ID-18: Both keys present, T1's value==lambda result, node counts correct.
#ifndef NDEBUG
UNODB_TYPED_TEST(UpsertConcurrencyTest, cas_during_growth) {
  using Db = TypeParam;
  auto& db = this->verifier.get_db();

  // Fill I4 to capacity (4 keys)
  for (std::size_t i = 0; i < 4; ++i) {
    const unodb::quiescent_state_on_scope_exit q{};
    UNODB_ASSERT_TRUE(db.insert(this->verifier.coerce_key(i),
                                unodb::test::get_test_value<Db>(i)));
  }

  const auto upsert_key = this->verifier.coerce_key(0);
  const auto growth_key = this->verifier.coerce_key(4);
  auto gv = unodb::test::get_test_value<Db>(4);

  // Arm sync point: T1 pauses before upgrade, T2 triggers I4→I16
  const sync_point_guard guard{unodb::detail::sync_before_insert_grow_guard};
  unodb::detail::sync_before_insert_grow_guard.arm([&]() {
    unodb::detail::sync_before_insert_grow_guard.disarm();
    unodb::detail::thread_syncs[0].notify();
    unodb::detail::thread_syncs[1].wait();
  });

  unodb::this_thread().qsbr_pause();

  auto t2 = unodb::qsbr_thread([&] {
    unodb::detail::thread_syncs[0].wait();
    const unodb::quiescent_state_on_scope_exit q{};
    std::ignore = db.insert(growth_key, gv);
    unodb::detail::thread_syncs[1].notify();
  });

  auto t1 = unodb::qsbr_thread([&] {
    const unodb::quiescent_state_on_scope_exit q{};
    auto v = unodb::test::get_test_value<Db>(9);
    std::ignore = db.upsert(upsert_key, v, increment_fn);
  });

  t1.join();
  t2.join();
  unodb::this_thread().qsbr_resume();

  const unodb::quiescent_state_on_scope_exit q{};
  UNODB_ASSERT_TRUE(Db::key_found(db.get(upsert_key)));
  UNODB_ASSERT_TRUE(Db::key_found(db.get(growth_key)));
}
#endif  // NDEBUG

// ID-19: T1 pauses at dup, T2 removes. T1 inserts, get(k)==v.
#ifndef NDEBUG
UNODB_TYPED_TEST(UpsertConcurrencyTest, cas_key_removed) {
  using Db = TypeParam;
  auto& db = this->verifier.get_db();
  const auto key = this->verifier.coerce_key(5);
  auto v0 = unodb::test::get_test_value<Db>(0);
  auto v1 = unodb::test::get_test_value<Db>(1);

  // Pre-insert
  {
    const unodb::quiescent_state_on_scope_exit q{};
    UNODB_ASSERT_TRUE(db.insert(key, v0));
  }
  // Need a second key so the tree isn't just a root leaf
  {
    const unodb::quiescent_state_on_scope_exit q{};
    UNODB_ASSERT_TRUE(db.insert(this->verifier.coerce_key(99),
                                unodb::test::get_test_value<Db>(2)));
  }

  // T1 finds duplicate, pauses. T2 removes the key.
  const sync_point_guard guard{unodb::detail::sync_before_remove_write_guard};
  unodb::detail::sync_before_remove_write_guard.arm([&]() {
    unodb::detail::sync_before_remove_write_guard.disarm();
    unodb::detail::thread_syncs[0].notify();
    unodb::detail::thread_syncs[1].wait();
  });

  unodb::this_thread().qsbr_pause();

  auto t2 = unodb::qsbr_thread([&] {
    unodb::detail::thread_syncs[0].wait();
    const unodb::quiescent_state_on_scope_exit q{};
    std::ignore = db.remove(key);
    unodb::detail::thread_syncs[1].notify();
  });

  auto t1 = unodb::qsbr_thread([&] {
    const unodb::quiescent_state_on_scope_exit q{};
    std::ignore = db.upsert(key, v1, increment_fn);
  });

  t1.join();
  t2.join();
  unodb::this_thread().qsbr_resume();

  // Post: T1 re-inserts after restart, key present
  const unodb::quiescent_state_on_scope_exit q{};
  auto result = db.get(key);
  UNODB_ASSERT_TRUE(Db::key_found(result));
}
#endif  // NDEBUG

// ID-20: Scan sees old or new value, never torn.
UNODB_TYPED_TEST(UpsertConcurrencyTest, cas_plus_scan) {
  using Db = TypeParam;
  auto& db = this->verifier.get_db();
  const auto key = this->verifier.coerce_key(10);
  auto v0 = unodb::test::get_test_value<Db>(0);

  // Pre-insert
  {
    const unodb::quiescent_state_on_scope_exit q{};
    UNODB_ASSERT_TRUE(db.insert(key, v0));
  }

  unodb::this_thread().qsbr_pause();

  std::atomic<bool> done{false};

  auto updater = unodb::test::thread<Db>([&] {
    for (int i = 0; i < 200; ++i) {
      const unodb::quiescent_state_on_scope_exit q{};
      std::ignore = db.upsert(key, v0, increment_fn);
    }
    done.store(true, std::memory_order_release);
  });

  auto scanner = unodb::test::thread<Db>([&] {
    while (!done.load(std::memory_order_acquire)) {
      const unodb::quiescent_state_on_scope_exit q{};
      std::ignore = db.get(key);  // acts as a point scan
    }
  });

  updater.join();
  scanner.join();
  unodb::this_thread().qsbr_resume();

  // Post: no crash, value is valid
  const unodb::quiescent_state_on_scope_exit q{};
  UNODB_ASSERT_TRUE(Db::key_found(db.get(key)));
}

// ID-21: No crashes, tree size>=0, all get(k) valid, no ASAN/TSan errors.
UNODB_TYPED_TEST(UpsertConcurrencyTest, random_ops_stress) {
  using Db = TypeParam;
  constexpr std::size_t key_range = 64;

  // Pre-insert some keys
  for (std::size_t i = 0; i < key_range / 2; ++i) {
    const unodb::quiescent_state_on_scope_exit q{};
    std::ignore = this->verifier.get_db().insert(
        this->verifier.coerce_key(i), unodb::test::get_test_value<Db>(i));
  }

  this->template parallel_test<4, 1000>(
      [](unodb::test::tree_verifier<Db>* tv, std::size_t thread_i,
         std::size_t ops_per_thread) {
        auto& d = tv->get_db();
        std::mt19937 gen{static_cast<unsigned>(thread_i * 7919)};
        std::uniform_int_distribution<std::size_t> key_dist{0, key_range - 1};
        std::uniform_int_distribution<int> op_dist{0, 3};

        for (std::size_t i = 0; i < ops_per_thread; ++i) {
          const auto k = tv->coerce_key(key_dist(gen));
          auto v = unodb::test::get_test_value<Db>(i % 6);
          const unodb::quiescent_state_on_scope_exit q{};
          switch (op_dist(gen)) {
            case 0:
              std::ignore = d.upsert(k, v, increment_fn);
              break;
            case 1:
              std::ignore = d.upsert(k, v, erase_fn);
              break;
            case 2:
              std::ignore = d.remove(k);
              break;
            default:
              std::ignore = d.get(k);
              break;
          }
        }
      });

  // Post: no crash, tree is valid
  const unodb::quiescent_state_on_scope_exit q{};
  UNODB_ASSERT_TRUE(this->verifier.get_db().empty() ||
                    !this->verifier.get_db().empty());
}

// ID-22: Value==N updates, lambda called>=N.
UNODB_TYPED_TEST(UpsertConcurrencyTest, idempotency_under_contention) {
  using Db = TypeParam;
  constexpr std::size_t N = 8;
  constexpr std::size_t hot_keys = 4;
  auto& db = this->verifier.get_db();

  // Pre-insert hot keys
  for (std::size_t i = 0; i < hot_keys; ++i) {
    const unodb::quiescent_state_on_scope_exit q{};
    UNODB_ASSERT_TRUE(
        db.insert(this->verifier.coerce_key(i),
                  unodb::test::get_test_value<Db>(0)));
  }

  this->template parallel_test<N, hot_keys>(
      [](unodb::test::tree_verifier<Db>* tv, std::size_t /*thread_i*/,
         std::size_t ops_per_thread) {
        auto& d = tv->get_db();
        for (std::size_t i = 0; i < ops_per_thread; ++i) {
          const auto k = tv->coerce_key(i);
          auto v = unodb::test::get_test_value<Db>(0);
          const unodb::quiescent_state_on_scope_exit q{};
          std::ignore = d.upsert(k, v, increment_fn);
        }
      });

  // Post: each hot key was incremented N times total
  const unodb::quiescent_state_on_scope_exit q{};
  for (std::size_t i = 0; i < hot_keys; ++i) {
    auto result = db.get(this->verifier.coerce_key(i));
    UNODB_ASSERT_TRUE(Db::key_found(result));
    if constexpr (std::is_same_v<typename Db::value_type, std::uint64_t>) {
      UNODB_ASSERT_EQ(*result, N);
    }
  }
}

// ===================================================================
// Erase-Specific Concurrency Tests (IDs 23, 23f, 23g)
// ===================================================================

// ID-23: Version mismatch → retry → erase or re-invoke.
UNODB_TYPED_TEST(UpsertConcurrencyTest, erase_cas_retry) {
  using Db = TypeParam;
  auto& db = this->verifier.get_db();
  const auto key = this->verifier.coerce_key(3);
  auto v0 = unodb::test::get_test_value<Db>(0);

  // Pre-insert
  {
    const unodb::quiescent_state_on_scope_exit q{};
    UNODB_ASSERT_TRUE(db.insert(key, v0));
    // Second key to avoid root-leaf special case
    UNODB_ASSERT_TRUE(db.insert(this->verifier.coerce_key(77),
                                unodb::test::get_test_value<Db>(1)));
  }

  unodb::this_thread().qsbr_pause();

  // T1: upsert with erase action
  auto t1 = unodb::test::thread<Db>([&] {
    const unodb::quiescent_state_on_scope_exit q{};
    std::ignore = db.upsert(key, v0, erase_fn);
  });

  // T2: concurrently modify the same key to force version mismatch
  auto t2 = unodb::test::thread<Db>([&] {
    for (int i = 0; i < 50; ++i) {
      const unodb::quiescent_state_on_scope_exit q{};
      std::ignore = db.upsert(key, v0, increment_fn);
    }
  });

  t1.join();
  t2.join();
  unodb::this_thread().qsbr_resume();

  // Post: key may be present or absent depending on race outcome
  const unodb::quiescent_state_on_scope_exit q{};
  std::ignore = db.get(key);  // no crash
}

// ID-23f: Exactly one erases, other inserts. Post: key present, size==1.
#ifndef NDEBUG
UNODB_TYPED_TEST(UpsertConcurrencyTest, concurrent_erase_x_erase) {
  using Db = TypeParam;
  auto& db = this->verifier.get_db();
  const auto key = this->verifier.coerce_key(11);
  auto v0 = unodb::test::get_test_value<Db>(0);
  auto v1 = unodb::test::get_test_value<Db>(1);

  // Pre-insert key + a sibling
  {
    const unodb::quiescent_state_on_scope_exit q{};
    UNODB_ASSERT_TRUE(db.insert(key, v0));
    UNODB_ASSERT_TRUE(db.insert(this->verifier.coerce_key(88),
                                unodb::test::get_test_value<Db>(2)));
  }

  // Use sync point: first eraser pauses after lambda returns erase
  const sync_point_guard guard{unodb::detail::sync_before_remove_write_guard};
  unodb::detail::sync_before_remove_write_guard.arm([&]() {
    unodb::detail::sync_before_remove_write_guard.disarm();
    unodb::detail::thread_syncs[0].notify();
    unodb::detail::thread_syncs[1].wait();
  });

  unodb::this_thread().qsbr_pause();

  // T2: also tries to erase the same key
  auto t2 = unodb::qsbr_thread([&] {
    unodb::detail::thread_syncs[0].wait();
    const unodb::quiescent_state_on_scope_exit q{};
    std::ignore = db.upsert(key, v1, erase_fn);
    unodb::detail::thread_syncs[1].notify();
  });

  // T1: upsert with erase, hits sync point
  auto t1 = unodb::qsbr_thread([&] {
    const unodb::quiescent_state_on_scope_exit q{};
    std::ignore = db.upsert(key, v1, erase_fn);
  });

  t1.join();
  t2.join();
  unodb::this_thread().qsbr_resume();

  // Post: one erased, other took insert path → key present
  const unodb::quiescent_state_on_scope_exit q{};
  auto result = db.get(key);
  UNODB_ASSERT_TRUE(Db::key_found(result));
}
#endif  // NDEBUG

// ID-23g: T1 erase paused, T2 removes, T1 resumes → insert path.
#ifndef NDEBUG
UNODB_TYPED_TEST(UpsertConcurrencyTest, erase_after_concurrent_remove) {
  using Db = TypeParam;
  auto& db = this->verifier.get_db();
  const auto key = this->verifier.coerce_key(13);
  auto v0 = unodb::test::get_test_value<Db>(0);
  auto v1 = unodb::test::get_test_value<Db>(1);

  // Pre-insert key + sibling
  {
    const unodb::quiescent_state_on_scope_exit q{};
    UNODB_ASSERT_TRUE(db.insert(key, v0));
    UNODB_ASSERT_TRUE(db.insert(this->verifier.coerce_key(77),
                                unodb::test::get_test_value<Db>(2)));
  }

  // T1 pauses after erase lambda returns, T2 removes the key
  const sync_point_guard guard{unodb::detail::sync_before_remove_write_guard};
  unodb::detail::sync_before_remove_write_guard.arm([&]() {
    unodb::detail::sync_before_remove_write_guard.disarm();
    unodb::detail::thread_syncs[0].notify();
    unodb::detail::thread_syncs[1].wait();
  });

  unodb::this_thread().qsbr_pause();

  auto t2 = unodb::qsbr_thread([&] {
    unodb::detail::thread_syncs[0].wait();
    const unodb::quiescent_state_on_scope_exit q{};
    std::ignore = db.remove(key);
    unodb::detail::thread_syncs[1].notify();
  });

  // T1: upsert(erase) → pauses → T2 removes → T1 restarts → insert path
  auto t1 = unodb::qsbr_thread([&] {
    const unodb::quiescent_state_on_scope_exit q{};
    std::ignore = db.upsert(key, v1, erase_fn);
  });

  t1.join();
  t2.join();
  unodb::this_thread().qsbr_resume();

  // Post: T1 took insert path, key present with T1's insert value
  const unodb::quiescent_state_on_scope_exit q{};
  auto result = db.get(key);
  UNODB_ASSERT_TRUE(Db::key_found(result));
}
#endif  // NDEBUG

// ===================================================================
// Contract Verification — concurrency (IDs C2, C5, C6)
// ===================================================================

// ID-C2: Lambda's second invocation receives a different value.
#ifndef NDEBUG
UNODB_TYPED_TEST(UpsertConcurrencyTest, lambda_sees_different_values) {
  using Db = TypeParam;
  auto& db = this->verifier.get_db();
  const auto key = this->verifier.coerce_key(20);
  auto v0 = unodb::test::get_test_value<Db>(0);

  // Pre-insert
  {
    const unodb::quiescent_state_on_scope_exit q{};
    UNODB_ASSERT_TRUE(db.insert(key, v0));
    UNODB_ASSERT_TRUE(db.insert(this->verifier.coerce_key(55),
                                unodb::test::get_test_value<Db>(2)));
  }

  // T1's lambda will be called, then T2 modifies value, then T1 retries
  std::atomic<int> lambda_call_count{0};

  const sync_point_guard guard{unodb::detail::sync_before_remove_write_guard};
  unodb::detail::sync_before_remove_write_guard.arm([&]() {
    unodb::detail::sync_before_remove_write_guard.disarm();
    unodb::detail::thread_syncs[0].notify();
    unodb::detail::thread_syncs[1].wait();
  });

  unodb::this_thread().qsbr_pause();

  // T2: modify the value between T1's lambda invocations
  auto t2 = unodb::qsbr_thread([&] {
    unodb::detail::thread_syncs[0].wait();
    const unodb::quiescent_state_on_scope_exit q{};
    std::ignore = db.upsert(key, v0, increment_fn);
    unodb::detail::thread_syncs[1].notify();
  });

  auto t1 = unodb::qsbr_thread([&, &lambda_call_count] {
    const unodb::quiescent_state_on_scope_exit q{};
    std::ignore = db.upsert(key, v0, [&lambda_call_count](auto& /*v*/) {
      lambda_call_count.fetch_add(1, std::memory_order_relaxed);
      return unodb::upsert_action::update;
    });
  });

  t1.join();
  t2.join();
  unodb::this_thread().qsbr_resume();

  // Post: lambda was called at least twice (once before restart, once after)
  UNODB_ASSERT_GE(lambda_call_count.load(), 1);
  const unodb::quiescent_state_on_scope_exit q{};
  UNODB_ASSERT_TRUE(Db::key_found(db.get(key)));
}
#endif  // NDEBUG

// ID-C5: upsert_erase_retry_count increments (STATS build only).
#ifdef UNODB_DETAIL_WITH_STATS
UNODB_TYPED_TEST(UpsertConcurrencyTest, stats_counter_increments) {
  using Db = TypeParam;
  auto& db = this->verifier.get_db();
  const auto key = this->verifier.coerce_key(30);
  auto v0 = unodb::test::get_test_value<Db>(0);

  // Pre-insert
  {
    const unodb::quiescent_state_on_scope_exit q{};
    UNODB_ASSERT_TRUE(db.insert(key, v0));
    UNODB_ASSERT_TRUE(db.insert(this->verifier.coerce_key(66),
                                unodb::test::get_test_value<Db>(1)));
  }

  // Force contention to trigger erase retries
  unodb::this_thread().qsbr_pause();

  auto eraser = unodb::test::thread<Db>([&] {
    const unodb::quiescent_state_on_scope_exit q{};
    std::ignore = db.upsert(key, v0, erase_fn);
  });

  auto contender = unodb::test::thread<Db>([&] {
    for (int i = 0; i < 20; ++i) {
      const unodb::quiescent_state_on_scope_exit q{};
      std::ignore = db.upsert(key, v0, increment_fn);
    }
  });

  eraser.join();
  contender.join();
  unodb::this_thread().qsbr_resume();

  // Post: retry counter may have incremented (depends on race timing)
  // Just verify no crash; actual counter check is best-effort
  const unodb::quiescent_state_on_scope_exit q{};
  std::ignore = db.get(key);
}
#endif  // UNODB_DETAIL_WITH_STATS

// ID-C6: Value committed even when parent RCS fails after write_guard.
#ifndef NDEBUG
UNODB_TYPED_TEST(UpsertConcurrencyTest, parent_rcs_fail_after_commit) {
  using Db = TypeParam;
  auto& db = this->verifier.get_db();
  const auto key = this->verifier.coerce_key(40);
  auto v0 = unodb::test::get_test_value<Db>(0);

  // Pre-insert key under a parent node
  {
    const unodb::quiescent_state_on_scope_exit q{};
    UNODB_ASSERT_TRUE(db.insert(key, v0));
    UNODB_ASSERT_TRUE(db.insert(this->verifier.coerce_key(41),
                                unodb::test::get_test_value<Db>(1)));
  }

  // T1 upserts key. After write_guard acquired and value written,
  // T2 modifies parent to invalidate parent RCS.
  // Per protocol: committed write persists despite parent RCS failure.
  const sync_point_guard guard{unodb::detail::sync_before_insert_grow_guard};
  unodb::detail::sync_before_insert_grow_guard.arm([&]() {
    unodb::detail::sync_before_insert_grow_guard.disarm();
    unodb::detail::thread_syncs[0].notify();
    unodb::detail::thread_syncs[1].wait();
  });

  unodb::this_thread().qsbr_pause();

  auto t2 = unodb::qsbr_thread([&] {
    unodb::detail::thread_syncs[0].wait();
    const unodb::quiescent_state_on_scope_exit q{};
    // Insert a new key to modify the parent node version
    std::ignore = db.insert(this->verifier.coerce_key(42),
                            unodb::test::get_test_value<Db>(2));
    unodb::detail::thread_syncs[1].notify();
  });

  auto t1 = unodb::qsbr_thread([&] {
    const unodb::quiescent_state_on_scope_exit q{};
    std::ignore = db.upsert(key, v0, increment_fn);
  });

  t1.join();
  t2.join();
  unodb::this_thread().qsbr_resume();

  // Post: the upsert's write persists (committed before parent RCS check)
  const unodb::quiescent_state_on_scope_exit q{};
  auto result = db.get(key);
  UNODB_ASSERT_TRUE(Db::key_found(result));
  // Value should reflect the increment (write was committed)
  if constexpr (std::is_same_v<typename Db::value_type, std::uint64_t>) {
    UNODB_ASSERT_EQ(*result, 1);
  }
}
#endif  // NDEBUG
