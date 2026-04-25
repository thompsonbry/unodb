# Bulk Index Build for unodb ART Trees

**Issue:** [#636](https://github.com/unodb-dev/unodb/issues/636)
**Date:** 2026-04-25
**Status:** Design

---

## 1. Background and Literature

### 1.1 The Canonical Strategy: Sort-Then-Insert

The well-known strategy for bulk loading trie-based indexes is:

1. **Sort the keys** into lexicographic order.
2. **Insert in sorted order** into the tree.

This is optimal for ART (and tries in general) because:

- **Maximal prefix sharing.** Each successive key shares the longest common
  prefix with the immediately preceding key. The insert cursor stays in the
  same subtree, touching only the rightmost frontier of the tree.
- **Minimal node splits.** New keys extend the rightmost child of each inode
  rather than splitting interior prefixes. In the worst case (random order),
  every insert can trigger a prefix mismatch at an arbitrary depth; sorted
  order confines structural changes to the rightmost path.
- **Cache locality.** The working set is the rightmost path from root to leaf
  — O(key_length) nodes — rather than random nodes scattered across the tree.
- **Predictable growth.** Inodes grow monotonically (4→16→48→256) at each
  level as children accumulate, never shrinking and re-growing.

**References:**

- Leis et al., *The Adaptive Radix Tree: ARTful Indexing for Main-Memory
  Databases* (ICDE 2013) — §III-D discusses path compression and lazy
  expansion, both of which benefit from sorted insertion.
- Kipf et al., *SOSD: A Benchmark for Sorted Order-Based Data Structures*
  (2020) — benchmarks bulk-loaded indexes including ART.
- DuckDB ART implementation — uses sorted bulk load for index construction
  during CREATE INDEX.
- HyPer/Umbra — the original ART deployment; bulk loads via sorted scan of
  the base table.
- LMDB — sorted cursor-based insertion for B-tree bulk load; analogous
  principle (append-only to rightmost page).

### 1.2 Beyond Sort-Then-Insert: Bottom-Up Construction

A more aggressive optimization is **bottom-up construction**: instead of
calling `insert()` N times (each of which traverses root-to-leaf), build the
tree in a single pass from the sorted key array:

1. Group keys by their first distinguishing byte at each level.
2. Allocate the correct inode type directly (skip 4→16→48→256 growth).
3. Wire children in a single pass.

This eliminates:
- All root-to-leaf traversals (O(N × key_length) → O(N)).
- All inode growth overhead (no temporary inode4 that immediately grows to
  inode16).
- All prefix comparison work (prefixes are computed once from the sorted
  array, not re-derived on each insert).

### 1.3 Parallel Bulk Load

The ART structure naturally partitions by the first byte of the key:

- Partition the sorted key array into up to 256 buckets by first byte.
- Build each subtree independently (no shared state).
- Assemble the root inode256 (or smaller) from the subtree roots.

This is embarrassingly parallel with zero synchronization during the build
phase.

---

## 2. unodb Architecture Relevant to Bulk Load

### 2.1 Node Types and Growth

From `art_internal_impl.hpp`:

| Type      | Max Children | Growth Trigger |
|-----------|-------------|----------------|
| `inode4`  | 4           | Created on first split |
| `inode16` | 16          | inode4 full (5th child) |
| `inode48` | 48          | inode16 full (17th child) |
| `inode256`| 256         | inode48 full (49th child) |

Each growth step allocates a new, larger inode, copies children, and frees
the old one. For bulk load of N keys, this means O(N) temporary allocations
that are immediately freed — pure waste.

Key prefix capacity is 7 bytes (`key_prefix_capacity = 7`). The
`build_chain` function creates single-child inode4 chains for key_view keys
that exceed the prefix capacity.

### 2.2 Value-In-Slot (VIS) Optimization

When `can_eliminate_leaf` is true (small fixed-size values), values are packed
directly into inode child pointer slots, eliminating leaf node allocations
entirely. The bulk loader must handle both VIS and non-VIS paths.

### 2.3 The Three db Types

| Type       | Synchronization | Bulk Load Applicability |
|------------|----------------|------------------------|
| `db`       | None           | Primary target — single-threaded build |
| `mutex_db` | Mutex wrapper around `db` | Delegates to `db::bulk_insert` |
| `olc_db`   | Optimistic lock coupling + QSBR | Phase 2 — needs special handling |

### 2.4 Allocator Interface

From `art_allocator.hpp`, trees accept a pluggable `allocator_type` with
`alloc`, `dealloc`, and `defer_dealloc` callbacks. The bulk loader must use
the tree's allocator for all node allocations.

### 2.5 Stats Tracking

Under `UNODB_DETAIL_WITH_STATS`, the tree tracks:
- `node_counts[type]` — current count per node type
- `current_memory_use` — total bytes allocated
- `growing_inode_counts[type]` — cumulative growth events
- `key_prefix_splits` — prefix mismatch splits

The bulk loader must maintain these counters accurately.

### 2.6 Insert Path Summary

`insert_internal()` dispatches to:
- `insert_internal_fixed()` for fixed-width keys (uint64_t etc.)
- `insert_internal_key_view()` for variable-length keys (key_view)

Both follow the same pattern: traverse from root, compare prefixes, find or
create child slots, grow inodes as needed. The bulk loader replaces this
entire traversal with direct construction.

---

## 3. Proposed Design

### 3.1 API

```cpp
/// Bulk-insert a range of key-value pairs.
///
/// Precondition: the tree MUST be empty.
/// Precondition: [first, last) MUST be sorted by key in ascending order
///               with no duplicate keys.
///
/// These preconditions are asserted in debug builds but not checked in
/// release builds (the caller is responsible).
///
/// Complexity: O(N × max_key_length) time, O(max_key_length) stack space.
///
/// \return the number of keys inserted (== distance(first, last)).
template <typename InputIt>
std::size_t bulk_load(InputIt first, InputIt last);

/// Convenience overload for contiguous ranges.
std::size_t bulk_load(std::span<const std::pair<Key, value_type>> entries);
```

**Design decisions:**

- **Empty-tree precondition.** Merging into an existing tree is substantially
  more complex (Phase 2). The primary use case — initial index construction —
  always starts from an empty tree.
- **Sorted-order precondition.** Sorting is the caller's responsibility. This
  keeps the bulk loader focused and avoids a redundant copy if the data is
  already sorted (e.g., scan from a sorted source).
- **No-duplicate precondition.** Simplifies the build logic. The caller can
  deduplicate during sorting.

### 3.2 Phase 1: Sorted Sequential Insert (Minimal Useful Implementation)

The simplest bulk loader that delivers measurable speedup:

```
bulk_load(first, last):
    assert(empty())
    assert(is_sorted(first, last))
    for each (key, value) in [first, last):
        insert(key, value)    // uses existing insert_internal
    return count
```

**Why this is already faster than random insert:**

1. Sorted insertion means the insert path always descends the rightmost
   frontier — hot in L1/L2 cache.
2. No prefix mismatches at interior nodes (each new key extends the
   rightmost child).
3. Inodes grow monotonically — no pathological split-then-grow patterns.

**Expected speedup:** 2–5× over random-order insert for large key sets,
based on published ART benchmarks (Leis et al. §V, DuckDB benchmarks).

**Implementation cost:** ~20 lines of code. Can ship immediately.

### 3.3 Phase 2: Bottom-Up Construction

Replace the loop-of-inserts with a recursive builder that constructs the
tree in a single pass:

```
build_subtree(keys[], depth):
    if len(keys) == 0: return null
    if len(keys) == 1: return make_leaf(keys[0])

    // All keys share a common prefix at this depth.
    // Find the length of the shared prefix.
    prefix = common_prefix(keys, depth)

    // Group keys by the byte at (depth + prefix_length).
    // This is the dispatch byte for the inode at this level.
    groups = group_by_byte(keys, depth + prefix_length)

    // Choose the right inode type based on group count.
    n = len(groups)
    inode = allocate_inode(n)   // directly: I4/I16/I48/I256
    inode.set_prefix(prefix)

    for (byte, subkeys) in groups:
        child = build_subtree(subkeys, depth + prefix_length + 1)
        inode.add_child(byte, child)   // direct slot write, no growth

    return inode
```

**Key optimizations over repeated insert:**

| Aspect | Repeated Insert | Bottom-Up Build |
|--------|----------------|-----------------|
| Traversals | N × O(key_len) | Single pass O(N × key_len) |
| Inode allocations | O(N) temporary + O(N) final | O(N) final only |
| Prefix comparisons | O(N × key_len) | O(N) total (computed from sorted array) |
| Cache behavior | Good (sorted) | Excellent (sequential scan) |

**Pre-sizing inodes:**

The group count at each level is known before allocation:
- 1–4 children → `inode4`
- 5–16 children → `inode16`
- 17–48 children → `inode48`
- 49–256 children → `inode256`

This eliminates all growth events. The `growing_inode_counts` stats will
reflect only the final allocation (one growth event per inode, at its final
size).

**Handling key_view (variable-length keys):**

For key_view keys, the builder must create chain inode4 nodes when the
common prefix exceeds `key_prefix_capacity` (7 bytes). The existing
`build_chain` logic can be adapted, but the bottom-up builder naturally
handles this: when the common prefix is longer than 7 bytes, the builder
creates intermediate single-child inode4 nodes at each 8-byte boundary
(7 prefix bytes + 1 dispatch byte).

**Handling VIS (value-in-slot):**

When `can_eliminate_leaf` is true, leaf values are packed into inode child
slots. The bottom-up builder packs values directly during `add_child`
instead of creating leaf nodes.

### 3.4 Phase 3: Parallel Bulk Load

```
parallel_bulk_load(keys[]):
    sort(keys)  // or assume pre-sorted

    // Partition by first byte (depth 0).
    buckets[256] = partition_by_first_byte(keys)

    // Build subtrees in parallel.
    subtrees[256] = parallel_for(buckets, [](bucket) {
        return build_subtree(bucket, depth=1)
    })

    // Assemble root.
    root = allocate_inode(count_non_null(subtrees))
    for byte in 0..255:
        if subtrees[byte] != null:
            root.add_child(byte, subtrees[byte])
```

**Parallelism model:**

- Each of the up to 256 subtrees is built independently with zero shared
  state.
- The only synchronization point is assembling the root inode after all
  subtrees complete.
- For `olc_db`, the parallel build phase uses thread-local allocators (no
  QSBR needed during construction since no concurrent readers exist yet).
  After assembly, the tree is published atomically by setting the root
  pointer.

**Thread count:**

- Use `std::thread::hardware_concurrency()` or a caller-supplied thread
  count.
- Partition the 256 buckets across threads (work-stealing or static
  assignment weighted by bucket size).

### 3.5 Integration with Existing Code

#### Allocator

All node allocations go through `this->allocator_`. The bottom-up builder
calls the same `allocate_aligned` path as `inode_4::create` etc. No
allocator changes needed.

For Phase 3 parallel build, each thread uses the tree's allocator. Since
`db` is single-threaded, the parallel build must use a thread-safe allocator
or build with per-thread arenas that are merged. For `olc_db`, the existing
QSBR allocator is already thread-safe.

#### Stats Tracking

The bottom-up builder must update stats atomically (for `olc_db`) or
directly (for `db`):

```cpp
// After allocating an inode of type T:
UNODB_DETAIL_WITH_STATS {
    ++node_counts[as_i<T>];
    current_memory_use += sizeof(T);
    ++growing_inode_counts[internal_as_i<T>];
}
```

For Phase 3, accumulate per-thread stats and merge after join.

#### OLC Lock Protocol

For `olc_db` bulk load:
- **Phase 1 (sorted insert):** Each insert acquires write locks as usual.
  No change needed.
- **Phase 2/3 (bottom-up):** The tree is built without locks (no concurrent
  readers during construction). The root is published with a single atomic
  store. This is safe because `olc_db::bulk_load` requires an empty tree
  and exclusive access during the build.

#### Exception Safety

The bottom-up builder must handle allocation failures:
- On `std::bad_alloc`, free all nodes allocated so far.
- Use RAII guards (similar to `subtree_guard` in `art_internal_impl.hpp`)
  to ensure cleanup.
- The recursive builder naturally unwinds: each level's `unique_ptr` or
  guard releases its subtree on exception.

---

## 4. Benchmark Impact

Issue #636 states: *"would make the larger scale benchmarks much faster."*

The existing benchmarks in `benchmark/micro_benchmark.cpp` and
`benchmark/micro_benchmark_node_utils.hpp` use `insert_key_range` to
populate trees. These currently insert keys one at a time.

### Expected Improvements

| Scenario | Current | Phase 1 | Phase 2 | Phase 3 |
|----------|---------|---------|---------|---------|
| 1M uint64 keys, random order | baseline | 2–3× faster (sorted) | 5–10× faster | 10–20× faster |
| 1M uint64 keys, already sorted | ~same as random* | ~same | 5–10× faster | 10–20× faster |
| 10M key_view keys | baseline | 2–5× faster | 5–15× faster | 15–30× faster |

*\* Random vs sorted single-insert is similar because the insert path
always traverses root-to-leaf; the cache benefit of sorted order is modest
for small trees but significant for large ones.*

### New Benchmarks

```cpp
// In micro_benchmark.cpp:
static void BM_BulkLoad_Sequential(benchmark::State& state) {
    // Pre-generate sorted keys
    for (auto _ : state) {
        db<uint64_t, value_type> tree;
        tree.bulk_load(sorted_keys.begin(), sorted_keys.end());
    }
}

static void BM_BulkLoad_BottomUp(benchmark::State& state) { ... }
static void BM_BulkLoad_Parallel(benchmark::State& state) { ... }
```

---

## 5. Implementation Plan

### Phase 1: Sorted Sequential Insert (Target: immediate)

**Scope:** Add `bulk_load()` method to `db`, `mutex_db`, and `olc_db` that
iterates the sorted input and calls `insert()`.

**Files modified:**
- `art.hpp` — add `bulk_load` template method to `db`
- `mutex_art.hpp` — add `bulk_load` to `mutex_db` (delegates to `db`)
- `olc_art.hpp` — add `bulk_load` to `olc_db`
- `test/test_art.cpp` — add bulk_load correctness tests
- `benchmark/micro_benchmark.cpp` — add bulk_load benchmark

**Validation:**
- Assert empty tree precondition.
- Assert sorted order in debug builds (check `keys[i] < keys[i+1]`).
- Verify tree correctness via scan after bulk load.
- Verify stats consistency.

### Phase 2: Bottom-Up Construction

**Scope:** Replace the insert loop with a recursive bottom-up builder.

**Files modified:**
- `art.hpp` — add private `build_subtree` recursive method
- `art_internal_impl.hpp` — add `create_with_children` factory methods to
  inode types (direct construction without growth)
- `test/test_art.cpp` — extend bulk_load tests for edge cases

**New inode factory methods:**

```cpp
// In basic_inode_4:
static auto create_with_children(
    db_type& db, key_prefix_snapshot prefix,
    std::span<std::pair<std::byte, node_ptr>> children);

// Similar for inode_16, inode_48, inode_256
```

These bypass the growth path entirely, initializing the inode with all
children at once.

### Phase 3: Parallel Bulk Load

**Scope:** Partition by first byte, build subtrees in parallel.

**Files modified:**
- `art.hpp` — add `parallel_bulk_load` method
- `olc_art.hpp` — add `parallel_bulk_load` with QSBR-aware assembly

**Dependencies:**
- Phase 2 (bottom-up builder)
- Thread pool or `std::jthread` for parallel execution

---

## 6. Open Questions

1. **Should `bulk_load` sort the input?** Current design requires pre-sorted
   input. Alternative: accept unsorted input and sort internally. Pro:
   simpler caller API. Con: forces a copy; caller may already have sorted
   data.

2. **Should `bulk_load` work on non-empty trees?** Current design requires
   empty tree. Merging sorted input into an existing tree is possible but
   complex (requires a merge-join of the existing tree's iterator with the
   input iterator). Defer to Phase 4.

3. **Thread pool vs std::jthread for Phase 3?** Using raw threads is
   simplest but wasteful for small inputs. A thread pool avoids thread
   creation overhead but adds a dependency. Consider making the parallel
   executor pluggable.

4. **Should Phase 2 use iterative or recursive construction?** Recursive is
   cleaner but risks stack overflow for very deep trees (pathological key
   distributions). Iterative with an explicit stack is safer. Key depth is
   bounded by max key length, so recursion depth ≤ max_key_length /
   (key_prefix_capacity + 1) ≈ max_key_length / 8. For 256-byte keys,
   that's ~32 levels — safe.

5. **How to handle `olc_db` bulk load with concurrent readers?** Phase 1
   (sorted insert) works with the existing OLC protocol. Phase 2/3 require
   exclusive access. Options: (a) require exclusive access (simplest), (b)
   build the tree offline and swap the root atomically (requires careful
   QSBR epoch management for the old tree).

---

## 7. Summary

| Phase | Strategy | Speedup | Complexity | Risk |
|-------|----------|---------|------------|------|
| 1 | Sorted sequential insert | 2–5× | Low (~20 LOC) | None |
| 2 | Bottom-up construction | 5–15× | Medium (~200 LOC) | Moderate (new inode factories) |
| 3 | Parallel bottom-up | 10–30× | High (~400 LOC) | Higher (threading, olc_db integration) |

**Recommendation:** Ship Phase 1 immediately to unblock benchmarks. Design
and implement Phase 2 as the next step. Phase 3 is the target for #636 but
depends on Phase 2.
