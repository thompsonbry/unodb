# CAS / Upsert API Design — `insert_or_resolve` (Issue #847)

## 1. Prior Art: libcuckoo

### API Surface

libcuckoo's `cuckoohash_map` provides four lambda-based operations:

```cpp
bool find_fn(key, fn)       // fn(const V&)           — read under lock
bool update_fn(key, fn)     // fn(V&)                 — mutate under lock
bool erase_fn(key, fn)      // fn(V&) → bool          — erase if fn returns true
bool uprase_fn(key, fn, val...)  // insert-or-resolve  — fn can mutate or erase
```

### `uprase_fn` Protocol

```cpp
template <class K, class F, class... Args>
bool uprase_fn(K&& key, F fn, Args&&... val);
```

1. Hash the key, acquire **two bucket locks** (cuckoo hashing uses two candidate buckets).
2. Call `cuckoo_insert_loop` which either finds a duplicate or an empty slot.
3. If **empty slot found** (`status == ok`): construct the value in-place, set `UpsertContext::NEWLY_INSERTED`.
4. If **duplicate found** (`status == failure_key_duplicated`): set `UpsertContext::ALREADY_EXISTED`.
5. Invoke `fn(mapped_type&, UpsertContext)` (or `fn(mapped_type&)` for the 1-arg overload).
6. If `fn` returns `true` → erase the entry (`del_from_bucket`).
7. Return `true` if newly inserted, `false` if already existed.

### Thread Safety Guarantees

- The lambda executes **under the bucket lock** — both candidate bucket locks are held for the entire duration.
- No concurrent reader or writer can access the same key while the lambda runs.
- The lock scope covers: find → optional insert → lambda → optional erase → unlock.
- This makes the inspect-and-decide **atomic** with respect to concurrent mutations.

### Error Handling

- If the table is full during insert, `cuckoo_fast_double` expands the table and retries (locks are re-acquired).
- No partial-failure states: either the operation completes fully or retries.

### Key Design Insight

The `UpsertContext` enum (`NEWLY_INSERTED` / `ALREADY_EXISTED`) tells the lambda whether it's looking at a freshly-constructed value or a pre-existing one. The lambda's `bool` return controls erasure. This is more general than our proposed `upsert_action` enum but serves the same purpose.

## 2. Issue #847 Spec Summary

The issue proposes:

- `enum class upsert_action { keep, update, erase }`
- `insert_or_resolve(Key k, value_type v, FN fn)` where `FN = upsert_action(value_type& existing)`
- Lambda is invoked **only when key already exists** (not on fresh insert)
- For `update`: lambda mutates the value in-place, then the implementation writes it back
- For `erase`: remove the entry
- For `keep`: no-op, release locks
- Companion `erase_fn(Key k, FN fn)` where `FN = bool(const value_type&)`
- A `set_value<Value>` on the leaf, symmetric with existing `get_value<Value>`

## 3. Current Insert Implementation Analysis

### 3.1 `db` (non-concurrent, `art.hpp`)

`insert_internal` → `insert_internal_key_view` / `insert_internal_fixed`:

- Descends the tree following key bytes.
- At a **leaf node** (keyed-leaf path): compares `k.cmp(existing_key)`. If `== 0`, returns `false` (duplicate).
- At a **VIS slot** (`can_eliminate_leaf`): after `add_or_choose_subtree`, checks `is_value_in_slot(ci)`. If true, returns `false` (duplicate).
- No locks involved — single-threaded.

### 3.2 `mutex_db` (`mutex_art.hpp`)

Wraps `db` with a global `std::mutex`. `insert_internal` is called under `std::lock_guard{mutex}`. The entire operation is serialized.

### 3.3 `olc_db` (`olc_art.hpp`)

`insert_internal` → `try_insert` (retry loop):

**Duplicate detection site 1 — Keyed-leaf path** (~line in `try_insert`):
```cpp
if (UNODB_DETAIL_UNLIKELY(k.cmp(existing_key) == 0)) {
    // holds: parent_critical_section (read), node_critical_section (read)
    // node is the leaf
    // parent is the inode containing the leaf pointer
    return false;  // duplicate
}
```

**Duplicate detection site 2 — VIS path** (after `add_or_choose_subtree`):
```cpp
if (inode->is_value_in_slot(node_type, ci_chk)) {
    // holds: parent_critical_section (read), node_critical_section (read)
    // node_critical_section guards the inode containing the packed value
    return false;  // duplicate
}
```

At both sites, we hold **two OLC read locks** (parent and node) via `read_critical_section`. The value is accessible but read-only.

### 3.4 Key Types: `get_value<Value>` and the missing `set_value<Value>`

In `art_internal_impl.hpp`, `basic_leaf::get_value<Value>()`:
```cpp
template <typename Value>
constexpr auto get_value() const noexcept {
    static_assert(std::is_trivially_copyable_v<Value>);
    Value v{};
    std::memcpy(&v, data + key_size, sizeof(v));
    return v;
}
```

The symmetric `set_value<Value>` is straightforward:
```cpp
template <typename Value>
constexpr void set_value(const Value& v) noexcept {
    static_assert(std::is_trivially_copyable_v<Value>);
    std::memcpy(data + key_size, &v, sizeof(v));
}
```

For the keyless leaf (`basic_leaf<no_key_tag, Header>`), the offset is `data + 0` instead of `data + key_size`.

### 3.5 `art_policy` — VIS pack/unpack

`pack_value(v)` XORs the value bits with a sentinel and stores in a `node_ptr`. `unpack_value(n)` reverses the XOR. Both are in `basic_art_policy` in `art_internal_impl.hpp`.

## 4. Proposed Design

### 4.1 Public API

```cpp
/// Action the lambda returns to indicate what to do with an existing entry.
enum class upsert_action { keep, update, erase };

/// Insert value if key absent. If key exists, invoke fn to resolve.
/// fn receives a mutable reference to the existing value and returns
/// an action: keep (no change), update (value was modified in-place
/// by fn), or erase (remove the entry).
///
/// Returns true if a new key was inserted, false if key already existed.
template <typename FN>
[[nodiscard]] bool insert_or_resolve(Key k, value_type v, FN fn);
// where FN = upsert_action(value_type& existing)

/// If key exists, invoke fn. If fn returns true, erase the entry.
/// Returns true if key was found (regardless of erase decision).
template <typename FN>
[[nodiscard]] bool erase_fn(Key k, FN fn);
// where FN = bool(const value_type&)
```

### 4.2 `set_value<Value>` on Leaf

Add to `basic_leaf<Key, Header>`:

```cpp
template <typename Value>
constexpr void set_value(const Value& v) noexcept {
    static_assert(std::is_trivially_copyable_v<Value>);
    std::memcpy(data + key_size, &v, sizeof(v));
}
```

Add to `basic_leaf<no_key_tag, Header>`:

```cpp
template <typename Value>
constexpr void set_value(const Value& v) noexcept {
    static_assert(std::is_trivially_copyable_v<Value>);
    std::memcpy(data, &v, sizeof(v));
}
```

For `value_view` values, `set_value` requires the new value to have the same size as the existing one (the leaf is immutable-size). This is fine for fixed-width `Value` types. For `value_view`, `update` would need to allocate a new leaf — defer this to a later phase.

### 4.3 Implementation: `db` (non-concurrent)

Straightforward. At each duplicate-detection site, instead of `return false`, invoke the lambda and act on the result.

**Keyed-leaf path** (in `insert_internal_fixed` and `insert_internal_key_view`):

```cpp
if (UNODB_DETAIL_UNLIKELY(k.cmp(existing_key) == 0)) {
    auto existing_value = leaf->template get_value<value_type>();
    const auto action = fn(existing_value);
    if (action == upsert_action::update) {
        leaf->template set_value<value_type>(existing_value);
    } else if (action == upsert_action::erase) {
        // Invoke existing remove logic.
        // For Phase 1: call remove_internal(k) after returning.
        // Or inline the removal here.
    }
    // keep: no-op
    return false;
}
```

**VIS path** (after `add_or_choose_subtree`):

```cpp
if (inode->is_value_in_slot(node_type, ci)) {
    auto existing_value = art_policy::unpack_value(child_in_parent->load());
    const auto action = fn(existing_value);
    if (action == upsert_action::update) {
        *child_in_parent = art_policy::pack_value(existing_value);
    } else if (action == upsert_action::erase) {
        // Invoke existing remove logic for this slot.
    }
    return false;
}
```

For `db`, there are no concurrency concerns. The `erase` action can directly call the existing removal machinery.

### 4.4 Implementation: `mutex_db`

Identical to `db` — the global mutex is already held. Delegate to `db_::insert_or_resolve_internal(k, v, fn)`.

```cpp
template <typename FN>
[[nodiscard]] bool insert_or_resolve(Key insert_key, value_type v, FN fn) {
    const std::lock_guard guard{mutex};
    const art_key_type k{insert_key};
    return db_.insert_or_resolve_internal(k, v, fn);
}
```

### 4.5 Implementation: `olc_db` — The Hard Case

#### 4.5.1 `keep` Action

Trivial. Release read locks and return `false`. This is what the current code already does.

#### 4.5.2 `update` Action — Keyed-Leaf Path

At the duplicate-detection site, we hold:
- `parent_critical_section` — read lock on the **parent inode** (which contains the child pointer to the leaf)
- `node_critical_section` — read lock on the **leaf itself**

Leaves in OLC don't have their own locks in the traditional sense — the leaf's `olc_node_header::m_lock` is used. To modify the leaf's value:

1. Copy the existing value to a local: `auto val = leaf->get_value<Value>();`
2. Invoke the lambda: `auto action = fn(val);`
3. If `action == update`:
   a. Upgrade `node_critical_section` (leaf's lock) to `write_guard`.
   b. If upgrade fails → return `{}` (restart).
   c. Release parent read lock.
   d. Write back: `leaf->set_value<Value>(val);`
   e. Write guard destructor releases the lock.

```cpp
if (UNODB_DETAIL_UNLIKELY(k.cmp(existing_key) == 0)) {
    auto existing_value = leaf->template get_value<Value>();
    if (UNODB_DETAIL_UNLIKELY(!parent_critical_section.check())) return {};
    if (UNODB_DETAIL_UNLIKELY(!node_critical_section.check())) return {};

    const auto action = fn(existing_value);

    if (action == upsert_action::keep) {
        if (UNODB_DETAIL_UNLIKELY(!parent_critical_section.try_read_unlock()))
            return {};
        if (UNODB_DETAIL_UNLIKELY(!node_critical_section.try_read_unlock()))
            return {};
        return false;
    }

    if (action == upsert_action::update) {
        // Upgrade leaf lock to write.
        optimistic_lock::write_guard leaf_guard{
            std::move(node_critical_section)};
        if (UNODB_DETAIL_UNLIKELY(leaf_guard.must_restart())) return {};
        if (UNODB_DETAIL_UNLIKELY(!parent_critical_section.try_read_unlock()))
            return {};  // leaf_guard destructor handles unlock
        leaf->template set_value<Value>(existing_value);
        return false;
    }

    // action == upsert_action::erase — Phase 2
    UNODB_DETAIL_ASSERT(action == upsert_action::erase);
    // Release locks and fall through to remove path (Phase 2).
    // For now: release locks, return false, caller does separate remove().
    if (UNODB_DETAIL_UNLIKELY(!parent_critical_section.try_read_unlock()))
        return {};
    if (UNODB_DETAIL_UNLIKELY(!node_critical_section.try_read_unlock()))
        return {};
    return false;  // Phase 2: implement inline erase
}
```

#### 4.5.3 `update` Action — VIS Path

At the VIS duplicate-detection site, we hold:
- `parent_critical_section` — read lock on the **grandparent** (already released by this point in the current code, but we can restructure)
- `node_critical_section` — read lock on the **inode** containing the packed value slot

The packed value lives in the inode's `children[]` array. To modify it:

1. Unpack to local: `auto val = art_policy::unpack_value(child_in_parent->load());`
2. Invoke lambda: `auto action = fn(val);`
3. If `action == update`:
   a. Upgrade `node_critical_section` to `write_guard` on the inode.
   b. If upgrade fails → return `{}` (restart).
   c. Repack and write: `*child_in_parent = art_policy::pack_value(val);`

```cpp
if (inode->is_value_in_slot(node_type, ci_chk)) {
    auto existing_value = art_policy::unpack_value(child_in_parent->load());
    if (UNODB_DETAIL_UNLIKELY(!node_critical_section.check())) return {};

    const auto action = fn(existing_value);

    if (action == upsert_action::keep) {
        if (UNODB_DETAIL_UNLIKELY(!parent_critical_section.try_read_unlock()))
            return {};
        if (UNODB_DETAIL_UNLIKELY(!node_critical_section.try_read_unlock()))
            return {};
        return false;
    }

    if (action == upsert_action::update) {
        // Upgrade inode lock to write.
        optimistic_lock::write_guard inode_guard{
            std::move(node_critical_section)};
        if (UNODB_DETAIL_UNLIKELY(inode_guard.must_restart())) return {};
        if (UNODB_DETAIL_UNLIKELY(!parent_critical_section.try_read_unlock()))
            return {};
        *child_in_parent = art_policy::pack_value(existing_value);
        return false;
    }

    // erase — Phase 2
    // ...
}
```

#### 4.5.4 `erase` Action — Deferred to Phase 2

The `erase` action requires invoking the existing `remove` machinery, which involves:
- Node shrinking (I16→I4, I48→I16, etc.)
- I4 collapse (promote remaining child)
- Chain cleanup (for `key_view`)
- Multiple write guard acquisitions (parent, node, child)

This is significantly more complex than `update` because:
1. The lock state at the duplicate-detection point (two read locks) is different from what `remove_or_choose_subtree` expects.
2. Remove needs write locks on parent, node, and potentially grandparent for shrinking.
3. The existing remove code is structured as a top-down traversal, not as a "positioned delete."

**Recommendation**: Phase 1 delivers `keep` and `update`. For `erase`, the caller does a separate `remove()` call. Phase 2 adds inline `erase` by refactoring the remove internals into a "positioned remove" helper.

### 4.6 `erase_fn` Companion API

```cpp
template <typename FN>
[[nodiscard]] bool erase_fn(Key k, FN fn);
// where FN = bool(const value_type&)
```

Implementation: follow the `get` path to find the key. If found, invoke `fn(value)`. If `fn` returns `true`, invoke `remove`. For `olc_db`, this is a `try_erase_fn` in a retry loop. The positioned-read part is like `try_get`; the conditional-erase part reuses `try_remove` internals.

This can also be deferred to Phase 2 since it requires the same "positioned remove" infrastructure.

### 4.7 Internal Plumbing

#### New Internal Methods

For `db`:
```cpp
template <typename FN>
[[nodiscard]] bool insert_or_resolve_internal(art_key_type k, value_type v, FN fn);
```

For `olc_db`:
```cpp
template <typename FN>
[[nodiscard]] try_update_result_type try_insert_or_resolve(
    art_key_type k, value_type v, FN fn,
    olc_db_leaf_unique_ptr_type& cached_leaf);
```

These are clones of `insert_internal` / `try_insert` with the lambda invocation at the duplicate-detection sites.

#### Template Approach: Avoid Code Duplication

Rather than duplicating the entire `try_insert` function, use a tag-dispatch or template parameter to control behavior at the duplicate site:

```cpp
// Tag types
struct insert_only_tag {};
struct insert_or_resolve_tag {};

template <typename InsertPolicy, typename... FnArgs>
[[nodiscard]] try_update_result_type try_insert_impl(
    art_key_type k, value_type v,
    olc_db_leaf_unique_ptr_type& cached_leaf,
    FnArgs&&... fn_args);
```

At the duplicate site:
```cpp
if constexpr (std::is_same_v<InsertPolicy, insert_or_resolve_tag>) {
    // invoke lambda, handle action
} else {
    return false;  // plain insert
}
```

This keeps the complex traversal logic in one place.

## 5. Phasing

### Phase 1: `keep` + `update` only

1. Add `set_value<Value>` to both leaf specializations.
2. Add `upsert_action` enum to `art_common.hpp`.
3. Implement `insert_or_resolve` for `db` (both fixed-key and key_view paths).
4. Implement `insert_or_resolve` for `mutex_db` (delegates to `db`).
5. Implement `insert_or_resolve` for `olc_db`:
   - Keyed-leaf path: upgrade leaf lock to write, set_value.
   - VIS path: upgrade inode lock to write, repack value.
   - `erase` action: assert-fail or return `keep` with a diagnostic.
6. Tests for all three db types.

### Phase 2: `erase` action + `erase_fn`

1. Refactor `remove_or_choose_subtree` into a "positioned remove" helper.
2. Implement inline `erase` at the duplicate-detection sites.
3. Implement `erase_fn` for all three db types.
4. Tests for erase scenarios.

## 6. Lock Analysis Summary

| Path | Locks Held at Duplicate | `update` Needs | `erase` Needs |
|------|------------------------|----------------|---------------|
| Keyed-leaf (olc) | parent RCS + leaf RCS | Upgrade leaf RCS → write_guard | Parent + leaf write_guards, shrink logic |
| VIS (olc) | parent RCS + inode RCS | Upgrade inode RCS → write_guard | Parent + inode write_guards, shrink logic |
| Keyed-leaf (db) | none (single-threaded) | Direct memcpy | Direct remove |
| VIS (db) | none (single-threaded) | Direct store | Direct remove |
| mutex_db | Global mutex held | Same as db | Same as db |

## 7. Test Strategy

### Unit Tests

1. **Basic insert_or_resolve — insert path**: Key absent → inserts, returns `true`. Lambda not called.
2. **keep**: Key present → lambda returns `keep` → value unchanged, returns `false`.
3. **update**: Key present → lambda mutates value → value changed, returns `false`. Verify with `get()`.
4. **update idempotency**: Call `insert_or_resolve` twice with `update` → second call sees first update's value.
5. **erase** (Phase 2): Key present → lambda returns `erase` → key removed. Verify `get()` returns empty.
6. **Mixed operations**: Insert N keys, then `insert_or_resolve` on each with conditional update.

### Concurrency Tests (olc_db)

7. **Concurrent insert_or_resolve + get**: Multiple threads doing `insert_or_resolve` on overlapping keys while readers do `get`. Verify no crashes, values are consistent.
8. **Concurrent insert_or_resolve + insert_or_resolve**: Two threads racing to update the same key. Both should succeed (one inserts, one resolves).
9. **OLC restart coverage**: Use sync points to force write_guard upgrade failures. Verify the operation retries and eventually succeeds.
10. **Concurrent insert_or_resolve + remove**: One thread does `insert_or_resolve(update)`, another does `remove`. No crashes, final state is consistent.

### Type Coverage

11. Test with `<uint64_t, uint64_t>` (fixed key, fixed value — keyed-leaf path).
12. Test with `<key_view, uint64_t>` (variable key, VIS path — packed value).
13. Test with `<key_view, value_view>` (variable key, variable value — keyless leaf path).

### Edge Cases

14. Single-entry tree: root is a leaf → `insert_or_resolve` on that key.
15. Empty tree: `insert_or_resolve` → should insert.
16. `insert_or_resolve` after `clear()`.

## 8. Open Questions

1. **`value_view` update**: When `Value = value_view`, the leaf is immutable-size. Should `update` be restricted to same-size values, or should it allocate a new leaf? Recommend: restrict to same-size for Phase 1, document the limitation.

2. **Lambda exception safety**: If the lambda throws, what state should the tree be in? Recommend: the value is unmodified (lambda operates on a local copy; write-back only happens after lambda returns successfully).

3. **Return type enrichment**: Should `insert_or_resolve` return more than `bool`? E.g., `std::pair<bool, upsert_action>` to tell the caller what happened? The issue spec says `bool` (true = inserted). The action is known to the caller since they returned it from the lambda.

4. **Naming**: `insert_or_resolve` vs `upsert` vs `uprase_fn`. The issue uses `insert_or_resolve` which is descriptive. libcuckoo uses `uprase_fn`. Recommend: keep `insert_or_resolve` for clarity.

## 9. Round 1 Findings — Resolutions

This section addresses the critical and high-priority findings from the
Round 1 adversarial design review (2026-04-25).

### 9.1 CRITICAL: Lambda Re-execution on OLC Restart (Correctness A.1.1, Concurrency §1.1)

**Finding:** The lambda may execute multiple times with stale values when
the OLC write_guard upgrade fails. If the lambda has side effects (logging,
external counters), those side effects are not rolled back.

**Resolution — Document the contract explicitly:**

> **CONTRACT:** The resolver lambda MUST be idempotent with respect to
> external side effects. It MAY be invoked multiple times on the same
> `insert_or_resolve` call due to OLC optimistic lock restarts. Each
> invocation receives the value as it existed at the time of the optimistic
> read; if the read is stale (concurrent writer intervened), the write-back
> is suppressed and the operation restarts with a fresh read.
>
> Lambdas that only mutate the `existing` parameter and return an action
> are inherently safe — the local copy is discarded on restart. Lambdas
> with external side effects (logging, counters, secondary index updates)
> must be designed to tolerate re-execution.

**Design change:** Add this contract to the `insert_or_resolve` Doxygen
comment (§4.1) and to the public API header documentation.

**Why not restructure to call lambda under write_guard?** Calling the lambda
after acquiring the write_guard would eliminate re-execution but would hold
the write lock for the duration of the lambda. This blocks all concurrent
readers on the same node (OLC readers spin on locked nodes). For short
lambdas (the common case), the current design — lambda on local copy, then
upgrade — minimizes write-lock hold time. The tradeoff is documented
re-execution vs. longer lock hold time. We choose shorter lock hold time
with documented re-execution, matching the OLC philosophy of optimistic
reads with validation.

**Test requirement added to §7:** Test A.1.1 — concurrent `insert_or_resolve`
on the same key with incrementing lambda. Verify final value equals
`original + sum_of_all_increments` (no lost updates).

### 9.2 CRITICAL: `value_view` Update Size Constraint (Correctness A.1.4)

**Finding:** If `Value = value_view` and the lambda changes the value to a
different size, `set_value` writes past the leaf boundary → memory corruption.
For VIS values, size change is impossible (packed into `node_ptr`). For
keyed-leaf values with `value_view`, the leaf allocation is fixed-size.

**Resolution — Compile-time and runtime constraints:**

1. **Phase 1 constraint (compile-time):** `insert_or_resolve` with `update`
   action is only supported for fixed-size `Value` types where
   `sizeof(Value)` is known at compile time. For `value_view` values,
   the `update` action is a **compile error** in Phase 1.

   Implementation: `static_assert(!std::is_same_v<value_type, value_view>)`
   in the `update` branch, with a clear error message:
   ```cpp
   static_assert(!std::is_same_v<value_type, value_view>,
       "insert_or_resolve with update action requires fixed-size values. "
       "For value_view, use erase + re-insert with the new value.");
   ```

2. **Phase 2 (future):** If `value_view` update is needed, the `update`
   path must allocate a new leaf, copy the key, write the new value, and
   atomically swap the parent's child pointer (same as insert). This is
   equivalent to erase + insert but atomic under the write_guard.

3. **VIS path:** No constraint needed — VIS values are always
   `sizeof(Value) <= sizeof(uint64_t)`, packed/unpacked via XOR. Size
   cannot change.

**Design change:** Add the `static_assert` to §4.5.2 and §4.3. Update §8
Open Question 1 to mark it as resolved.

### 9.3 HIGH: Test Plan Gaps — Concurrent CAS Scenarios (Correctness A.1.1–A.1.3)

**Finding:** The test plan (§7) lacks tests for:
- Concurrent `insert_or_resolve` on the same key (A.1.1)
- `insert_or_resolve` during node growth (A.1.2)
- `insert_or_resolve` on a key being concurrently removed (A.1.3)

**Resolution — Add tests 17–22 to §7:**

17. **Concurrent CAS same key (increment):** N threads each call
    `insert_or_resolve(K, V, [](auto& v) { v += 1; return update; })`.
    Final value == original + N. Tests OLC restart correctness.

18. **CAS during I4→I16 growth:** Thread T1 does `insert_or_resolve(update)`
    on key K in an I4 node. Thread T2 inserts a new key triggering growth.
    Use `sync_before_insert_grow_guard` to control interleaving. T1 must
    restart and succeed after growth completes.

19. **CAS on key being removed:** Pre-insert K. T1 pauses at duplicate
    detection (sync point). T2 removes K. T1 resumes — upgrade fails,
    restarts, takes insert path. Final: `get(K) == V` (the insert value).

20. **CAS + concurrent scan:** T1 does `insert_or_resolve(update)` while
    T2 does `scan_range`. Scan must see either the old or new value, never
    a torn read. (OLC write_guard prevents torn reads by design.)

21. **CAS stress (random ops):** Add `insert_or_resolve` as a 5th operation
    in `random_op_thread` (existing concurrency test infrastructure).

22. **CAS idempotency under contention:** Lambda that logs invocation count
    to a thread-local counter. After N concurrent CAS operations on the same
    key, verify that the lambda was called ≥ N times (due to restarts) but
    the value reflects exactly N successful updates.

### 9.4 HIGH: Branch Prediction Hint for CAS Path (Performance §2.1)

**Finding:** The `UNODB_DETAIL_UNLIKELY` hint on the duplicate-detection
branch is wrong for `insert_or_resolve` where duplicates are the expected
case.

**Resolution:** Use the template policy tag to select the hint:

```cpp
if constexpr (std::is_same_v<InsertPolicy, insert_or_resolve_tag>) {
    if (k.cmp(existing_key) == 0) {  // no UNLIKELY — duplicates expected
        // invoke lambda
    }
} else {
    if (UNODB_DETAIL_UNLIKELY(k.cmp(existing_key) == 0)) {
        return false;  // plain insert — duplicates rare
    }
}
```

This is a zero-cost change — the `if constexpr` is resolved at compile time.

### 9.5 MEDIUM: API Naming — `insert_or_resolve` vs `upsert` (API §1)

**Finding:** "resolve" is misleading — it implies arbitration between two
values. The industry-standard term is "upsert."

**Resolution — Keep `insert_or_resolve` for now, add alias later:**

Rationale: The GitHub issue (#847) uses `insert_or_resolve` and the
maintainer chose it deliberately. The name is more descriptive than `upsert`
for this specific API where the lambda *resolves* what to do with the
existing entry. We will not rename at this stage to avoid churn on the
issue tracker. A `using upsert = insert_or_resolve` alias can be added
post-merge if discoverability is a concern.

**Status:** Deferred — not blocking.

### 9.6 MEDIUM: Lambda Signature — Key Availability (API §2)

**Finding:** The lambda cannot see which key it is resolving without
capturing it.

**Resolution — Provide two overloads via concepts (C++20):**

```cpp
// Overload 1: key-blind (common case)
template <typename FN>
  requires std::invocable<FN, value_type&>
[[nodiscard]] bool insert_or_resolve(Key k, value_type v, FN fn);

// Overload 2: key-aware
template <typename FN>
  requires std::invocable<FN, const Key&, value_type&>
[[nodiscard]] bool insert_or_resolve(Key k, value_type v, FN fn);
```

The key-aware overload passes `k` (the original key argument) to the lambda.
This is zero-cost — the key is already on the stack. SFINAE/concepts
disambiguate at compile time.

**Design change:** Update §4.1 to show both overloads.

### 9.7 Resolved Open Questions (§8 Updates)

**Q1 (`value_view` update):** Resolved — compile-time restriction in Phase 1.
See §9.2.

**Q2 (Lambda exception safety):** Confirmed safe. The lambda operates on a
local copy. If it throws, the local copy is destroyed, read locks unwind via
RAII (`read_critical_section` destructor is a no-op — it doesn't release
anything, just stops checking). No write has occurred. The tree is unchanged.
Add a note to §4.5.2 confirming this.

**Q3 (Return type):** Keep `bool` for Phase 1 per issue spec. The caller
knows the action because they returned it from the lambda. A richer return
type can be added in Phase 2 if needed.

**Q4 (Naming):** See §9.5 — keep `insert_or_resolve`.
