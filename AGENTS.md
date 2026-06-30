# Agent Bootstrap — unodb

## Scope
- Project scope: `S-ef6c488c` (unodb)
- Feature scope: `S-e413568f` (unodb-leaf-elimination)
- Repo: `unodb-dev/unodb` (upstream), `thompsonbry/unodb` (fork)
- Fork remote: `origin` (SSH push target — updates upstream PRs automatically)
- Upstream remote: `upstream` (read-only reference)

## Repo Orientation

At the start of every session, read:
1. This file
2. `.unodb-work/blackboards/session-context.md` — active branch state, known bugs, task status
3. `.unodb-work/blackboards/roadmap.md` — feature roadmap

## Graph Orientation

On startup:
1. `ScopeGetIssues(scope_id="S-ef6c488c")` — open issues
2. `TaskList(scope_id="S-ef6c488c")` — current tasks
3. `ConstraintList(scope_id="S-ef6c488c")` — active constraints

Key graph procedures (use `ProcedureGet` to load):
- `PR-685965e7` — Complete push-to-upstream workflow
- `PR-7c3bbffe` — Full pre-push checks
- `PR-9d9efa19` — Check upstream CI status for a PR
- `PR-a5209341` — Trigger and check MSVC CI on fork
- `PR-df57e832` — Coverage CI — trigger, download, and patch analysis
- `PR-1ac21bea` — clang-format-21 via docker
- `PR-1f155b37` — Docker-based compiler and GCC testing
- `PR-7b4b575b` — Sanitizer builds (UBSan, ASan, TSan)
- `PR-5baa595c` — CI Tooling Reference (index of all scripts)
- `PR-de318874` — GitHub Design Review (Trident-adapted for GitHub PRs)
- `PR-1782864f` — Design → Implementation Spec Decomposition (v3)

Key decisions:
- `D-ca0f9841` — Rebase strategy for post-#845 branch consolidation
- `D-ca6e0715` — Monolith (937685c4) → #845 + #837-v2 relationship
- `D-b2095642` — 937685c4 pin for other projects (brazil-deps overlay)
- `D-71d95041` — upsert: rename, key-blind lambda, static_assert not concepts
- `D-b4fe263d` — upsert erase: Semantics A (CAS — erase only observed value)

Key resources:
- `R-82734c9f` — Branch crosswalk (.unodb-work/blackboards/branch-crosswalk.md)

## Active Branch Stack

| Scope | Branch | PR | HEAD | Status |
|-------|--------|-----|------|--------|
| S-c250a9c8 | `design/cas-847` | #854 | `b2883e4c` | Needs fixes (CAS-erase bypass + style) |
| S-ef6c488c | `feat/bulk-load-636` | #864 | `23ad7362` (local) | Portability fix local, CodeRabbit feedback pending |
| S-ef6c488c | `master` | — | `f52f55b6` | Post-#863 MSVC LLVM fix |
| S-ef6c488c | `feat/tla-olc-art-verification` | — | `74e25fa4` | Needs rebase onto current master, no PR yet |

```
upstream/master (f52f55b6) — #845, #849, #851, #856, #863 all merged
  ├── design/cas-847 (1 commit) — PR #854 open, CI green, awaiting merge
  ├── feat/tla-olc-art-verification (8 commits) — needs rebase, no PR yet
  ├── design/bulk-load-636 — design done, implementation pending
  └── bench/ndb-spog-scale (local only, benchmark files)
```

## CI Process

All CI tooling lives in `.unodb-work/`. Scripts are executable.

### Before pushing (MANDATORY — no exceptions)
```bash
bash .unodb-work/pre-push-checks.sh        # FULL: format, build, test, sanitizers
```
**Do NOT use `--quick` before pushing to origin.** The full run catches issues
that waste 12+ hours of CI time if missed. `--quick` is only for local iteration.

### Fork CI (MSVC + coverage) — run BEFORE pushing to upstream
```bash
bash .unodb-work/trigger-msvc-ci.sh         # Merges branch into msvc-check, pushes
bash .unodb-work/trigger-coverage-ci.sh     # Merges branch into coverage-check, pushes
bash .unodb-work/check-msvc-ci.sh           # Poll MSVC status
bash .unodb-work/check-coverage-ci.sh       # Poll coverage status
bash .unodb-work/check-coverage-ci.sh --download  # Download lcov artifacts
bash .unodb-work/parse-lcov-patch.sh        # Patch coverage analysis (target ≥ 98.63%)
```

### Upstream CI — poll after pushing
```bash
bash .unodb-work/check-ci.sh https://github.com/unodb-dev/unodb/pull/<N>
```
Known infra failures (not our code): SonarCloud, claude-review.
**Read the actual CI failure logs** — do not assume failures are FPs without checking.

### Formatting
```bash
docker run --rm -v "$(pwd):/src" -w /src unodb-clang21 \
  clang-format-21 -i <files>                    # Fix
docker run --rm -v "$(pwd):/src" -w /src unodb-clang21 \
  clang-format-21 --dry-run -Werror <files>     # Check
```

## Git Rules

- **Never amend commits** — always make new ones.
- **Never `git add -A`** — stage specific files.
- **Push to `origin`** (fork) via SSH — this updates the upstream PR.
- **clang-format-21 via docker** (`unodb-clang21`) is canonical.
- **`gh` CLI token**: Run `unset GITHUB_TOKEN` before `gh pr create` so
  `gh` falls back to `~/.config/gh/hosts.yml` which has `repo` scope.

## Subagent Workspace Rule

**Agents MUST NOT dispatch parallel subagents that read and write to the same
checked-out workspace.** Concurrent writes cause merge conflicts, lost changes,
and broken builds. Parallelize across separate workspaces or serialize within one.

## Push Workflow (complete sequence)

1. Run FULL pre-push checks: `bash .unodb-work/pre-push-checks.sh`
2. Trigger fork CI: MSVC + coverage (scripts above)
3. Wait for MSVC to pass (9/9 jobs)
4. Wait for coverage CI to pass, then download and verify patch coverage:
   ```bash
   bash .unodb-work/check-coverage-ci.sh --download
   bash .unodb-work/parse-lcov-patch.sh   # MUST show ≥ 98.63%
   ```
   If patch coverage is below target, fix uncovered lines before pushing.
5. Push: `git push origin <branch>`
6. Poll upstream CI and READ failure logs — do not assume FPs

## The Old Monolith (937685c4)

The old `pr-837-allocator-decoupling` branch at commit `937685c4` was a monolithic
development branch (131 commits). #845 is a clean rewrite; #837-v2 (now PR #849)
cherry-picks the allocator decoupling onto post-#845 master.

**Other local projects are pinned to this commit** via brazil-deps overlay.
Full crosswalk: `.unodb-work/blackboards/branch-crosswalk.md`.

## Merge Plan

1. ~~#845 merges to upstream/master~~ ✅ DONE (squash-merged as `36e47703`)
2. ~~#849 (allocator decoupling)~~ ✅ DONE (merged 2026-05-18)
3. ~~#851 (scan_from backtrack)~~ ✅ DONE (merged 2026-05-21)
4. ~~#856 (small-vector iter)~~ ✅ DONE (merged 2026-06-16 as `6333b9d8`)
5. **#847 (CAS/upsert)** — PR #854 open, needs CAS-erase fix + style items, then merge
6. **#636 (bulk load)** — PR #864 open, needs portability push + CodeRabbit fixes
7. **TLA+ specs** — rebase needed onto current master, then PR
8. **Update brazil-deps overlay** in other projects (post-#849, can do anytime)

## Known Bugs

- ~~**T-5bec51c4** (high): `db::scan_from` backtrack failure~~ → Fixed in PR #851 (merged)
- **#853**: Benchmark CI timeouts on ASan/ARM64 — split into separate workflow (open)
- **#860**: Path-reuse refactoring for olc_art.hpp try_insert/try_upsert (follow-up, filed)

<!-- NOTE (2026-06-18): Prior "PR #854 CI failures" entries removed — they were from
     push be9adc27 (51-commit branch). Current push 614bfaea is a clean squash with
     all reviewer fixes applied. Actual CI failures (if any) will be determined when
     runners pick up the queued jobs. Suspect clang-tidy-17 and UBSan clang-14 may
     still flag issues since our local checks only run clang-tidy-21 and clang-17 sanitizers,
     but this is unconfirmed. -->

## Local Tooling Gap (discovered 2026-06-10)

Local pre-push checks use GCC 7.3 (2018) for sanitizers and clang-tidy-21 only.
Upstream CI uses GCC 10-14, clang 11-21, clang-tidy-17, and MSVC 14.51.362.
This means local checks can pass while upstream fails. Need:
- Docker-based sanitizer builds with clang ≥ 14 or GCC ≥ 10
- Add clang-tidy-17 check alongside clang-tidy-21
- Fork MSVC runner image needs update to match upstream

## Code Quality Rules (from CONTRIBUTING.md)

- `const` everywhere possible (except by-value params and movable fields).
- `constexpr` everywhere it is legal.
- `[[nodiscard]]` on all value-returning functions by default.
- `noexcept` on everything that cannot throw.
- Pass by const reference for non-trivial types.
- All testable paths must be tested; LCOV_EXCL only for genuinely dead code.
- Coverage target: ≥ 98.63% patch coverage.
- Doxygen comments on all declarations including private members.
- A clean CI run is a prerequisite for merging.

## Resume State (2026-06-27T14:03 UTC)

### Current Work
- **#847 / PR #854 (CAS/upsert)**: `design/cas-847` at `17deeaa6` (pushed to origin).
  ALL review fixes done. value_view CAS update implemented. MSVC+coverage CI green.
  Upstream CI should be complete — check status on restart.
  If green: ready for maintainer merge.
- **#636 / PR #864 (bulk_load)**: `feat/bulk-load-636`, local commit `23ad7362` (not pushed).
  10 CodeRabbit comments — task T-ac1bc5a0 has full details. Paused for #854.

### Branch State
| Branch | HEAD | Remote | Status |
|--------|------|--------|--------|
| `master` | `f52f55b6` | upstream ✅ | Current upstream/master |
| `design/cas-847` | `17deeaa6` | origin ✅ | PR #854, pushed, awaiting upstream CI + merge |
| `feat/bulk-load-636` | `23ad7362` (local) | origin at `31bfbcaa` | PR #864, paused |
| `feat/tla-olc-art-verification` | `74e25fa4` | origin (stale) | Needs rebase, then PR |

### On Restart
1. Check upstream CI for PR #854: `bash .unodb-work/check-ci.sh https://github.com/unodb-dev/unodb/pull/854`
2. If CI green → notify user, ready for merge
3. If failures → gather all, batch fix
4. After #854 merges → switch to PR #864 bulk_load (T-ac1bc5a0)

## Emacs

- Show files to human: `tmux split-window -d -h -t $TMUX_PANE "emacs -nw file1 file2 ..."` — split closes on exit, list all files upfront.

## Build Rules

### TSan and OLC Fields

**Never use `DISABLE_TSAN` or `__attribute__((no_sanitize("thread")))`.** The
pre-push check enforces this mechanically.

OLC uses optimistic reads (read without lock, validate version after). TSan
cannot model this protocol and reports races on unprotected fields. The correct
fix is to wrap the field in the existing `in_critical_section<T>` template
(relaxed atomics that TSan understands) — NOT to suppress TSan.

Pattern:
- `in_critical_section<T>` (from `optimistic_lock.hpp`) — for OLC/concurrent use
- `in_fake_critical_section<T>` (from `in_fake_critical_section.hpp`) — for single-threaded `db`
- Both provide `load()` and `operator=(T)` with identical interfaces
- Template parameterize via `ArtPolicy::template critical_section_policy`

Example (value_bitmask_field):
```cpp
template <bool Enabled, class Storage, template <class> class CritSec>
struct value_bitmask_field {
  CritSec<Storage> bits{};  // NOT plain Storage
  void set(std::uint8_t i) noexcept {
    bits = static_cast<Storage>(bits.load() | (Storage{1} << i));
  }
};
```

For array-based fields, wrap each element: `std::array<CritSec<T>, N> bits{}`.

