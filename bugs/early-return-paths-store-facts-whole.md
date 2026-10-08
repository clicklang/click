# A function with early returns verifies in work quadratic in their count

## Violated invariant

A proof written with explicit simple tactics must verify in work near linear
in the selected C source, Click source, and certificate
(`docs/internals/verification-efficiency.md`). The checked execution stores
each path's facts whole. A function with `P` early returns, each after the
conditions of the returns before it, has `P + 1` paths, and path `k` holds
the `k` conditions that precede it, so the execution holds about `P^2/2` path
facts. Whatever reads every path's facts is then quadratic in `P`.
Post-execution `simp` and contract certification both do.

The efficiency page already lists this under the context-build rule as a
known violation with no regression. It is independent of how the function is
executed: outside the planner's own builds, about the same counts appear
whether `execute()` runs on the checked `Proof` or through the planner (71,
155, 419, and 1331 through the planner at the sizes below).

Measured on 2026-10-02 with `early_return_fan_out` from
`src/surface/tests/scaling_tests.rs` (a `malloc` null check, then `P`
`if (a == k) return k;` statements), proved by `execute(); simp();` against
`ensures result == a or result == -1`. Whole-verification context entries
(`context_rebuild_entries`) at 4, 8, 16, and 32 returns: 75, 159, 423, and
1335. The last doubling is 3.2 times.

`executing_a_fan_out_stays_on_the_proof_in_near_linear_work` pins only the
`execute` tactic's own work on this function, and
`grouped_proof_finalization_reads_each_path_once` pins only the implicit
empty-effect check. Neither bounds the whole verification.

## Measured sources

Stored path facts are one source among several. Each source below does work
proportional to a path's length once per path. Measured on 2026-10-05 at 4,
8, 16, 32, and 64 returns, in deterministic work units:

| | 4 | 8 | 16 | 32 | 64 |
|---|---|---|---|---|---|
| total, before | 7727 | 14947 | 33347 | 85907 | 254003 |
| total, transport search bounded | 6991 | 12739 | 25987 | 59411 | 153907 |
| total, terminal joins also fixed | 6811 | 12199 | 24151 | 52679 | 128167 |
| total, premise spelling also fixed | 6703 | 11873 | 23053 | 48693 | 113029 |
| `simp`, before premise spelling fix | 2070 | 4196 | 9456 | 24008 | 69240 |
| `simp`, now | 1962 | 3870 | 8358 | 20022 | 54102 |
| `execute`, before | 4054 | 7138 | 13906 | 29762 | 70690 |
| `execute`, now | 3874 | 6598 | 12070 | 23030 | 44950 |

Fixed:

- simp's snapshot-transport search
  (`try_snapshot_transport_closure_candidates`) offered the goal as a
  transport from every program point the path recorded, about `2k` attempts
  on path `k`. It now offers function entry and the eight most recent
  points; `simp_snapshot_transport_search_is_linear_in_early_returns` pins
  it.

- A terminal branch join re-recorded every enclosing arm's condition
  spelling into its parent (`merge_branch_surface_facts`,
  `execution_joins.rs`), so the innermost condition was recorded once per
  enclosing join, and `execute` grew 2.4 times per doubling. A terminal join
  has no successor and each path keeps its own spellings, so it no longer
  carries them; `executing_a_fan_out_is_near_linear_in_its_length` now runs
  to 64 returns.

- simp spelled every fact its derivation's selection held as a premise,
  all `k` conditions about `a` on path `k`, before a closer said which it
  cites. It now spells only the premises a recorded equality or
  signed-order path names, falling back to the whole selection when that
  closer misses, and spells none for a derivation that only selects a
  disjunct; `simp_premise_spelling_is_linear_in_early_returns` pins it.

- simp's constant-equality dependency selection now selects at most two
  premises from the exact constant index and checks an atomic derivation in
  that small context before falling back to connected selection. Earlier
  `a != j` guards are irrelevant to `result == a` when both terms are pinned
  to the same constant. `indexed_simp_premises_reduce_whole_early_return_work`
  measures the complete verification and bounds selection work at 4, 8,
  16, 32, and 64 returns; a negative postcondition remains rejected. The
  previous selection work at these sizes was 84, 232, 720, 2464, and 9024.

- Explicit early-return proof processing is now iterative, so
  `explicit_early_return_proof_completes_through_sixty_four_returns` extends through
  64 returns. The former region nesting limit no longer blocks that test.

- Contract preparation now reuses the persistent body context retained by
  the checked Proof completion producer for paths without observable entry
  resource facts. Entry-dependent resources are still evaluated under entry
  premises alone, and only assumable obligations are added afterwards. Typed
  load bindings and private effect facts are retained with the body context.
  `completed_early_return_contexts_are_reused_for_certification` bounds this
  phase for both grouped and explicit proofs, and whole-verification context
  construction for the grouped proof, through 64 returns.

- Decided C branches now build allocation-resolution assumptions only while
  an allocation is pending. Previously every later branch eagerly rebuilt
  the statement-local context before asking a settled allocation to resolve
  again. Temporary caller instrumentation identified this source in
  `execute_branch_step_from_frontier_position`. The context-reuse regression
  also bounds the named branch-allocation phase for both proof forms through
  64 returns.

Remaining. Checked paths still retain flat facts. Outcome goals still import
those facts once per path. Legacy execution producers and paths with observable
entry-resource propositions also keep the original certification rebuild to
preserve resource-fact/path-fact precedence.

Measurements on 2026-10-07, after indexed premise selection, at 4, 8, 16, 32,
and 64 returns:

| proof / metric | 4 | 8 | 16 | 32 | 64 |
| --- | --- | --- | --- | --- | --- |
| grouped total work, before context reuse | 6850 | 11836 | 21976 | 42848 | 86896 |
| grouped total work, context reused | 6800 | 11728 | 21704 | 42056 | 84296 |
| grouped context entries, before | 69 | 131 | 303 | 839 | 2679 |
| grouped context entries, reused | 49 | 77 | 133 | 245 | 469 |
| explicit total work, before | 6329 | 10855 | 20419 | 44865 | 130097 |
| explicit total work, context reused | 6279 | 10747 | 20147 | 44073 | 127497 |
| explicit context entries, before | 64 | 122 | 396 | 1772 | 7596 |
| explicit context entries, reused | 44 | 68 | 226 | 1178 | 5386 |

Measured against base `d4ded0835`, avoiding settled allocation resolution
reduces the explicit context entries to 44, 68, 198, 718, and 2526, and total work to 6279, 10747, 20087, 43453,
and 124221, with the C and proof unchanged. Grouped measurements are unchanged.
The named branch-allocation phase costs 26 units at 16, 32, and 64 returns;
smaller explicit proofs do not visit that driver.
The branch fix removes 2860 rebuilt entries at 64 returns, but the explicit
proof's whole-verification curve is still a remaining violation. Its existing
scaling guard tolerates 3x growth per doubling and missed these counts. The completion/certification part is now shared in both
proof forms; most total work is outside the named completion phases.

Explicit statement steps also used to rebuild the local case context at each
return. They constructed a fresh local fact list from all enclosing proof
cases, so merely consulting the list's cached context still rebuilt the prefix.
The kernel now retains a persistent context when it admits a logical frontier
case. A step reuses that prefix only when every written case selects a distinct
available premise covered by it; duplicates, dropped cases and other producers
keep the ordered fold. Statement-local resource observations follow the case
prefix, and the successor carries the context into return preparation.

Measured on base `0aecf5bd5`, with the original C and both proofs unchanged:

| proof / metric | 4 | 8 | 16 | 32 | 64 |
| --- | --- | --- | --- | --- | --- |
| grouped context entries, after case-context retention | 53 | 81 | 137 | 249 | 473 |
| explicit context entries, before | 44 | 68 | 196 | 716 | 2524 |
| explicit context entries, retained | 46 | 70 | 129 | 257 | 513 |
| explicit total work, before | 6279 | 10747 | 20061 | 43427 | 124195 |
| explicit total work, retained | 6281 | 10749 | 19994 | 42968 | 122184 |

`completed_early_return_contexts_are_reused_for_certification` now bounds
whole-verification context construction in both forms, plus the named return
context phase. The explicit total-work curve still violates the near-linear
contract: terminal joins rebuild flat returned-path containers, and flat path
facts are still imported per outcome. This bug remains open for those costs.

## Intended regression

A scaling test over `early_return_fan_out` at 4, 8, 16, and 32 returns that
measures the whole verification, not one named tactic: total deterministic
work and `context_rebuild_entries`. Each doubling of the returns must at most
slightly more than double both. Run it for the grouped `execute(); simp();`
proof and for the same proof written as explicit `step()` and `branch`
tactics, so a fix cannot live only in a smart tactic. Keep the claim
unchanged, and include a variant whose postcondition is false on the last
path so the negative result is still reported.

## Acceptance criteria

- Paths that share a prefix share that prefix's facts in the checked
  execution, so the stored path facts of this function are linear in `P`.
- Post-execution `simp` and contract certification read a shared prefix
  once, not once per path that extends it.
- The regression above passes at all four sizes for both proof forms, and
  the known-violation paragraph in
  `docs/internals/verification-efficiency.md` is removed or narrowed to what
  remains.
- Existing positive and negative proof behavior is preserved, and
  `scripts/check.sh` passes.
