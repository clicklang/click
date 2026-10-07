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
  `explicit_early_return_proof_is_near_linear_in_its_returns` extends through
  64 returns. The former region nesting limit no longer blocks that test.

Remaining. Checked paths still retain flat facts. The whole-verification
context-rebuild count at 4, 8, 16, 32, and 64 returns is 69, 131, 303, 839,
and 2679. The indexed selection change does not remove this quadratic work.
The two remaining sources, measured at 32 and then 64 returns on 2026-10-05:

- Each path's outcome goal re-adds the path's conditions to the root facts
  (`outcomes_and_focus.rs`, the `with_kernel_checked_fact` loop): 957 then
  2925. The arm that reached the return already held those facts.
- Kernel contract certification rebuilds each path's assumptions from its
  flat fact list (`contract_claims.rs`, `assumptions_with_path_context`):
  693 then 2405 context entries. This and the item above are the stored
  path facts this bug was filed for; they need path facts shared across the
  paths that share a prefix.

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
