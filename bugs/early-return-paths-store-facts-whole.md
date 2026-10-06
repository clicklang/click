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
| `simp`, bounded | 2070 | 4196 | 9456 | 24008 | 69240 |
| `execute` | 4054 | 7138 | 13906 | 29762 | 70690 |

Fixed:

- simp's snapshot-transport search
  (`try_snapshot_transport_closure_candidates`) offered the goal as a
  transport from every program point the path recorded, about `2k` attempts
  on path `k`. It now offers function entry and the eight most recent
  points; `simp_snapshot_transport_search_is_linear_in_early_returns` pins
  it.

Remaining, by the work each still charges at 32 and then 64 returns:

- A terminal branch join re-records every enclosing arm's condition
  spelling into its parent (`merge_branch_surface_facts`,
  `execution_joins.rs`), so the innermost condition is recorded once per
  enclosing join: 2244 then 8580 `record_lowering` calls, 5028 then 18212
  units, with 2514 then 9106 and 1250 then 4546 in the lookups beside it.
- Alpha-key work in `fact_keys.rs` (`alpha_work_checkpoint`): 4352 then
  16896.
- Assumption-context work at `assumptions.rs` near lines 5164 and 3616, the
  latter with `proposition_search.rs:1874`: 2883 then 9827, and 1088 then
  4224 each.
- Step recording at `cursor_execution.rs:1289`: 1290 then 4618.
- Each path's outcome goal re-adds the path's conditions to the root facts
  (`outcomes_and_focus.rs`, the `with_kernel_checked_fact` loop): 957 then
  2925.
- Kernel contract certification rebuilds each path's assumptions from its
  flat fact list (`contract_claims.rs`, `assumptions_with_path_context`):
  693 then 2405 context entries, and a simp route rebuilds a context from
  its selected premises (`equality_rewrite.rs`, `pure_context`): 528 then
  2080.
- `execute` itself grows 2.4 times per doubling.

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
