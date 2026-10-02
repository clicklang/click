# Expanded `simp` in a loop `initialize` leaves the invariant entry goal open

## Violated invariant

A smart tactic that verifies must expand to explicit tactics that verify the same claim: `click expand` output has to parse, re-verify in the retained session and through the direct targeted entry point, and contain no smart tactic at the audited site. `click audit` checks exactly this, and CLAUDE.md lists an expansion that fails or does not re-verify as a tooling defect that blocks feature work.

Each fixture closes a loop invariant's entry obligation with `simp` (inline or in an `initialize` body). The expansion of that `simp` re-verifies as `loop initialization body did not close its goal`: the emitted explicit tactics stop short of the goal the smart tactic closed.

The root cause has not been investigated. The fixtures below may not all share one; split this file if they do not.

## Reproduction

On `master` at `b3ab98334`, the fixture verifies (`MDTEST_FILTER=loop_decreases_pure_expression cargo test --test mdtests`) and its audit fails:

```
click audit mdtests/loop_decreases_pure_expression.md
```

fails at `mdtests/loop_decreases_pure_expression.md:38:44` (`simp`) with:

```
loop 0 invariant 0 entry, owing `0 <= *box`: loop initialization body did not close its goal
```

The gate does not audit fixtures, which is why these pass `scripts/check.sh`.

Affected fixtures (6), each failing `click audit` the same way:

- `mdtests/loop_decreases_pure_expression.md`
- `mdtests/loop_frame_through_field_over_folded_binder_cells.md`
- `mdtests/loop_frame_through_folded_state_field_cells.md`
- `mdtests/loop_frame_through_parameter_over_folded_binder_cells.md`
- `mdtests/loop_initialize_narrows_a_held_byte_range_under_a_universal.md`
- `mdtests/loop_initialize_narrows_a_held_byte_range_without_a_count_bound.md`

## Intended regression

Reduce `mdtests/loop_decreases_pure_expression.md` to the smallest sidecar whose audit fails this way and add it as a retained expansion-audit case, so the fixture is expanded and re-verified by the gate rather than only verified. Do not change the fixture's C or weaken its proof to make the expansion pass.

## Acceptance criteria

- `click audit` passes for every fixture listed above, with no change to their C sources or contracts.
- The reduced case is audited by `scripts/check.sh`.
- The fix is in the expander, the smart tactic's certificate, or the checker, not a per-fixture special case; `scripts/check.sh` passes.
