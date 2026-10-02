# Expanded `simp` in a loop `initialize` emits an arithmetic step the checker rejects

## Violated invariant

A smart tactic that verifies must expand to explicit tactics that verify the same claim: `click expand` output has to parse, re-verify in the retained session and through the direct targeted entry point, and contain no smart tactic at the audited site. `click audit` checks exactly this, and CLAUDE.md lists an expansion that fails or does not re-verify as a tooling defect that blocks feature work.

The expansion of an invariant-entry `simp` contains an `arithmetic()` step inside a `have` body's `then` arm whose certificate the checker refuses: `signed_int32 arithmetic certificate rejected: the conclusion node does not establish the goal`. A smart tactic reported success but its generated certificate does not verify.

The root cause has not been investigated. The fixtures below may not all share one; split this file if they do not.

## Reproduction

On `master` at `b3ab98334`, the fixture verifies (`MDTEST_FILTER=loop_bundle_names_a_quantified_invariant_binder_as_written cargo test --test mdtests`) and its audit fails:

```
click audit mdtests/loop_bundle_names_a_quantified_invariant_binder_as_written.md
```

fails at `mdtests/loop_bundle_names_a_quantified_invariant_binder_as_written.md:50:13` (`simp`) with:

```
loop 0 invariant 0 entry, owing `0 == 0`: `count_up.contract` proof step tactic 8 > have body tactic 6 > then arm tactic 2: signed_int32 arithmetic certificate rejected: the conclusion node does not establish the goal
```

The gate does not audit fixtures, which is why these pass `scripts/check.sh`.

Affected fixtures (3), each failing `click audit` the same way:

- `mdtests/loop_bundle_names_a_quantified_invariant_binder_as_written.md`
- `mdtests/loop_initialize_narrows_a_held_range_under_a_universal.md`
- `mdtests/loop_quantified_viewable_invariant_bounded_by_its_views_clause.md`

## Intended regression

Reduce `mdtests/loop_bundle_names_a_quantified_invariant_binder_as_written.md` to the smallest sidecar whose audit fails this way and add it as a retained expansion-audit case, so the fixture is expanded and re-verified by the gate rather than only verified. Do not change the fixture's C or weaken its proof to make the expansion pass.

## Acceptance criteria

- `click audit` passes for every fixture listed above, with no change to their C sources or contracts.
- The reduced case is audited by `scripts/check.sh`.
- The fix is in the expander, the smart tactic's certificate, or the checker, not a per-fixture special case; `scripts/check.sh` passes.
