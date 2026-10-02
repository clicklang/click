# `loop` expansion emits an empty `by` block

## Violated invariant

A smart tactic that verifies must expand to explicit tactics that verify the same claim: `click expand` output has to parse, re-verify in the retained session and through the direct targeted entry point, and contain no smart tactic at the audited site. `click audit` checks exactly this, and CLAUDE.md lists an expansion that fails or does not re-verify as a tooling defect that blocks feature work.

For a ranked loop with no invariant, the expanded `loop` tactic contains `by { }`, which is not Click: `` `by` block must contain at least one tactic ``. The expander already keeps `assumption();` when a block would otherwise be emptied elsewhere; this site does not.

The root cause has not been investigated. The fixtures below may not all share one; split this file if they do not.

## Reproduction

On `master` at `b3ab98334`, the fixture verifies (`MDTEST_FILTER=a_ranked_loop_with_no_invariant_closes_a_branching_body cargo test --test mdtests`) and its audit fails:

```
click audit mdtests/a_ranked_loop_with_no_invariant_closes_a_branching_body.md
```

fails at `mdtests/a_ranked_loop_with_no_invariant_closes_a_branching_body.md:31:5` (`loop`) with:

```
the expansion did not parse as Click: line 9, column 9: `by` block must contain at least one tactic
```

The gate does not audit fixtures, which is why these pass `scripts/check.sh`.

Affected fixtures (2), each failing `click audit` the same way:

- `mdtests/a_ranked_loop_with_no_invariant_closes_a_branching_body.md`
- `mdtests/a_ranked_unsigned_loop_with_no_invariant_closes_a_branching_body.md`

## Intended regression

Reduce `mdtests/a_ranked_loop_with_no_invariant_closes_a_branching_body.md` to the smallest sidecar whose audit fails this way and add it as a retained expansion-audit case, so the fixture is expanded and re-verified by the gate rather than only verified. Do not change the fixture's C or weaken its proof to make the expansion pass.

## Acceptance criteria

- `click audit` passes for every fixture listed above, with no change to their C sources or contracts.
- The reduced case is audited by `scripts/check.sh`.
- The fix is in the expander, the smart tactic's certificate, or the checker, not a per-fixture special case; `scripts/check.sh` passes.
