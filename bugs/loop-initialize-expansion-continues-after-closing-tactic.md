# Expanded `simp` in a loop `initialize` emits a tactic after one that closed the goal

## Violated invariant

A smart tactic that verifies must expand to explicit tactics that verify the same claim: `click expand` output has to parse, re-verify in the retained session and through the direct targeted entry point, and contain no smart tactic at the audited site. `click audit` checks exactly this, and CLAUDE.md lists an expansion that fails or does not re-verify as a tooling defect that blocks feature work.

The expansion places a `have` after an `apply` that already closed the entry goal, which the checker rejects: only `assumption`, `simp`, or `normalize` may follow a goal-closing tactic.

The root cause has not been investigated. The fixtures below may not all share one; split this file if they do not.

## Reproduction

On `master` at `b3ab98334`, the fixture verifies (`MDTEST_FILTER=loop_explicit_initialize_and_preserve cargo test --test mdtests`) and its audit fails:

```
click audit mdtests/loop_explicit_initialize_and_preserve.md
```

fails at `mdtests/loop_explicit_initialize_and_preserve.md:47:13` (`simp`) with:

```
loop 0 invariant 0 entry, owing `acceptable(x)`: `loop_explicit_initialize_and_preserve.contract` proof step tactic 2: `have` follows a goal-closing tactic: `apply` already closed this goal, so only `assumption`, `simp`, or `normalize` may follow it
```

The gate does not audit fixtures, which is why these pass `scripts/check.sh`.

Affected fixtures (1), each failing `click audit` the same way:

- `mdtests/loop_explicit_initialize_and_preserve.md`

## Intended regression

Reduce `mdtests/loop_explicit_initialize_and_preserve.md` to the smallest sidecar whose audit fails this way and add it as a retained expansion-audit case, so the fixture is expanded and re-verified by the gate rather than only verified. Do not change the fixture's C or weaken its proof to make the expansion pass.

## Acceptance criteria

- `click audit` passes for every fixture listed above, with no change to their C sources or contracts.
- The reduced case is audited by `scripts/check.sh`.
- The fix is in the expander, the smart tactic's certificate, or the checker, not a per-fixture special case; `scripts/check.sh` passes.
