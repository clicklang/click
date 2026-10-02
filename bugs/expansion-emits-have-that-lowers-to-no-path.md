# Expansion of a by-value struct copy emits a `have` that lowers to zero paths

## Violated invariant

A smart tactic that verifies must expand to explicit tactics that verify the same claim: `click expand` output has to parse, re-verify in the retained session and through the direct targeted entry point, and contain no smart tactic at the audited site. `click audit` checks exactly this, and CLAUDE.md lists an expansion that fails or does not re-verify as a tooling defect that blocks feature work.

The expanded proof contains a `have` whose proposition the surface cannot lower: `the kernel lowering produced 0 paths, not one`. The proposition was produced by the expander itself from the checked state.

The root cause has not been investigated. The fixtures below may not all share one; split this file if they do not.

## Reproduction

On `master` at `b3ab98334`, the fixture verifies (`MDTEST_FILTER=struct_by_value_embedded_array_copy cargo test --test mdtests`) and its audit fails:

```
click audit mdtests/struct_by_value_embedded_array_copy.md
```

fails at `mdtests/struct_by_value_embedded_array_copy.md:63:6` (`auto`) with:

```
`finish.contract` proof step tactic 11: could not lower `have` proposition: the kernel lowering produced 0 paths, not one
```

The gate does not audit fixtures, which is why these pass `scripts/check.sh`.

Affected fixtures (2), each failing `click audit` the same way:

- `mdtests/struct_by_value_embedded_array_copy.md`
- `mdtests/struct_by_value_embedded_array_multidim_copy.md`

## Intended regression

Reduce `mdtests/struct_by_value_embedded_array_copy.md` to the smallest sidecar whose audit fails this way and add it as a retained expansion-audit case, so the fixture is expanded and re-verified by the gate rather than only verified. Do not change the fixture's C or weaken its proof to make the expansion pass.

## Acceptance criteria

- `click audit` passes for every fixture listed above, with no change to their C sources or contracts.
- The reduced case is audited by `scripts/check.sh`.
- The fix is in the expander, the smart tactic's certificate, or the checker, not a per-fixture special case; `scripts/check.sh` passes.
