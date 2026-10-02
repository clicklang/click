# Expanded sidecar prints a multidimensional array field with too few indices

## Violated invariant

A smart tactic that verifies must expand to explicit tactics that verify the same claim: `click expand` output has to parse, re-verify in the retained session and through the direct targeted entry point, and contain no smart tactic at the audited site. `click audit` checks exactly this, and CLAUDE.md lists an expansion that fails or does not re-verify as a tooling defect that blocks feature work.

The rewritten sidecar does not parse: `multidimensional scalar array field requires 2 indices, got 1`. The expander's printer drops an index when it spells an element of a multidimensional array member.

The root cause has not been investigated. The fixtures below may not all share one; split this file if they do not.

## Reproduction

On `master` at `b3ab98334`, the fixture verifies (`MDTEST_FILTER=struct_multidimensional_scalar_array cargo test --test mdtests`) and its audit fails:

```
click audit mdtests/struct_multidimensional_scalar_array.md
```

fails at `mdtests/struct_multidimensional_scalar_array.md:93:6` (`auto`) with:

```
could not locate `finish.contract` in the rewritten sidecar: line 31, column 40: multidimensional scalar array field requires 2 indices, got 1
```

The gate does not audit fixtures, which is why these pass `scripts/check.sh`.

Affected fixtures (2), each failing `click audit` the same way:

- `mdtests/struct_multidimensional_scalar_array.md`
- `mdtests/struct_wide_integer_arrays.md`

## Intended regression

Reduce `mdtests/struct_multidimensional_scalar_array.md` to the smallest sidecar whose audit fails this way and add it as a retained expansion-audit case, so the fixture is expanded and re-verified by the gate rather than only verified. Do not change the fixture's C or weaken its proof to make the expansion pass.

## Acceptance criteria

- `click audit` passes for every fixture listed above, with no change to their C sources or contracts.
- The reduced case is audited by `scripts/check.sh`.
- The fix is in the expander, the smart tactic's certificate, or the checker, not a per-fixture special case; `scripts/check.sh` passes.
