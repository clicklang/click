# Expansion changes what a later C branch condition is decided from

## Violated invariant

A smart tactic that verifies must expand to explicit tactics that verify the same claim: `click expand` output has to parse, re-verify in the retained session and through the direct targeted entry point, and contain no smart tactic at the audited site. `click audit` checks exactly this, and CLAUDE.md lists an expansion that fails or does not re-verify as a tooling defect that blocks feature work.

After expansion, execution reaches a C `if` that the unexpanded proof decided and reports it undecided (`got 2 feasible condition paths`) or reports `focused outcome records both sides of the post-execution if condition`. The expanded prefix leaves a different fact set at the branch than the smart tactic did.

The root cause has not been investigated. The fixtures below may not all share one; split this file if they do not.

## Reproduction

On `master` at `b3ab98334`, the fixture verifies (`MDTEST_FILTER=a_bounded_argument_to_a_narrow_parameter_is_in_its_range cargo test --test mdtests`) and its audit fails:

```
click audit mdtests/a_bounded_argument_to_a_narrow_parameter_is_in_its_range.md
```

fails at `mdtests/a_bounded_argument_to_a_narrow_parameter_is_in_its_range.md:41:8` (`execute`) with:

```
`pass_checked.contract` tactic 1: `step` could not prove that the next C `if` condition `((0 <= y) && (y <= 255))` is one exact truth value; got 2 feasible condition paths
```

The gate does not audit fixtures, which is why these pass `scripts/check.sh`.

Affected fixtures (2), each failing `click audit` the same way:

- `mdtests/a_bounded_argument_to_a_narrow_parameter_is_in_its_range.md`
- `mdtests/a_condition_reaching_one_value_along_two_paths_splits_into_them.md`

## Intended regression

Reduce `mdtests/a_bounded_argument_to_a_narrow_parameter_is_in_its_range.md` to the smallest sidecar whose audit fails this way and add it as a retained expansion-audit case, so the fixture is expanded and re-verified by the gate rather than only verified. Do not change the fixture's C or weaken its proof to make the expansion pass.

## Acceptance criteria

- `click audit` passes for every fixture listed above, with no change to their C sources or contracts.
- The reduced case is audited by `scripts/check.sh`.
- The fix is in the expander, the smart tactic's certificate, or the checker, not a per-fixture special case; `scripts/check.sh` passes.
