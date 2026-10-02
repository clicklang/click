# Expanded proofs about file-scope and static objects do not re-verify

## Violated invariant

A smart tactic that verifies must expand to explicit tactics that verify the same claim: `click expand` output has to parse, re-verify in the retained session and through the direct targeted entry point, and contain no smart tactic at the audited site. `click audit` checks exactly this, and CLAUDE.md lists an expansion that fails or does not re-verify as a tooling defect that blocks feature work.

The expansion emits a `have` whose body cannot be checked. In three file-scope fixtures a `rewrite` names an equality (`load(&entries) == 6`) that is not an exact available fact; in two a `normalize` inside the `have` body does not reach true.

The root cause has not been investigated. The fixtures below may not all share one; split this file if they do not.

## Reproduction

On `master` at `b3ab98334`, the fixture verifies (`MDTEST_FILTER=data_only_translation_unit cargo test --test mdtests`) and its audit fails:

```
click audit mdtests/data_only_translation_unit.md
```

fails at `mdtests/data_only_translation_unit.md:28:29` (`auto`) with:

```
`read.ensures_1` proof step tactic 1 > have body tactic 5: `rewrite` requires its equality to be an exact available fact
```

The gate does not audit fixtures, which is why these pass `scripts/check.sh`.

Affected fixtures (5), each failing `click audit` the same way:

- `mdtests/data_only_translation_unit.md`
- `mdtests/file_scope_incomplete_extern_arrays.md`
- `mdtests/file_scope_tentative_aggregates.md`
- `mdtests/designated_aggregate_static_objects.md`
- `mdtests/struct_array_parameter_fields.md`

## Intended regression

Reduce `mdtests/data_only_translation_unit.md` to the smallest sidecar whose audit fails this way and add it as a retained expansion-audit case, so the fixture is expanded and re-verified by the gate rather than only verified. Do not change the fixture's C or weaken its proof to make the expansion pass.

## Acceptance criteria

- `click audit` passes for every fixture listed above, with no change to their C sources or contracts.
- The reduced case is audited by `scripts/check.sh`.
- The fix is in the expander, the smart tactic's certificate, or the checker, not a per-fixture special case; `scripts/check.sh` passes.
