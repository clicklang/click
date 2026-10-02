# Expansion refuses a witness that has no surface spelling

## Violated invariant

A smart tactic that verifies must expand to explicit tactics that verify the same claim: `click expand` output has to parse, re-verify in the retained session and through the direct targeted entry point, and contain no smart tactic at the audited site. `click audit` checks exactly this, and CLAUDE.md lists an expansion that fails or does not re-verify as a tooling defect that blocks feature work.

`simp` proves a goal by choosing a witness for a resource's existential field. The expander then stops: `the expansion needs a name for the witness ... which has no surface spelling`. The proof verifies but cannot be expanded at all.

The root cause has not been investigated. The fixtures below may not all share one; split this file if they do not.

## Reproduction

On `master` at `b3ab98334`, the fixture verifies (`MDTEST_FILTER=rb_parent_family cargo test --test mdtests`) and its audit fails:

```
click audit mdtests/rb_parent_family.md
```

fails at `mdtests/rb_parent_family.md:120:5` (`simp`) with:

```
the expansion needs a name for the witness `parent` of `linked`, which has no surface spelling
```

The gate does not audit fixtures, which is why these pass `scripts/check.sh`.

Affected fixtures (2), each failing `click audit` the same way:

- `mdtests/rb_parent_family.md`
- `mdtests/resource_witness_unfold_fold.md`

## Intended regression

Reduce `mdtests/rb_parent_family.md` to the smallest sidecar whose audit fails this way and add it as a retained expansion-audit case, so the fixture is expanded and re-verified by the gate rather than only verified. Do not change the fixture's C or weaken its proof to make the expansion pass.

## Acceptance criteria

- `click audit` passes for every fixture listed above, with no change to their C sources or contracts.
- The reduced case is audited by `scripts/check.sh`.
- The fix is in the expander, the smart tactic's certificate, or the checker, not a per-fixture special case; `scripts/check.sh` passes.
