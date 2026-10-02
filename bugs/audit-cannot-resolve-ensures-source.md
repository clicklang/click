# `click audit` cannot resolve an `ensures` source it inventoried

## Violated invariant

A smart tactic that verifies must expand to explicit tactics that verify the same claim: `click expand` output has to parse, re-verify in the retained session and through the direct targeted entry point, and contain no smart tactic at the audited site. `click audit` checks exactly this, and CLAUDE.md lists an expansion that fails or does not re-verify as a tooling defect that blocks feature work.

The audit stops before checking any site: `could not resolve write_inner.ensures_2 source 0 ...: could not locate source ensure 2`. The inventory names a claim the source locator cannot find, so `click audit` disagrees with itself about the sidecar's claims.

The root cause has not been investigated. The fixtures below may not all share one; split this file if they do not.

## Reproduction

On `master` at `b3ab98334`, the fixture verifies (`MDTEST_FILTER=struct_aggregate_resources cargo test --test mdtests`) and its audit fails:

```
click audit mdtests/struct_aggregate_resources.md
```

fails with:

```
could not resolve write_inner.ensures_2 source 0 in `mdtests/struct_aggregate_resources.md`: could not locate source ensure 2
```

The gate does not audit fixtures, which is why these pass `scripts/check.sh`.

Affected fixtures (1), each failing `click audit` the same way:

- `mdtests/struct_aggregate_resources.md`

## Intended regression

Reduce `mdtests/struct_aggregate_resources.md` to the smallest sidecar whose audit fails this way and add it as a retained expansion-audit case, so the fixture is expanded and re-verified by the gate rather than only verified. Do not change the fixture's C or weaken its proof to make the expansion pass.

## Acceptance criteria

- `click audit` passes for every fixture listed above, with no change to their C sources or contracts.
- The reduced case is audited by `scripts/check.sh`.
- The fix is in the expander, the smart tactic's certificate, or the checker, not a per-fixture special case; `scripts/check.sh` passes.
