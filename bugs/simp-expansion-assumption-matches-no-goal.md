# Expanded `simp` emits an `assumption` that matches no goal

## Violated invariant

A smart tactic that verifies must expand to explicit tactics that verify the same claim: `click expand` output has to parse, re-verify in the retained session and through the direct targeted entry point, and contain no smart tactic at the audited site. `click audit` checks exactly this, and CLAUDE.md lists an expansion that fails or does not re-verify as a tooling defect that blocks feature work.

The expansion of `simp` ends in an `assumption` that finds no current proposition goal to match.

The root cause has not been investigated. The fixtures below may not all share one; split this file if they do not.

## Reproduction

On `master` at `b3ab98334`, the fixture verifies (`MDTEST_FILTER=cstr_stdlib cargo test --test mdtests`) and its audit fails:

```
click audit mdtests/cstr_stdlib.md
```

fails at `mdtests/cstr_stdlib.md:69:9` (`simp`) with:

```
`plain_cstr.exposes_ghost_length` path 0, tactic 5: `assumption` did not match any current proposition goal
```

The gate does not audit fixtures, which is why these pass `scripts/check.sh`.

Affected fixtures (2), each failing `click audit` the same way:

- `mdtests/cstr_stdlib.md`
- `mdtests/post_execution_intro_quantified_ensure.md`

## Intended regression

Reduce `mdtests/cstr_stdlib.md` to the smallest sidecar whose audit fails this way and add it as a retained expansion-audit case, so the fixture is expanded and re-verified by the gate rather than only verified. Do not change the fixture's C or weaken its proof to make the expansion pass.

## Acceptance criteria

- `click audit` passes for every fixture listed above, with no change to their C sources or contracts.
- The reduced case is audited by `scripts/check.sh`.
- The fix is in the expander, the smart tactic's certificate, or the checker, not a per-fixture special case; `scripts/check.sh` passes.
