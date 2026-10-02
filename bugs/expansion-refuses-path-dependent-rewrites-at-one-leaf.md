# Expansion refuses a tactic whose rewrite differs by execution path or obligation

## Violated invariant

A smart tactic that verifies must expand to explicit tactics that verify the same claim: `click expand` output has to parse, re-verify in the retained session and through the direct targeted entry point, and contain no smart tactic at the audited site. `click audit` checks exactly this, and CLAUDE.md lists an expansion that fails or does not re-verify as a tooling defect that blocks feature work.

One written tactic is checked on several execution paths or proof obligations, and its expansion differs between them. The expander gives up with one of three messages: `two execution paths require different tactic expansions at one surface leaf`, `a path-independent tactic expansion conflicts with a leaf's existing expansion`, or `selected tactic expands differently across proof obligations`. The proofs verify but cannot be expanded.

The root cause has not been investigated. The fixtures below may not all share one; split this file if they do not.

## Reproduction

On `master` at `b3ab98334`, the fixture verifies (`MDTEST_FILTER=bubble_sort3_loop_permutation cargo test --test mdtests`) and its audit fails:

```
click audit mdtests/bubble_sort3_loop_permutation.md
```

fails at `mdtests/bubble_sort3_loop_permutation.md:245:9` (`simp`) with:

```
could not expand selected tactic: two execution paths require different tactic expansions at one surface leaf
```

The gate does not audit fixtures, which is why these pass `scripts/check.sh`.

Affected fixtures (4), each failing `click audit` the same way:

- `mdtests/bubble_sort3_loop_permutation.md`
- `mdtests/cpp_one_guard_unwind.md`
- `mdtests/bubble_sort3_loop_sorted.md`
- `mdtests/c_decreases_recursive_in_loop.md`

## Intended regression

Reduce `mdtests/bubble_sort3_loop_permutation.md` to the smallest sidecar whose audit fails this way and add it as a retained expansion-audit case, so the fixture is expanded and re-verified by the gate rather than only verified. Do not change the fixture's C or weaken its proof to make the expansion pass.

## Acceptance criteria

- `click audit` passes for every fixture listed above, with no change to their C sources or contracts.
- The reduced case is audited by `scripts/check.sh`.
- The fix is in the expander, the smart tactic's certificate, or the checker, not a per-fixture special case; `scripts/check.sh` passes.
