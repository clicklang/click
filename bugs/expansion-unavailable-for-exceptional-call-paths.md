# Expansion is unavailable where a call has an exceptional path

## Violated invariant

A smart tactic that verifies must expand to explicit tactics that verify the same claim: `click expand` output has to parse, re-verify in the retained session and through the direct targeted entry point, and contain no smart tactic at the audited site. `click audit` checks exactly this, and CLAUDE.md lists an expansion that fails or does not re-verify as a tooling defect that blocks feature work.

For a caller of a function with an exceptional outcome, expansion reports `surface/certificate path coverage diverged at p1: surface has 1 paths but frame certificate has 2`. `click expand` disagrees with the certificate the verifier accepted.

The root cause has not been investigated. The fixtures below may not all share one; split this file if they do not.

## Reproduction

On `master` at `b3ab98334`, the fixture verifies (`MDTEST_FILTER=exceptional_call_continuation cargo test --test mdtests`) and its audit fails:

```
click audit mdtests/exceptional_call_continuation.md
```

fails at `mdtests/exceptional_call_continuation.md:29:5` (`auto`) with:

```
proof expansion is unavailable for `caller`: surface/certificate path coverage diverged at p1: surface has 1 paths but frame certificate has 2
```

The gate does not audit fixtures, which is why these pass `scripts/check.sh`.

Affected fixtures (2), each failing `click audit` the same way:

- `mdtests/exceptional_call_continuation.md`
- `mdtests/exceptional_terminal_call.md`

## Intended regression

Reduce `mdtests/exceptional_call_continuation.md` to the smallest sidecar whose audit fails this way and add it as a retained expansion-audit case, so the fixture is expanded and re-verified by the gate rather than only verified. Do not change the fixture's C or weaken its proof to make the expansion pass.

## Acceptance criteria

- `click audit` passes for every fixture listed above, with no change to their C sources or contracts.
- The reduced case is audited by `scripts/check.sh`.
- The fix is in the expander, the smart tactic's certificate, or the checker, not a per-fixture special case; `scripts/check.sh` passes.
