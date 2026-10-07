# A path-dependent post-execution have expands to a proof that does not verify

## Violated invariant

A verified `have` must expand to explicit tactics that establish the same fact
on every execution path and preserve it for the subsequent proof. Replaying an
earlier loop's branch skeleton at function exit does not provide this guarantee.

This is a separate remaining case from the former combined path-dependent
expansion report, rather than the trailing claim-closer or shared-invariant case.

## Reproduction

On `master` at `4bc08bee6`, verification passes, but:

```sh
click audit mdtests/bubble_sort3_loop_sorted.md
```

fails at line 258, `have p[0] <= p[1] by simp;`. The rewrite reports a
proof-level `if` unsupported in the execution context. Both smart sites in this
claim are post-execution `have` statements. Keep the fixture's C and contract
unchanged.

Merely moving the first `have` into the original execution leaves is
insufficient: the independently checked rewrite then fails on path 4 at the
later `have p[1] <= p[2] by simp;` because its search does not retain a complete
proof. The rewrite must preserve the facts and outcome context the suffix uses.

## Intended regression

Expand each smart `have`, independently verify the rewrite and its unselected
suffix, and confirm the established comparison remains available. Use bounded
shared-engine checks rather than adding a whole-fixture CLI audit to the gate.

## Acceptance criteria

- Both sites in `mdtests/bubble_sort3_loop_sorted.md` audit successfully.
- Each rewritten `have` preserves the proof context needed by later tactics.
- The fix is generic capture/checker work; `scripts/check.sh` passes.
