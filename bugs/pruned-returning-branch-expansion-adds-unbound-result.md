# Whole-claim expansion adds outcome tactics to a pruned C branch

## Violated invariant

A verified proof must expand to a proof that verifies. A C branch excluded by
entry facts has no returning outcome and must not receive a sibling's
`result`-dependent closing tactics.

This reproduces without a loop, independently of the loop-return ownership
repair from PR #367.

## Reproduction

Save the following as a markdown proof fixture and run `click verify FILE.md`,
then `click expand --claim f.contract FILE.md`. Verification passes; expansion
fails with `could not lower have proposition` and `unbound variable result`.
The diagnostic lists the inconsistent branch facts `n <= 0` and `n == 5`.

```c filename=pruned.c
int32 f(int32 n) {
    if (n > 0) {
        return 5;
    }
    return 7;
}
```

```click
verifying "pruned.c";
int32 f(int32 n) {
    requires n == 5;
    ensures result == 5 or result == 7;
} by {
    branch then { step(); simp(); } else { step(); simp(); }
}
```

## Intended regression and acceptance

- Whole-claim expansion of this unchanged C and proof succeeds, and the
  generated proof cold reverifies without smart tactics.
- The unreachable arm is represented by checked refutation or omitted in a
  form the checker accepts; it receives no outcome tactics for a path that
  never returned.
- Retain coverage for the case where both arms are reachable, so neither a
  genuine return nor the continuing C tail is dropped.
