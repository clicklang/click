# A modular automatic-storage pointer return loses its ended lifetime

Priority: P1.

Soundness: unsound. A caller can compare a pointer returned into a callee's
ended automatic object. C11 6.2.4p2 makes the pointer indeterminate when that
object's lifetime ends; this is a use of the indeterminate pointer, beyond
merely copying its representation.

Reproduced on the scalar-member worktree after merging `0486bf816`, without
needing a member selector or memory permission. The return abstraction keeps
neither the automatic object's identity nor its ended lifetime. Rejecting
nonzero arithmetic and accesses on an unknown return does not reject this
comparison.

## Reproduction

```c filename=probe.c
int32* leak(void) { int32 value; return &value; }
int32 probe(int32* p) {
    int32* q = leak();
    if (q == p) return 1;
    return 0;
}
```

```click
verifying "probe.c";
int32* leak() { ensures result == result; } by { execute(); simp(); }
int32 probe(int32* p) {
    ensures result == 0 or result == 1;
} by { execute(); simp(); }
```

Ordinary verification accepts both claims. The caller's defined-behavior claim
must be rejected at the comparison.

## Acceptance

Preserve ended-local identity through checked modular pointer returns and
value copies; reject comparisons, pointer truth tests, conversions and accesses
that use that indeterminate pointer. Preserve supported representation copies
and overwrites, and valid returns of pointers into caller-owned objects,
static storage and live heap allocations. Include expanded and retained
checks. A scalar-member return must not export a live selected domain for
callee automatic storage.
