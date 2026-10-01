# A proof `if` nested in a branch arm reports "not implemented"

## Violated invariant

A refusal must name the real failure. This proof (true `ensures u == u`) is
refused with "the proof script is valid, but the verifier cannot yet certify
it … reached tactic 3 (proof-level `if`), which is not implemented in this
execution context", which hides what actually failed:

```c
int32 f(int32 u, int32 v) {
    int32 r; int32* buf;
    buf = malloc(16);
    if (buf == 0) { return 0; }
    buf[0] = 3; buf[u] = 7; buf[v] = 9;
    r = buf[0];
    free(buf);
    return r;
}
```

```click
int32 f(int32 u, int32 v) {
    requires 0 <= u; requires u < 4; requires 0 <= v; requires v < 4;
    ensures u == u;
} by {
    step(); step(); step();
    if buf == 0 { execute(); simp(); }
    else { step(); step(); step(); step(); execute(); simp(); }
}
```

PR #53 fixed nested proof `if`s inside *expanded* branch arms; check whether
this shape still fails on master first.

## Intended regression

The mdtest above verifies, and a variant with a false `ensures` is refused with
an ordinary unclosed goal naming its case.

## Acceptance criteria

- Proof-level `if` works inside a proof-level `if` arm that also contains C
  steps, for heap programs with symbolic stores.
- Where some proof shape genuinely isn't supported, the refusal names the
  actual unsupported construct and the reason, not a generic
  "not implemented in this execution context".
