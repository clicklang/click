# `branch` refuses a condition prerequisite it cannot decide

A non-constant `double` cast to `int32` in a C condition owes the cast's range,
starting with `isfinite(d)`. `branch` checks each such prerequisite by exact
lookup or by the kernel's condition decision, without searching the proof
context. Nothing here states `isfinite(d)`, so the `branch` is refused at it.
A `requires` or `have` that states the range before the `branch` lets it split
(`bugs/branch-float-cast-prerequisite-prints-unnamed-and-raw-bits.md` tracks
how the refusal spells the fact).

```c filename=branch_float_cast_prerequisite.c
int32 positive(double d) {
    if ((int32) d > 0) {
        return 1;
    }
    return 0;
}
```

```click
verifying "branch_float_cast_prerequisite.c";

int32 positive(double d) {
    ensures result >= 0;
} by {
    branch then { step(); simp(); } else {}
    step();
    simp();
}
```

```expect
fail: `branch` is missing condition prerequisite
```
