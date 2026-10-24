# A match arm in an Integer comparison is exact

Each arm of a `match` is in the position the match is in, so when the
comparison reads as Integer its arms' machine arithmetic is exact: `x + 1`
is `to_integer(x) + 1`, greater than `a` for every `int32`, and the unsigned
`a + 1` at `UINT32_MAX` is `4294967296` rather than C's wrapped `0`. An `if`
is not yet such a position: the kernel has no Integer conditional, so a
conditional keeps its C value and is observed whole.

```click
spec enum Step {
    Next(int32),
    Stay(int32),
}

theorem a_signed_arm_does_not_overflow(a: int32) {
    ensures match Step::Next(a) {
        Step::Next(x) => x + 1,
        Step::Stay(x) => x,
    } > a by {
        normalize();
        simp();
    }
}

theorem an_unsigned_arm_does_not_wrap(a: uint32) {
    requires a == 4294967295u32;
    ensures match Step::Next(0) {
        Step::Next(x) => a + 1,
        Step::Stay(x) => a,
    } > a by {
        normalize();
        simp();
    }
}
```

```expect
pass
```
