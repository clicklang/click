# `solve` plans a narrow comparison through its operation identity

`let n: int8 = v + 1;` is the native `int8` sum, and a comparison of two
8- or 16-bit values is lowered natively at their format (rule K8), so
`to_integer(n) <= to_integer(u)` is the goal `int8 <=(v + 1i8, u)`. `solve`
reads it, as at 32 and 64 bits, through its Integer reading and the sum's
in-range identity `to_integer(n) == to_integer(v) + 1`, whose bounds follow
from `v < u`. The planner reads the narrow comparison through its `int32`
widenings, whose observations are the narrow ones the goal writes.

`solve_does_not_read_a_wrapping_narrow_operation_as_exact.md` is the
refused counterpart.

```click
theorem increment_upper_bound_int8(v: int8, u: int8) {
    requires v < u;
    let n: int8 = v + 1;
    ensures to_integer(n) <= to_integer(u);
}

theorem increment_strictly_increases_uint16(v: uint16, u: uint16) {
    requires v < u;
    let n: uint16 = v + 1;
    ensures to_integer(v) < to_integer(n);
}

theorem positive_predecessor_strictly_decreases_uint8(v: uint8) {
    requires 0 < v;
    let p: uint8 = v - 1;
    ensures to_integer(p) < to_integer(v);
}

theorem less_than_implies_positive_difference_uint8(v: uint8, u: uint8) {
    requires v < u;
    let d: uint8 = u - v;
    ensures 0 < to_integer(d);
}

theorem nonnegative_predecessor_upper_bound_int16(v: int16, b: int16) {
    requires 0 <= v;
    requires v <= b;
    let p: int16 = v - 1;
    ensures to_integer(p) <= to_integer(b);
}
```

```expect
pass
```
