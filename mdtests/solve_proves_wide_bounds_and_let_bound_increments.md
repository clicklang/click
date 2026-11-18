# solve proves wide equalities and let-bound increments

Two `solve` goals that the removed arithmetic-certificate fallback used to
close, kept here so the ordinary composition that replaced it covers them
in the gate (`width_uniformity.rs` checks every width nightly).

A 128-bit comparison is held as its Integer reading, and refutation proves
only `<=` goals, so `a == b` from its two bounds is composed directly. A
theorem `let` around an observation, `let n: int32 = v + 1;
to_integer(n)`, is already an Integer: it is neither observed again nor
cast whole to `int32`. The last theorem's bound allows `v == u`, so `v + 1`
may exceed `u`, and it is refused.

```click
theorem equal_from_bounds_int128(a: int128, b: int128) {
    requires a <= b;
    requires not (a < b);
    ensures a == b;
}

theorem equal_from_bounds_uint128(a: uint128, b: uint128) {
    requires a <= b;
    requires b <= a;
    ensures a == b;
}

theorem increment_below_bound_int32(v: int32, u: int32) {
    requires v < u;
    let n: int32 = v + 1;
    ensures to_integer(n) <= to_integer(u);
}

theorem increment_below_bound_int64(v: int64, u: int64) {
    requires v < u;
    let n: int64 = v + 1;
    ensures to_integer(n) <= to_integer(u);
}

theorem increment_from_weak_bound_int32(v: int32, u: int32) {
    requires v <= u;
    requires v < 2147483647;
    let n: int32 = v + 1;
    ensures to_integer(n) <= to_integer(u);
}
```

```expect
fail: increment_from_weak_bound_int32
```
