# `solve` does not read a wrapping narrow operation as exact

`let n: uint8 = v + 1;` is the native `uint8` sum, which wraps to `0` at
`v == 255`. With no bound on `v`, its in-range identity has no bounds, so
`to_integer(v) < to_integer(n)` is refused
(`solve_plans_a_narrow_comparison_through_its_operation_identity.md` bounds
`v` by `v < u`).

```click
theorem increment_may_wrap(v: uint8) {
    let n: uint8 = v + 1;
    ensures to_integer(v) < to_integer(n);
}
```

```expect
fail: could not establish `to_integer(v) < (let n: uint8 = v + 1; to_integer(n))`
```
