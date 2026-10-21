# `arithmetic()` does not bound the lower side of a non-strict premise below `INT32_MAX`

`i <= n` allows `i == n == 2147483647`, where `i + 1` overflows, so
`0 <= i; i <= n` does not show that the `int32` sum `i + 1` is nonnegative.
Its exact observation `to_integer(i + 1)` denotes a value only where `i + 1`
does not overflow, and the premises do not establish that, so the claim is
refused where it is stated. Written `0 <= i + 1`, the claim would compare
Integers, where it holds. The strict neighbour is
`mdtests/arithmetic_bounds_a_strict_lower_side_below_int32_max.md`.

```c filename=arithmetic_does_not_bound_a_non_strict_lower_side_below_int32_max.c
int32 next_index(int32 i, int32 n) {
    return 0;
}
```

```click
verifying "arithmetic_does_not_bound_a_non_strict_lower_side_below_int32_max.c";

theorem successor_nonnegative(i: int32, n: int32) {
    requires 0 <= i;
    requires i <= n;
    ensures 0 <= to_integer(i + 1) by {
        arithmetic() using { 0 <= i; i <= n; };
    }
}

int32 next_index(int32 i, int32 n) {
    ensures result == 0 by auto();
}
```

```expect
fail: not established: `i + 1` must not overflow
```
