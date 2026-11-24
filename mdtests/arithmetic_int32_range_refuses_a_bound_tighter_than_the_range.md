# `int32_range` refuses a bound tighter than the `int32` range

`int32_range` states one term's own `int32` range, `n <= 2147483647`, which
holds of every `n`. `n <= 2147483646` is false at `n == 2147483647`, so the
kernel refuses it as an `int32_range` step; accepted, it would let `i <= n`
bound `i` by `2147483645` and prove the false `0 <= i + 1` over
`i == n == 2147483647` once `i < n` is weakened to `i <= n`. The true step is
in `mdtests/arithmetic_bounds_a_strict_lower_side_below_int32_max.md`.

```c filename=arithmetic_int32_range_refuses_a_bound_tighter_than_the_range.c
int32 next_index(int32 i, int32 n) {
    return 0;
}
```

```click
verifying "arithmetic_int32_range_refuses_a_bound_tighter_than_the_range.c";

theorem successor_nonnegative(i: int32, n: int32) {
    requires 0 <= i;
    requires i <= n;
    requires defined(i + 1);
    ensures 0 <= to_integer(i + 1) by {
        close() using { 0 <= i; i <= n; };
    }
}

int32 next_index(int32 i, int32 n) {
    ensures result == 0;
}
```

```expect
fail: `close() using`
```
