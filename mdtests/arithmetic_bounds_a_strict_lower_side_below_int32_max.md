# `close() using` bounds the lower side of a strict premise below `INT32_MAX`

Arithmetic search expands to ordinary proof steps, with the selected premises
stated explicitly in `close() using { ... }`.

```c filename=arithmetic_bounds_a_strict_lower_side_below_int32_max.c
int32 next_index(int32 i, int32 n) {
    return 0;
}
```

```click
verifying "arithmetic_bounds_a_strict_lower_side_below_int32_max.c";

theorem successor_nonnegative(i: int32, n: int32) {
    requires 0 <= i;
    requires i < n;
    ensures 0 <= to_integer(i + 1) by {
        close() using { 0 <= i; i < n; };
    }
}

theorem successor_nonnegative_certificate(i: int32, n: int32) {
    requires 0 <= i;
    requires i < n;
    ensures 0 <= to_integer(i + 1) by {
        close() using { 0 <= i; i < n; };
    }
}

int32 next_index(int32 i, int32 n) {
    requires 0 <= i;
    requires i < n;
    ensures result == 0;
} by {
    have 0 <= to_integer(i + 1) by { close() using { 0 <= i; i < n; }; }
    step();
    solve();
}
```

```expect
pass
```
