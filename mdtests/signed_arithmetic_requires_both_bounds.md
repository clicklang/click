# Signed increment and decrement need both overflow bounds

`x + 1` needs `x < 2147483647` and `x - 1` needs `x > -2147483648`; with both
requirements the function verifies.

```c filename=signed_arithmetic_requires_both_bounds.c
int32 step_both(int32 x) {
    int32 up;
    int32 down;
    up = x + 1;
    down = x - 1;
    return down;
}
```

```click
verifying "signed_arithmetic_requires_both_bounds.c";

int32 step_both(int32 x) {
    requires x < 2147483647;
    requires x > -2147483648;
    ensures result == x - 1 by auto();
}
```

```expect
pass
```
