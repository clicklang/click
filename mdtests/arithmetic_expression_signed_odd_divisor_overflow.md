# An odd divisor does not rule out signed overflow

```c filename=arithmetic.c
int32 divide(int32 x, int32 y) { return x / (y | 1); }
```

```click
verifying "arithmetic.c";

int32 divide(int32 x, int32 y) {
    requires x == -2147483648;
    requires y == -1;
    ensures true;
}
```

```expect
fail: INT_MIN / -1
```
