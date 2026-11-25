# An upper quotient guard does not prevent underflow

```c filename=arithmetic.c
int32 product(int32 x, int32 y) {
    if (y < 2) return 0;
    if (x > 2147483647 / y) return 0;
    return x * y;
}
```

```click
verifying "arithmetic.c";

int32 product(int32 x, int32 y) { ensures true; }
```

```expect
fail: requires proof excluding signed overflow
```
