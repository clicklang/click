# A maximum quotient guard admits a divisor of minus one

```c filename=arithmetic.c
int32 product(int32 x, int32 y) {
    return (y < 0 && x < 0 && x >= 2147483647 / y) ? x * y : 0;
}
```

```click
verifying "arithmetic.c";

int32 product(int32 x, int32 y) { ensures true; }

theorem upper(x: int32, y: int32) {
    requires x < 0;
    requires y < 0;
    requires x >= 2147483647 / y;
    ensures to_integer(x) * to_integer(y) <= 2147483647 by {
        normalize() using { x < 0; y < 0; x >= 2147483647 / y; };
    }
}
```

```expect
pass
```
