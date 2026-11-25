# Bounds from a positive divisor guard both signs of a product

```c filename=arithmetic.c
int32 product(int32 x, int32 y) {
    if (y < 2) return 0;
    if (x > 2147483647 / y) return 0;
    if (x < (-2147483647 - 1) / y) return 0;
    return x * y;
}
int64 reversed(int64 x, int64 y) {
    if (y <= 0) return 0;
    if (x > 9223372036854775807LL / y) return 0;
    if (x < (-9223372036854775807LL - 1) / y) return 0;
    return y * x;
}
```

```click
verifying "arithmetic.c";

int32 product(int32 x, int32 y) { ensures true; }
int64 reversed(int64 x, int64 y) { ensures true; }

theorem upper(x: int32, y: int32) {
    requires y > 0;
    requires x <= 2147483647 / y;
    ensures to_integer(x) * to_integer(y) <= 2147483647 by {
        normalize() using { y > 0; x <= 2147483647 / y; };
    }
}
theorem lower(x: int32, y: int32) {
    requires y > 0;
    requires x >= (-2147483647 - 1) / y;
    ensures to_integer(x) * to_integer(y) >= -2147483648 by {
        normalize() using { y > 0; x >= (-2147483647 - 1) / y; };
    }
}
```

```expect
pass
```
