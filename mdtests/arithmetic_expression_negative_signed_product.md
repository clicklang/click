# A quotient guard bounds the product of two negative operands

```c filename=arithmetic.c
int32 product(int32 x, int32 y) {
    return (y < -1 && x < 0 && x >= 2147483647 / y) ? x * y : 0;
}
```

```click
verifying "arithmetic.c";

int32 product(int32 x, int32 y) { ensures true; }

theorem upper(x: int32, y: int32) {
    requires x < 0;
    requires y < -1;
    requires x >= 2147483647 / y;
    ensures to_integer(x) * to_integer(y) <= 2147483647 by close();
}
```

```expect
pass
```
