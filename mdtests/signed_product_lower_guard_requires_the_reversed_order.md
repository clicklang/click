# A lower product bound reverses the guard order for a negative divisor

```c filename=product.c
int32 product(int32 x, int32 y) {
    if (x < (-2147483647 - 1) / y) return 0;
    return x * y;
}
```

```click
verifying "product.c";

int32 product(int32 x, int32 y) {
    requires x >= 0;
    requires y < -1;
    ensures true;
}
```

```expect
fail: requires proof excluding signed overflow
```
