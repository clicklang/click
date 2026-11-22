# A quotient using another divisor does not bound the product

```c filename=product.c
int32 product(int32 x, int32 y, int32 z) {
    if (x > 2147483647 / z) return 0;
    return x * y;
}
```

```click
verifying "product.c";

int32 product(int32 x, int32 y, int32 z) {
    requires x >= 0;
    requires y > 0;
    requires z > 0;
    ensures true;
}
```

```expect
fail: requires proof excluding signed overflow
```
