# A checked quotient bounds a signed product from below

```c filename=product.c
int32 positive_divisor32(int32 x, int32 y) {
    if (x < (-2147483647 - 1) / y) return 0;
    return x * y;
}

int64 positive_divisor64(int64 x, int64 y) {
    if (x < (-9223372036854775807LL - 1) / y) return 0;
    return y * x;
}

int32 negative_divisor32(int32 x, int32 y) {
    if (x > (-2147483647 - 1) / y) return 0;
    return x * y;
}

int64 negative_divisor64(int64 x, int64 y) {
    if (x > (-9223372036854775807LL - 1) / y) return 0;
    return y * x;
}
```

```click
verifying "product.c";

int32 positive_divisor32(int32 x, int32 y) {
    requires x <= 0;
    requires y > 0;
    ensures true;
}

int64 positive_divisor64(int64 x, int64 y) {
    requires x <= 0i64;
    requires y > 0i64;
    ensures true;
}

int32 negative_divisor32(int32 x, int32 y) {
    requires x >= 0;
    requires y < -1;
    ensures true;
}

int64 negative_divisor64(int64 x, int64 y) {
    requires x >= 0i64;
    requires y < -1i64;
    ensures true;
}
```

```expect
pass
```
