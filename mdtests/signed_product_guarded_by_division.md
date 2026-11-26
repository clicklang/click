# A checked quotient bounds a signed product

```c filename=product.c
int32 product32(int32 x, int32 y) {
    if (x > 2147483647 / y) return 0;
    return x * y;
}

int64 product64(int64 x, int64 y) {
    if (x > 9223372036854775807LL / y) return 0;
    return x * y;
}
```

```click
verifying "product.c";

int32 product32(int32 x, int32 y) {
    requires x >= 0;
    requires y > 0;
    ensures true;
}

int64 product64(int64 x, int64 y) {
    requires x >= 0i64;
    requires y > 0i64;
    ensures true;
}

theorem signed_quotient_observation(y: int32) {
    requires y > 0;
    ensures to_integer(2147483647 / y) == truncating_quotient(2147483647, to_integer(y)) by {
        have to_integer(y) != 0 by close();
        close();
    }
}
```

```expect
pass
```
