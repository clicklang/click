# Checked bounds for conversions and signed products

```c filename=return_cast.c
double return_cast(uint64 x) {
    return (double)x;
}
```

```click
verifying "return_cast.c";

double return_cast(uint64 x) {
    requires x <= 1024u64;
    ensures result <= float64_from_bits(0x4090000000000000u64);
}

theorem rounded_upper(x: uint64) {
    requires x <= 1024u64;
    ensures (x as float) <= float32_from_bits(0x44800000) by {
        close() using bounds { x <= 1024u64; };
    }
}

theorem rounded_strict_lower(x: int64) {
    requires x > -2i64;
    ensures (x as double) >= float64_from_bits(0xbff0000000000000u64) by {
        close() using bounds { x > -2i64; };
    }
}

theorem guarded_product(x: int32, y: int32) {
    requires y > 0;
    requires x <= 2147483647 / y;
    ensures to_integer(x) * to_integer(y) <= 2147483647 by {
        close() using bounds { y > 0; x <= 2147483647 / y; };
    }
}
```

```expect
pass
```
