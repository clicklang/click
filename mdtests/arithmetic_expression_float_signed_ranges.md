# Float products and quotients use finite endpoints on either side of zero

```c filename=arithmetic.c
int32 by_zero(float x) { return (int32)(x * 0.0f); }
int32 by_zero_bounded(float x) { return (int32)(x * 0.0f); }
int32 product(float x, float y) { return (int32)(x * y); }
int32 quotient(float x, float y) { return (int32)(x / y); }
```

```click
verifying "arithmetic.c";

int32 by_zero(float x) {
    requires isfinite(x);
    ensures true;
}
int32 by_zero_bounded(float x) {
    requires x >= float32_from_bits(0xbf800000);
    requires x <= float32_from_bits(0x3f800000);
    ensures true;
}
int32 product(float x, float y) {
    requires x >= float32_from_bits(0xbf800000);
    requires x <= float32_from_bits(0x3f800000);
    requires y >= float32_from_bits(0x3f800000);
    requires y <= float32_from_bits(0x40000000);
    ensures true;
}
int32 quotient(float x, float y) {
    requires x >= float32_from_bits(0x3f800000);
    requires x <= float32_from_bits(0x40000000);
    requires y >= float32_from_bits(0xc0000000);
    requires y <= float32_from_bits(0xbf800000);
    ensures true;
}
theorem finite_zero(x: float) {
    requires isfinite(x);
    ensures x * float32_from_bits(0) <= float32_from_bits(0) by {
        normalize() using { isfinite(x); };
    }
}
theorem negative_quotient(x: float, y: float) {
    requires x >= float32_from_bits(0x3f800000);
    requires x <= float32_from_bits(0x40000000);
    requires y >= float32_from_bits(0xc0000000);
    requires y <= float32_from_bits(0xbf800000);
    ensures x / y >= float32_from_bits(0xc0000000) by {
        normalize() using {
            y <= float32_from_bits(0xbf800000);
            x >= float32_from_bits(0x3f800000);
            y >= float32_from_bits(0xc0000000);
            x <= float32_from_bits(0x40000000);
        };
    }
}
```

```expect
pass
```
