# Floating-point finiteness from bounds and exact operations

```c filename=arithmetic.c
int32 integer_cast(int64 x) { return (int32)((float)x * 0.0f); }
int32 widen_negation(float x) { return (int32)((double)(-x) * 0.0); }
int32 bounded_product(float x, float y) { return (int32)((x * y) * 0.0f); }
int32 bounded_sum(float x) { return (int32)((x + x) * 0.0f); }
```

```click
verifying "arithmetic.c";

int32 integer_cast(int64 x) { ensures true; }
int32 widen_negation(float x) { requires isfinite(x); ensures true; }
int32 bounded_product(float x, float y) {
    requires x >= float32_from_bits(0xbf800000);
    requires x <= float32_from_bits(0x3f800000);
    requires y >= float32_from_bits(0xbf800000);
    requires y <= float32_from_bits(0x3f800000);
    ensures true;
}
int32 bounded_sum(float x) {
    requires x >= float32_from_bits(0xbf800000);
    requires x <= float32_from_bits(0x3f800000);
    ensures true;
}

theorem finite_from_bounds(x: float) {
    requires x >= float32_from_bits(0xbf800000);
    requires x <= float32_from_bits(0x3f800000);
    ensures isfinite(x) by {
        apply(click::float_order::float32_finite_between(
            x, float32_from_bits(0xbf800000), float32_from_bits(0x3f800000)
        ));
    }
}
theorem finite_integer(x: int64) {
    ensures isfinite(x as float) by { close(); }
}
```

```expect
pass
```
