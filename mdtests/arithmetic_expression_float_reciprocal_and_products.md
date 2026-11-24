# Ordered positive operand bounds support floating-point cast safety

```c filename=arithmetic.c
int32 reciprocal(float y) { return (int32)(1.0f / y); }
int32 multiply(float x, float y) { return (int32)(x * y); }
int32 divide(float x, float y) { return (int32)(x / y); }
```

```click
verifying "arithmetic.c";

int32 reciprocal(float y) {
    requires y >= float32_from_bits(0x3f800000);
    ensures true;
}
int32 multiply(float x, float y) {
    requires x >= float32_from_bits(0x3f800000);
    requires x <= float32_from_bits(0x40000000);
    requires y >= float32_from_bits(0x3f800000);
    requires y <= float32_from_bits(0x40000000);
    ensures true;
}
int32 divide(float x, float y) {
    requires x >= float32_from_bits(0x3f800000);
    requires x <= float32_from_bits(0x40000000);
    requires y >= float32_from_bits(0x3f800000);
    requires y <= float32_from_bits(0x40000000);
    ensures true;
}

theorem reciprocal_upper(y: float) {
    requires y >= float32_from_bits(0x3f800000);
    ensures float32_from_bits(0x3f800000) / y <= float32_from_bits(0x3f800000) by {
        normalize() using { y >= float32_from_bits(0x3f800000); };
    }
}

theorem multiply_lower(x: float, y: float) {
    requires x >= float32_from_bits(0x3f800000);
    requires y >= float32_from_bits(0x3f800000);
    ensures x * y >= float32_from_bits(0x3f800000) by {
        apply(click::float_order::float32_positive_product_lower(
            x, y, float32_from_bits(0x3f800000), float32_from_bits(0x3f800000)
        ));
        known();
    }
}
theorem multiply_lower64(x: double, y: double) {
    requires x >= float64_from_bits(0x3ff0000000000000u64);
    requires y >= float64_from_bits(0x3ff0000000000000u64);
    ensures x * y >= float64_from_bits(0x3ff0000000000000u64) by {
        apply(click::float_order::float64_positive_product_lower(
            x, y, float64_from_bits(0x3ff0000000000000u64), float64_from_bits(0x3ff0000000000000u64)
        ));
        known();
    }
}

```

```expect
pass
```
