# Floating-point interval proofs from strict operand bounds

```c filename=product.c
int32 product_cast(double x, double y) {
    return (int32)(x * y);
}
```

```click
verifying "product.c";

int32 product_cast(double x, double y) {
    requires x > float64_from_bits(0xc000000000000000u64);
    requires x < float64_from_bits(0x4000000000000000u64);
    requires y > float64_from_bits(0xc008000000000000u64);
    requires y < float64_from_bits(0x4008000000000000u64);
    ensures true;
}

theorem square(x: double) {
    requires x > float64_from_bits(0x3ff0000000000000u64);
    requires x < float64_from_bits(0x4000000000000000u64);
    ensures x * x < float64_from_bits(0x4010000000000000u64) by close();
}

theorem positive_product(x: double, y: double) {
    requires x > float64_from_bits(0x3ff0000000000000u64);
    requires y > float64_from_bits(0x3ff0000000000000u64);
    ensures x * y > float64_from_bits(0x3ff0000000000000u64) by close();
}

theorem mixed_product(x: float, y: float) {
    requires x > float32_from_bits(0xc0000000);
    requires x < float32_from_bits(0x40000000);
    requires y >= float32_from_bits(0xc0400000);
    requires y < float32_from_bits(0x40400000);
    ensures x * y <= float32_from_bits(0x40c00000) by close();
}

theorem positive_quotient(x: double, y: double) {
    requires x > float64_from_bits(0x4000000000000000u64);
    requires x < float64_from_bits(0x4020000000000000u64);
    requires y > float64_from_bits(0x3ff0000000000000u64);
    requires y < float64_from_bits(0x4000000000000000u64);
    ensures x / y < float64_from_bits(0x4020000000000000u64) by close();
}

theorem negative_quotient(x: float, y: float) {
    requires x > float32_from_bits(0x40000000);
    requires x < float32_from_bits(0x41000000);
    requires y > float32_from_bits(0xc0000000);
    requires y < float32_from_bits(0xbf800000);
    ensures x / y > float32_from_bits(0xc1000000) by close();
}

theorem zero_product(x: float) {
    requires x > float32_from_bits(0xbf800000);
    requires x < float32_from_bits(0x3f800000);
    ensures x * float32_from_bits(0) >= float32_from_bits(0) by close();
}
```

```expect
pass
```
