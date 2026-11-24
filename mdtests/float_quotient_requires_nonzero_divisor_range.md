# Four quotient corners cannot justify a divisor range crossing zero

```click
theorem divisor_range_crosses_zero(y: float) {
    requires y >= float32_from_bits(0xbf800000);
    requires y <= float32_from_bits(0x3f800000);
    ensures float32_from_bits(0x3f800000) / y <= float32_from_bits(0x3f800000) by {
        apply(click::float_order::float32_quotient_upper(
            float32_from_bits(0x3f800000), y,
            float32_from_bits(0x3f800000), float32_from_bits(0xbf800000),
            float32_from_bits(0x3f800000), float32_from_bits(0x3f800000),
            float32_from_bits(0x3f800000)));
    }
}
```

```expect
fail: unproved obligation
```
