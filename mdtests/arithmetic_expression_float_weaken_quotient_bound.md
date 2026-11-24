# Solve can weaken a bound on the same quotient

```click quick-solve
theorem probe(y: float) {
    requires float32_from_bits(0x3f800000) / y <= float32_from_bits(0x3f800000);
    ensures float32_from_bits(0x3f800000) / y < float32_from_bits(0x4f000000) by { solve(); }
}
theorem strict_upper(y: float) {
    requires float32_from_bits(0x3f800000) / y < float32_from_bits(0x3f800000);
    ensures float32_from_bits(0x3f800000) / y <= float32_from_bits(0x3f800000) by {
        apply(click::float_order::float32_lt_to_le(
            float32_from_bits(0x3f800000) / y, float32_from_bits(0x3f800000)
        ));
    }
}

theorem strict_lower64(y: double) {
    requires float64_from_bits(0x3ff0000000000000u64) <
        float64_from_bits(0x3ff0000000000000u64) / y;
    ensures float64_from_bits(0x3ff0000000000000u64) <=
        float64_from_bits(0x3ff0000000000000u64) / y by {
        apply(click::float_order::float64_lt_to_le(
            float64_from_bits(0x3ff0000000000000u64), float64_from_bits(0x3ff0000000000000u64) / y
        ));
    }
}

```

```expect
pass
```
