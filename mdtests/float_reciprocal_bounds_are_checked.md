# Signed reciprocal bounds with explicit divisor evidence

```click
theorem float32_negative_divisor_lower(y: float) {
    requires y <= float32_from_bits(0xbf800000);
    ensures float32_from_bits(0x3f800000) / y >= float32_from_bits(0xbf800000) by {
        have (float32_from_bits(0) < float32_from_bits(0xbf800000) and float32_from_bits(0xbf800000) <= y)
            or (float32_from_bits(0xbf800000) < float32_from_bits(0) and y <= float32_from_bits(0xbf800000)) by close();
        apply(click::float_order::float32_bounded_reciprocal_lower(float32_from_bits(0x3f800000), y, float32_from_bits(0xbf800000), float32_from_bits(0xbf800000)));
        close();
    }
}

theorem float32_negative_numerator_upper(y: float) {
    requires float32_from_bits(0x3f800000) <= y;
    ensures float32_from_bits(0xbf800000) / y <= float32_from_bits(0) by {
        have (float32_from_bits(0) < float32_from_bits(0x3f800000) and float32_from_bits(0x3f800000) <= y)
            or (float32_from_bits(0x3f800000) < float32_from_bits(0) and y <= float32_from_bits(0x3f800000)) by close();
        apply(click::float_order::float32_bounded_reciprocal_upper(float32_from_bits(0xbf800000), y, float32_from_bits(0x3f800000), float32_from_bits(0)));
        close();
    }
}

theorem float32_positive_minimum(y: float) {
    requires float32_from_bits(0x80000000) < y;
    ensures float32_from_bits(1) <= y by {
        apply(click::float_order::float32_strictly_positive_minimum(float32_from_bits(0x80000000), y));
        close();
    }
}

theorem float64_negative_divisor_lower(y: double) {
    requires y <= float64_from_bits(0xbff0000000000000u64);
    ensures float64_from_bits(0x3ff0000000000000u64) / y >= float64_from_bits(0xbff0000000000000u64) by {
        have (float64_from_bits(0u64) < float64_from_bits(0xbff0000000000000u64) and float64_from_bits(0xbff0000000000000u64) <= y)
            or (float64_from_bits(0xbff0000000000000u64) < float64_from_bits(0u64) and y <= float64_from_bits(0xbff0000000000000u64)) by close();
        apply(click::float_order::float64_bounded_reciprocal_lower(float64_from_bits(0x3ff0000000000000u64), y, float64_from_bits(0xbff0000000000000u64), float64_from_bits(0xbff0000000000000u64)));
        close();
    }
}

theorem float64_negative_numerator_upper(y: double) {
    requires float64_from_bits(0x3ff0000000000000u64) <= y;
    ensures float64_from_bits(0xbff0000000000000u64) / y <= float64_from_bits(0u64) by {
        have (float64_from_bits(0u64) < float64_from_bits(0x3ff0000000000000u64) and float64_from_bits(0x3ff0000000000000u64) <= y)
            or (float64_from_bits(0x3ff0000000000000u64) < float64_from_bits(0u64) and y <= float64_from_bits(0x3ff0000000000000u64)) by close();
        apply(click::float_order::float64_bounded_reciprocal_upper(float64_from_bits(0xbff0000000000000u64), y, float64_from_bits(0x3ff0000000000000u64), float64_from_bits(0u64)));
        close();
    }
}

theorem float64_positive_minimum(y: double) {
    requires float64_from_bits(0x8000000000000000u64) < y;
    ensures float64_from_bits(1u64) <= y by {
        apply(click::float_order::float64_strictly_positive_minimum(float64_from_bits(0x8000000000000000u64), y));
        close();
    }
}
```

```expect
pass
```
