# Finite endpoints establish operand and square bounds

```click
theorem finite_between32(x: float) {
    requires x >= float32_from_bits(0xc0000000);
    requires x <= float32_from_bits(0x3f800000);
    ensures isfinite(x) by {
        apply(click::float_order::float32_finite_between(x, float32_from_bits(0xc0000000), float32_from_bits(0x3f800000)));
        close();
    }
}

theorem square_upper32(x: float) {
    requires x >= float32_from_bits(0xc0000000);
    requires x <= float32_from_bits(0x3f800000);
    ensures x * x <= float32_from_bits(0x40800000) by {
        apply(click::float_order::float32_square_interval(
            x, float32_from_bits(0xc0000000), float32_from_bits(0x3f800000), float32_from_bits(0x40800000)
        ));
        close();
    }
}

theorem finite_between64(x: double) {
    requires x >= float64_from_bits(0xc000000000000000u64);
    requires x <= float64_from_bits(0x3ff0000000000000u64);
    ensures isfinite(x) by {
        apply(click::float_order::float64_finite_between(x, float64_from_bits(0xc000000000000000u64), float64_from_bits(0x3ff0000000000000u64)));
        close();
    }
}

theorem square_upper64(x: double) {
    requires x >= float64_from_bits(0xc000000000000000u64);
    requires x <= float64_from_bits(0x3ff0000000000000u64);
    ensures x * x <= float64_from_bits(0x4010000000000000u64) by {
        apply(click::float_order::float64_square_interval(
            x, float64_from_bits(0xc000000000000000u64), float64_from_bits(0x3ff0000000000000u64), float64_from_bits(0x4010000000000000u64)
        ));
        close();
    }
}
```

```expect
pass
```
