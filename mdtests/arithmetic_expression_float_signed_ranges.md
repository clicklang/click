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
        close() using { isfinite(x); };
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
theorem product_lower32(x: float, y: float) {
    requires x >= float32_from_bits(0xbf800000);
    requires y >= float32_from_bits(0x3f800000);
    requires x <= float32_from_bits(0x3f800000);
    requires y <= float32_from_bits(0x40000000);
    ensures x * y >= float32_from_bits(0xc0000000) by {
        apply(click::float_order::float32_product_lower(
            x, y, float32_from_bits(0xbf800000), float32_from_bits(0x3f800000),
            float32_from_bits(0x3f800000), float32_from_bits(0x40000000), float32_from_bits(0xc0000000)
        ));
        close();
    }
}

theorem product_upper32(x: float, y: float) {
    requires x >= float32_from_bits(0xbf800000);
    requires y >= float32_from_bits(0x3f800000);
    requires x <= float32_from_bits(0x3f800000);
    requires y <= float32_from_bits(0x40000000);
    ensures x * y <= float32_from_bits(0x40000000) by {
        apply(click::float_order::float32_product_upper(
            x, y, float32_from_bits(0xbf800000), float32_from_bits(0x3f800000),
            float32_from_bits(0x3f800000), float32_from_bits(0x40000000), float32_from_bits(0x40000000)
        ));
        close();
    }
}

theorem product_lower64(x: double, y: double) {
    requires x >= float64_from_bits(0xbff0000000000000u64);
    requires y >= float64_from_bits(0x3ff0000000000000u64);
    requires x <= float64_from_bits(0x3ff0000000000000u64);
    requires y <= float64_from_bits(0x4000000000000000u64);
    ensures x * y >= float64_from_bits(0xc000000000000000u64) by {
        apply(click::float_order::float64_product_lower(
            x, y, float64_from_bits(0xbff0000000000000u64), float64_from_bits(0x3ff0000000000000u64),
            float64_from_bits(0x3ff0000000000000u64), float64_from_bits(0x4000000000000000u64), float64_from_bits(0xc000000000000000u64)
        ));
        close();
    }
}

theorem product_upper64(x: double, y: double) {
    requires x >= float64_from_bits(0xbff0000000000000u64);
    requires y >= float64_from_bits(0x3ff0000000000000u64);
    requires x <= float64_from_bits(0x3ff0000000000000u64);
    requires y <= float64_from_bits(0x4000000000000000u64);
    ensures x * y <= float64_from_bits(0x4000000000000000u64) by {
        apply(click::float_order::float64_product_upper(
            x, y, float64_from_bits(0xbff0000000000000u64), float64_from_bits(0x3ff0000000000000u64),
            float64_from_bits(0x3ff0000000000000u64), float64_from_bits(0x4000000000000000u64), float64_from_bits(0x4000000000000000u64)
        ));
        close();
    }
}

```

```expect
pass
```
