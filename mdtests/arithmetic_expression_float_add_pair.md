# Bounds on both operands establish a float sum bound

```c filename=arithmetic.c
int32 sum(float x, float y) { return (int32)(x + y); }
```

```click
verifying "arithmetic.c";

int32 sum(float x, float y) {
    requires x >= float32_from_bits(0xbf800000);
    requires x <= float32_from_bits(0x3f800000);
    requires y >= float32_from_bits(0x3f800000);
    requires y <= float32_from_bits(0x40000000);
    ensures true;
}

theorem low(x: float, y: float) {
    requires x >= float32_from_bits(0xbf800000);
    requires y >= float32_from_bits(0x3f800000);
    ensures x + y >= float32_from_bits(0) by {
        apply(click::float_order::float32_add_lower(
            x, y, float32_from_bits(0xbf800000), float32_from_bits(0x3f800000)
        ));
        known();
    }
}
theorem upper(x: double, y: double) {
    requires x <= float64_from_bits(0x3ff0000000000000u64);
    requires y <= float64_from_bits(0x4000000000000000u64);
    ensures x + y <= float64_from_bits(0x4008000000000000u64) by {
        apply(click::float_order::float64_add_upper(
            x, y, float64_from_bits(0x3ff0000000000000u64), float64_from_bits(0x4000000000000000u64)
        ));
        known();
    }
}

theorem upper32(x: float, y: float) {
    requires x <= float32_from_bits(0x3f800000);
    requires y <= float32_from_bits(0x40000000);
    ensures x + y <= float32_from_bits(0x40400000) by {
        apply(click::float_order::float32_add_upper(
            x, y, float32_from_bits(0x3f800000), float32_from_bits(0x40000000)
        ));
        known();
    }
}

theorem lower64(x: double, y: double) {
    requires x >= float64_from_bits(0xbff0000000000000u64);
    requires y >= float64_from_bits(0x3ff0000000000000u64);
    ensures x + y >= float64_from_bits(0u64) by {
        apply(click::float_order::float64_add_lower(
            x, y, float64_from_bits(0xbff0000000000000u64), float64_from_bits(0x3ff0000000000000u64)
        ));
        known();
    }
}
```

```expect
pass
```
