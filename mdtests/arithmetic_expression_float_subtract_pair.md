# Opposite operand bounds establish a float difference bound

```c filename=arithmetic.c
int32 cast_difference(float x, float y) { return (int32)(x - y); }
```

```click
verifying "arithmetic.c";

int32 cast_difference(float x, float y) {
    requires x >= float32_from_bits(0xbf800000);
    requires x <= float32_from_bits(0x3f800000);
    requires y >= float32_from_bits(0x3f800000);
    requires y <= float32_from_bits(0x40000000);
    ensures true;
}

theorem upper(x: double, y: double) {
    requires x <= float64_from_bits(0x4010000000000000u64);
    requires y >= float64_from_bits(0x3ff0000000000000u64);
    requires y >= float64_from_bits(0x4000000000000000u64);
    ensures x - y <= float64_from_bits(0x4000000000000000u64) by { close(); }
}

theorem lower(x: float, y: float) {
    requires x >= float32_from_bits(0x40800000);
    requires y <= float32_from_bits(0x40000000);
    ensures x - y >= float32_from_bits(0x40000000) by {
        apply(click::float_order::float32_sub_lower(
            x, y, float32_from_bits(0x40800000), float32_from_bits(0x40000000)
        ));
        close();
    }
}

theorem lower64(x: double, y: double) {
    requires x >= float64_from_bits(0x4010000000000000u64);
    requires y <= float64_from_bits(0x4000000000000000u64);
    ensures x - y >= float64_from_bits(0x4000000000000000u64) by {
        apply(click::float_order::float64_sub_lower(
            x, y, float64_from_bits(0x4010000000000000u64), float64_from_bits(0x4000000000000000u64)
        ));
        close();
    }
}

theorem upper64(x: double, y: double) {
    requires x <= float64_from_bits(0x4010000000000000u64);
    requires y >= float64_from_bits(0x4000000000000000u64);
    ensures x - y <= float64_from_bits(0x4000000000000000u64) by {
        apply(click::float_order::float64_sub_upper(
            x, y, float64_from_bits(0x4010000000000000u64), float64_from_bits(0x4000000000000000u64)
        ));
        close();
    }
}
```

```expect
pass
```
