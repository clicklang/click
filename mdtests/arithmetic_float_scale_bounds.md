# A rounded product inherits an ordered bound


```c filename=arithmetic.c
int32 half32(float x) { return (int32)(x * 0.5f); }
int32 half64(double x) { return (int32)(-0.5 * x); }
```

```click
verifying "arithmetic.c";

int32 half32(float x) {
    requires x >= float32_from_bits(0xc1200000);
    requires x <= float32_from_bits(0x41200000);
    ensures true;
}

int32 half64(double x) {
    requires x >= float64_from_bits(0xc024000000000000);
    requires x <= float64_from_bits(0x4024000000000000);
    ensures true;
}

theorem scale_bound(x: float) {
    requires x >= float32_from_bits(0xc1200000);
    ensures x * float32_from_bits(0x3f000000) >= float32_from_bits(0xc0a00000) by {
        apply(click::float_order::float32_scale_right_lower(
            float32_from_bits(0x3f000000), x, float32_from_bits(0xc1200000)
        ));
        close();
    }
}
```

```expect
pass
```
