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
        normalize() using {
            y >= float32_from_bits(0x3f800000);
            x >= float32_from_bits(0xbf800000);
        };
    }
}
theorem upper(x: double, y: double) {
    requires x <= float64_from_bits(0x3ff0000000000000u64);
    requires y <= float64_from_bits(0x4000000000000000u64);
    ensures x + y <= float64_from_bits(0x4008000000000000u64) by {
        solve();
    }
}

```

```expect
pass
```
