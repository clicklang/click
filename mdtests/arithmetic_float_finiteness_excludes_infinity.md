# Non-strict infinity endpoints do not establish finiteness

```click
theorem finite(x: float) {
    requires x >= float32_from_bits(0xbf800000);
    requires x <= float32_from_bits(0x7f800000);
    ensures isfinite(x) by {
        normalize() using {
            x >= float32_from_bits(0xbf800000);
            x <= float32_from_bits(0x7f800000);
        };
    }
}
```

```expect
fail: goal did not normalize to true using the listed conditions
```
