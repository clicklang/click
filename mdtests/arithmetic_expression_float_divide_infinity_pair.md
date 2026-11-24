# Division can produce NaN if both operands can be infinite

```click
theorem unsafe_bound(x: float, y: float) {
    requires x >= float32_from_bits(0x3f800000);
    requires y >= float32_from_bits(0x3f800000);
    ensures x / y >= float32_from_bits(0) by {
        normalize() using { x >= float32_from_bits(0x3f800000); y >= float32_from_bits(0x3f800000); };
    }
}
```

```expect
fail: did not normalize
```
