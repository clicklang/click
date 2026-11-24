# A zero product can be NaN when its other operand is infinite

```click
theorem infinite_input(x: float) {
    requires x >= float32_from_bits(0x3f800000);
    ensures x * float32_from_bits(0) <= float32_from_bits(0) by {
        normalize() using { x >= float32_from_bits(0x3f800000); };
    }
}
```

```expect
fail: did not normalize
```
