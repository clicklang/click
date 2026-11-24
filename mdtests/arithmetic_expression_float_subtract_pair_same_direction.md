# Two upper bounds can admit infinity minus infinity

```click
theorem undecided(x: float, y: float) {
    requires x <= float32_from_bits(0x40800000);
    requires y <= float32_from_bits(0x40000000);
    ensures x - y <= float32_from_bits(0x40000000) by {
        normalize() using { x <= float32_from_bits(0x40800000); y <= float32_from_bits(0x40000000); };
    }
}
```

```expect
fail: did not normalize
```
