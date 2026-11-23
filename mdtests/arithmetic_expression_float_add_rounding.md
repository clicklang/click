# Adding a float literal can round distinct inputs to the same endpoint

```click
theorem rounded(x: float) {
    requires x > float32_from_bits(0);
    ensures x + float32_from_bits(0x3f800000) > float32_from_bits(0x3f800000) by {
        normalize() using { x > float32_from_bits(0); };
    }
}
```

```expect
fail: did not normalize
```
