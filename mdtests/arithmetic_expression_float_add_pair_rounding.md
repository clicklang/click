# A strict operand bound can round to the endpoint of a float sum

```click
theorem rounded(x: double, y: double) {
    requires x > float64_from_bits(0);
    requires y >= float64_from_bits(0x3ff0000000000000u64);
    ensures x + y > float64_from_bits(0x3ff0000000000000u64) by {
        normalize() using {
            x > float64_from_bits(0);
            y >= float64_from_bits(0x3ff0000000000000u64);
        };
    }
}
```

```expect
fail: did not normalize
```
