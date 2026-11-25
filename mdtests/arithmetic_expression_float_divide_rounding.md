# Float division by a literal can round a positive value to zero

```click
theorem rounded(x: float) {
    requires x > float32_from_bits(0);
    ensures x / float32_from_bits(0x40000000) > float32_from_bits(0) by {
        close() using { x > float32_from_bits(0); };
    }
}
```

```expect
fail: `close() using` could not prove the current goal from only its listed premises
```
