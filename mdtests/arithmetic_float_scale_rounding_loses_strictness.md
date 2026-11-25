# Rounding can make a strict input bound non-strict


```click
theorem rounded(x: float) {
    requires x > float32_from_bits(0);
    ensures x * float32_from_bits(0x3f000000) > float32_from_bits(0) by {
        close() using { x > float32_from_bits(0); };
    }
}
```

```expect
fail: `close() using` could not prove the current goal from only its listed premises
```
