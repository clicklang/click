# Subtracting a tiny negative float can round back to the literal

```click
theorem rounded(x: float) {
    requires x < float32_from_bits(0);
    ensures float32_from_bits(0x3f800000) - x > float32_from_bits(0x3f800000) by {
        close();
    }
}
```

```expect
fail: could not establish
```
