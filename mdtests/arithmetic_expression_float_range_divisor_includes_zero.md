# Finite divisor endpoints do not exclude zero between them

```click
theorem no_bound(x: float, y: float) {
    requires x >= float32_from_bits(0x3f800000);
    requires x <= float32_from_bits(0x40000000);
    requires y >= float32_from_bits(0xbf800000);
    requires y <= float32_from_bits(0x3f800000);
    ensures x / y >= float32_from_bits(0xc0000000) by {
        close() using {
            x >= float32_from_bits(0x3f800000);
            x <= float32_from_bits(0x40000000);
            y >= float32_from_bits(0xbf800000);
            y <= float32_from_bits(0x3f800000);
        };
    }
}
```

```expect
fail: `close() using` could not prove the current goal from only its listed premises
```
