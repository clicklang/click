# A zero lower endpoint can still admit infinity times zero

```click
theorem zero_endpoint(x: float, y: float) {
    requires x >= float32_from_bits(0x3f800000);
    requires y >= float32_from_bits(0);
    ensures x * y >= float32_from_bits(0) by { close(); }
}
```

```expect
fail: could not establish
```
