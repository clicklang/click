# A zero lower endpoint does not bound a positive reciprocal

```click
theorem unsafe_bound(y: float) {
    requires y >= float32_from_bits(0);
    ensures float32_from_bits(0x3f800000) / y <= float32_from_bits(0x3f800000) by {
        normalize() using { y >= float32_from_bits(0); };
    }
}
```

```expect
fail: did not normalize
```
