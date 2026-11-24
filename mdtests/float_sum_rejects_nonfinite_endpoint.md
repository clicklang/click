# Rounded sum bounds require finite endpoints

```click
theorem bad_pair(x: float, y: float) {
    requires x >= float32_from_bits(0xff800000);
    requires y >= float32_from_bits(0);
    ensures x + y >= float32_from_bits(0xff800000) by {
        apply(click::float_order::float32_add_lower(
            x, y, float32_from_bits(0xff800000), float32_from_bits(0)
        ));
    }
}
```

```expect
fail: isfinite
```
