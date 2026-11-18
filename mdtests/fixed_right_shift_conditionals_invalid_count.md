# A selected right shift still requires an in-range count

```click
theorem invalid_right_shift(z: uint64, y: uint64) {
    requires (z >> 7) < y;
    ensures (if (z >> 7) < y { z >> 64 } else { z }) == z by {
        normalize() using { (z >> 7) < y; };
    }
}
```

```expect
fail: it denotes a value only where
```
