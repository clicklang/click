# A selected signed sum still requires an overflow bound

```click
theorem unknown_sum(flag: Bool, z: int64, w: int64) {
    requires flag;
    ensures (if flag { (z + w) as int64 } else { z }) == z by {
        normalize() using { flag; };
    }
}
```

```expect
fail: it denotes a value only where
```
