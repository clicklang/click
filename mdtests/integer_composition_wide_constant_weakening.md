# Integer composition preserves wide constant arithmetic

A constant-only intermediate must retain exact Integer typing when its
magnitude exceeds the signed machine range.

```click
theorem widen(z: Integer) {
    requires 0 <= z;
    requires z <= 4000;
    ensures z <= 18446744073709551615 by {
        close();
    }
}

theorem neighboring_small_bound(z: Integer) {
    requires z <= 4000;
    ensures z <= 5000 by { close() using { z <= 4000; }; }
}
```

```expect
pass
```
