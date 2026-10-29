# A conversion requirement uses its bound variable

```click
theorem scoped_conversion() {
    ensures 0 == 0 by {
        have forall (k: int32) {
            0 <= k and k <= 255 implies to_uint8(to_integer(k)) == to_uint8(to_integer(k))
        } by { intro(); intro(); normalize(); }
        normalize();
    }
}
```

```expect
pass
```
