# A reflexive claim still owes its conversion domain

The binder includes 256, which cannot be converted to uint8.

```click
theorem scoped_conversion() {
    ensures 0 == 0 by {
        have forall (k: int32) {
            0 <= k and k <= 256 implies to_uint8(to_integer(k)) == to_uint8(to_integer(k))
        } by { intro(); intro(); normalize(); }
        normalize();
    }
}
```

```expect
fail: not established
```
