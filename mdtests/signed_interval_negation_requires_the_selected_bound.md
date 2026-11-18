# Negation preserves the selected premise boundary

The subtraction-from-zero bridge must not borrow an omitted int64 bound
from the ambient context.

```click
theorem omitted(a: int64) {
    requires a > -9223372036854775808i64;
    ensures defined(-a) by {
        solve() using {};
    }
}
```

```expect
fail: could not prove the current goal from only its listed premises
```
