# Opaque arithmetic retains its exact terms and evaluation guards

```click
theorem unguarded(x: int64, y: int64) {
    ensures to_integer(x + 1i64) * to_integer(y) - to_integer(x + 1i64) * to_integer(y) == 0 by arithmetic();
}
```

```expect
fail: overflow
```
