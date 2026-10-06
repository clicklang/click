# Reject an out-of-range native int64 literal

```click
theorem bad() { ensures to_integer(-9223372036854775809i64) == 0 by { normalize(); } }
```

```expect
fail: outside 0..9223372036854775807
```
