# arithmetic does not treat int32 as unbounded integers

Without bounds, the affine-looking expressions below may overflow before the
comparison is made.

```click
theorem unbounded_affine_overflow(x: int32) {
    ensures to_integer(2 * x) < to_integer(x + (x + 1)) by {
        solve() using {};
    }
}
```

```expect
fail: `2 * x` must not overflow
```
