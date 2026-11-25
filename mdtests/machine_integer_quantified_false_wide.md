# machine integer quantified false wide

```click
theorem bad(n: int64) {
    requires 0i64 <= n and n <= 100i64;
    ensures exists (x: int64) { x == n + 1i64 } by {
        witness(n);
        close();
    }
}
```

```expect
fail: could not establish `to_integer(n) == (to_integer(n) + to_integer(1i64))`
```
