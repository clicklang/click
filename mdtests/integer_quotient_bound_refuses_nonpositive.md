# Reject unsupported scaled quotient evidence

```click
theorem wrong(n: Integer, d: Integer, b: Integer) {
    requires d != 0;
    requires 0 <= d;
    requires b * d <= n;
    ensures b <= truncating_quotient(n, d) by {
        close() using { b * d <= n; 0 <= d; };
    }
}
```

```expect
fail: `close() using`
```
