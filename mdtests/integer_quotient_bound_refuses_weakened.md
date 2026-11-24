# Reject unsupported scaled quotient evidence

```click
theorem wrong(n: Integer, d: Integer, b: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires (b + -1) * d <= n;
    ensures b <= truncating_quotient(n, d) by {
        close() using { (b + -1) * d <= n; 1 <= d; };
    }
}
```

```expect
fail: solve
```
