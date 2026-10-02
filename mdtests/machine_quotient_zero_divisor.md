# Quotient bounds require a nonzero positive divisor

```click
theorem missing_divisor_guard(n: int32, d: int32) {
    requires 0 <= n;
    ensures n / d <= n by { normalize() using { 0 <= n; } }
}
```

```expect
fail: did not normalize to true
```
