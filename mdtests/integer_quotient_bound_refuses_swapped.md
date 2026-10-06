# Reject unsupported scaled quotient evidence

```click
theorem wrong(n: Integer, d: Integer, b: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires b * d <= n;
    ensures b <= truncating_quotient(n, d) by {
        arithmetic_certificate special {
            premise 0: b * d <= n => b * d <= n;
            premise 1: 1 <= d => 1 <= d;
            integer_quotient_bound bounds [1, 0] => b <= truncating_quotient(n, d);
            conclusion 0;
        }
    }
}
```

```expect
fail: node 0 requires an exact scaled numerator bound
```
