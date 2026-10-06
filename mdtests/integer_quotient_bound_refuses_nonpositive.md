# Reject unsupported scaled quotient evidence

```click
theorem wrong(n: Integer, d: Integer, b: Integer) {
    requires d != 0;
    requires 0 <= d;
    requires b * d <= n;
    ensures b <= truncating_quotient(n, d) by {
        arithmetic_certificate special {
            premise 0: b * d <= n => b * d <= n;
            premise 1: 0 <= d => 0 <= d;
            integer_quotient_bound bounds [0, 1] => b <= truncating_quotient(n, d);
            conclusion 0;
        }
    }
}
```

```expect
fail: node 0 requires an exact scaled numerator bound
```
