# Reject unsupported scaled quotient evidence

```click
theorem wrong(n: Integer, d: Integer, b: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires (b + -1) * d <= n;
    ensures b <= truncating_quotient(n, d) by {
        arithmetic_certificate special {
            premise 0: (b + -1) * d <= n => (b + -1) * d <= n;
            premise 1: 1 <= d => 1 <= d;
            integer_quotient_bound bounds [0, 1] => b <= truncating_quotient(n, d);
            conclusion 0;
        }
    }
}
```

```expect
fail: node 0 does not state what its rule derives from its inputs
```
