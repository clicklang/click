# A polynomial node rejects a false successor coefficient

```click
theorem false_successor(n: Integer) {
    ensures (n + 1) * (n + 2) == n * (n + 1) + 3 * (n + 1) by {
        arithmetic_certificate special {
            integer_polynomial_identity bounds [] => (n + 1) * (n + 2) == n * (n + 1) + 3 * (n + 1);
            conclusion 0;
        }
    }
}
```

```expect
fail: node 0 requires a true Integer polynomial identity
```
