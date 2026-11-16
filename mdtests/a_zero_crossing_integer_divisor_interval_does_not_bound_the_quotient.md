# Selected Integer division interval refusal

The nonzero divisor can still be 1, so numerator 8 is a counterexample.

```click
theorem rejected(n: Integer, d: Integer) {
    requires 1 <= n;
    requires n <= 8;
    requires -2 <= d;
    requires d <= 2;
    requires d != 0;
    ensures truncating_quotient(n, d) <= 4 by {
        solve() using { 1 <= n; n <= 8; -2 <= d; d <= 2; };
    }
}
```

```expect
fail: could not prove the current goal from only its listed premises
```
