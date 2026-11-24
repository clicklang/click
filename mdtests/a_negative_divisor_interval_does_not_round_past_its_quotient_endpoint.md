# Selected Integer division interval refusal

Numerator 9 and divisor -2 have truncating quotient -4.

```click
theorem rejected(n: Integer, d: Integer) {
    requires -8 <= n;
    requires n <= 9;
    requires -5 <= d;
    requires d <= -2;
    requires d != 0;
    ensures -3 <= truncating_quotient(n, d) by {
        close() using { -8 <= n; n <= 9; -5 <= d; d <= -2; };
    }
}
```

```expect
fail: could not prove the current goal from only its listed premises
```
