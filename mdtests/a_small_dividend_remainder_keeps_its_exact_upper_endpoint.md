# Selected Integer division interval refusal

Every admitted dividend is smaller than every divisor. Numerator 3 has remainder 3, not at most 2.

```click
theorem rejected(n: Integer, d: Integer) {
    requires 2 <= n;
    requires n <= 3;
    requires 5 <= d;
    requires d <= 8;
    requires d != 0;
    ensures truncating_remainder(n, d) <= 2 by {
        close() using { 2 <= n; n <= 3; 5 <= d; d <= 8; };
    }
}
```

```expect
fail: could not prove the current goal from only its listed premises
```
