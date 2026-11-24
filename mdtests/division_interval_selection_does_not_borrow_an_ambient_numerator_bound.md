# Selected Integer division interval refusal

The upper numerator bound stays ambient but is deliberately omitted from the selected arithmetic premises.

```click
theorem rejected(n: Integer, d: Integer) {
    requires -8 <= n;
    requires n <= 9;
    requires 2 <= d;
    requires d <= 5;
    requires d != 0;
    ensures truncating_quotient(n, d) <= 4 by {
        close() using { -8 <= n; 2 <= d; d <= 5; };
    }
}
```

```expect
fail: could not prove the current goal from only its listed premises
```
