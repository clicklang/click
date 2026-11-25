# A signed remainder need not be nonnegative

```click
theorem missing_nonnegative_dividend(n: int32, d: int32) {
    requires n < 0;
    requires 0 < d;
    ensures 0 <= n % d by { close() using { n < 0; 0 < d; }; }
}
```

```expect
fail: `close() using` could not prove the current goal from only its listed premises
```
