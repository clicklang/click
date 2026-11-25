# An unsigned quotient can have its sign bit set

```click
theorem missing_dividend_range(n: uint32, d: uint32) {
    requires 0 < d as int32;
    ensures 0 <= (n / d) as int32 by { close() using { 0 < d as int32; }; }
}
```

```expect
fail: `close() using` could not prove the current goal from only its listed premises
```
