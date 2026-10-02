# An unsigned quotient can have its sign bit set

```click
theorem missing_dividend_range(n: uint32, d: uint32) {
    requires 0 < (int32)d;
    ensures 0 <= (int32)(n / d) by { normalize() using { 0 < (int32)d; } }
}
```

```expect
fail: did not normalize to true
```
