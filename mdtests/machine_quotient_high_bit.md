# An unsigned quotient can have its sign bit set

```click
theorem missing_dividend_range(n: uint32, d: uint32) {
    requires 0 < d as int32;
    ensures 0 <= (n / d) as int32 by { normalize() using { 0 < d as int32; }; }
}
```

```expect
fail: did not normalize to true
```
