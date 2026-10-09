# A uint64 equality that does not follow is not arithmetic

`a <= b` alone does not give `a == b`. `arithmetic` proves a 64-bit
equality as the equality of two Integer observations, and
`to_integer(a) <= to_integer(b)` does not make them equal, so the step is
refused.

`a_uint64_equality_closes_with_arithmetic.md` lists the other half.

```click
theorem squeeze(a: uint64, b: uint64) {
    requires a <= b;
    ensures a == b by {
        arithmetic() using { a <= b; }
    }
}
```

```expect
fail: does not follow from the listed premises' Integer readings
```
