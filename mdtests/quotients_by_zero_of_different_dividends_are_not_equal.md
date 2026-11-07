# Quotients by zero of different dividends are not equal

Two quotients by zero are the same value only when their operands are: the
opaque quotient is a function of its operands, and nothing else relates it.

```click
theorem quotients_by_zero(a: uint32, b: uint32) {
    ensures a / 0u32 == b / 0u32;
}
```

```expect
fail: could not establish `(a / 0u32) == (b / 0u32)`
```
