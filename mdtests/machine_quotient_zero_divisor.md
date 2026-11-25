# Quotient bounds require a nonzero positive divisor

A specification quotient by a divisor that may be zero is defined: at zero
it is the opaque total quotient. That value bounds nothing, so `n / d <= n`
does not normalize without a positive divisor.

```click
theorem missing_divisor_guard(n: int32, d: int32) {
    requires 0 <= n;
    requires n != -2147483648 or d != -1;
    ensures n / d <= n by { close() using { 0 <= n; }; }
}
```

```expect
fail: `close() using` could not prove the current goal from only its listed premises
```
