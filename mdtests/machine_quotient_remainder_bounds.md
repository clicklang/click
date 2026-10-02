# Quotients and remainders preserve the bounded nonnegative range

These local rules require a nonnegative signed-word dividend and a strictly
positive signed-word divisor. The unsigned operations have the same value
within that range; a high-bit unsigned dividend does not satisfy the guard.

```click
theorem signed_bounds(n: int32, d: int32) {
    requires 0 <= n;
    requires 0 < d;
    ensures 0 <= n / d by { normalize() using { 0 <= n; 0 < d; } }
    ensures n / d <= n by { normalize() using { 0 <= n; 0 < d; } }
    ensures 0 <= n % d by { normalize() using { 0 <= n; 0 < d; } }
    ensures n % d <= n by { normalize() using { 0 <= n; 0 < d; } }
}
theorem unsigned_bounds(n: uint32, d: uint32) {
    requires 0 <= (int32)n;
    requires 0 < (int32)d;
    ensures 0 <= (int32)(n / d) by { normalize() using { 0 <= (int32)n; 0 < (int32)d; } }
    ensures ((int32)(n / d)) <= (int32)n by { normalize() using { 0 <= (int32)n; 0 < (int32)d; } }
    ensures 0 <= (int32)(n % d) by { normalize() using { 0 <= (int32)n; 0 < (int32)d; } }
    ensures ((int32)(n % d)) <= (int32)n by { normalize() using { 0 <= (int32)n; 0 < (int32)d; } }
}
```

```expect
pass
```
