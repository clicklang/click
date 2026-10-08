# Equality with a positive divisor does not preserve a remainder

```click
theorem not_a_strict_bound(n: uint64) {
    requires n <= 4u64;
    ensures n % 4u64 == n by { normalize() using { n <= 4u64; } }
}
```

```expect
fail: goal did not normalize to true
```
