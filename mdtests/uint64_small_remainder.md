# Small dividends keep their full-width unsigned remainder

```click
theorem small_remainder(n: uint64, d: uint64) {
    requires n < d;
    ensures n % d == n by { normalize() using { n < d; } }
}

theorem small_remainder_above_signed_high_bit(n: uint64) {
    requires n < 18446744073709551615u64;
    ensures n % 18446744073709551615u64 == n by {
        normalize() using { n < 18446744073709551615u64; }
    }
}
```

```expect
pass
```
