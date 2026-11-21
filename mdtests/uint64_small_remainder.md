# Small dividends keep their full-width unsigned remainder

```click
import click::integer;

theorem small_remainder(n: uint64, d: uint64) {
    requires n < d;
    ensures n % d == n by {
        have to_integer(n) < to_integer(d) by solve() using { n < d; };
        have 0 <= to_integer(n) by known();
        have 1 <= to_integer(d) by solve() using { 0 <= to_integer(n); to_integer(n) < to_integer(d); };
        have to_integer(d) != 0 by solve() using { 1 <= to_integer(d); };
        have d != 0u64 by solve() using { to_integer(d) != 0; };
        have 1 - to_integer(d) <= 0 by solve() using { 1 <= to_integer(d); };
        have to_integer(n) <= to_integer(d) - 1 by solve() using { to_integer(n) < to_integer(d); };
        apply(integer::small_remainder_interval(to_integer(n), to_integer(d), 0, to_integer(n), to_integer(d))) using {
            to_integer(d) != 0;
            1 <= to_integer(d);
            to_integer(d) <= to_integer(d);
            0 <= to_integer(n);
            to_integer(n) <= to_integer(n);
            1 - to_integer(d) <= 0;
            to_integer(n) <= to_integer(d) - 1;
        };
        apply(integer::uint64_remainder_to_integer(n, d)) using { d != 0u64; to_integer(d) != 0; };
        have to_integer(n % d) == to_integer(n) by known();
        known();
    }
}

theorem small_remainder_above_signed_high_bit(n: uint64) {
    requires n < 18446744073709551615u64;
    ensures n % 18446744073709551615u64 == n by {
        apply(small_remainder(n, 18446744073709551615u64)) using { n < 18446744073709551615u64; };
    }
}
```

```expect
pass
```
