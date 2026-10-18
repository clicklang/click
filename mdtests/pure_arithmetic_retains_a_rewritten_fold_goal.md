# Arithmetic retains a rewritten fold goal

A `peel` followed by explicit rewrites can leave a valid Integer goal
without a source template. Arithmetic must still emit a checked certificate.

```click
import click::integer;

function full_width_count(n: uint64) -> Integer {
    (0..n).fold(0, |acc, k| { acc + to_integer(1) })
}

theorem count_step(n: uint64) {
    requires 0u64 < n;
    requires full_width_count(n - 1u64) == to_integer(n - 1u64);
    ensures full_width_count(n) == to_integer(n) by {
        have 0u64 < n by simp();
        have 1u64 <= n by arithmetic() using { 0u64 < n; };
        have n - 1u64 < n by arithmetic() using { 0u64 < n; };
        have 0u64 <= n - 1u64 by normalize();
        have n - 1u64 < 18446744073709551615u64 by arithmetic() using { 0u64 < n; };
        peel(full_width_count(n)) using {
            0u64 <= n - 1u64;
            n - 1u64 < 18446744073709551615u64;
        };
        rewrite(full_width_count(n - 1u64) == to_integer(n - 1u64));
        apply(uint64_less_equal_to_integer(1u64, n)) using { 1u64 <= n; };
        apply(uint64_subtract_to_integer(n, 1u64)) using {
            to_integer(1u64) <= to_integer(n);
        };
        rewrite(to_integer(n - 1u64) == to_integer(n) - to_integer(1u64));
        arithmetic() using {};
    }
}
```

```expect
pass
```
