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
        have 0u64 < n by solve();
        have 1u64 <= n by solve() using { 0u64 < n; };
        have to_integer(n - 1u64) < to_integer(n) by solve() using { 0u64 < n; };
        have to_integer(0u64) <= to_integer(n - 1u64) by normalize();
        have to_integer(n - 1u64) < to_integer(18446744073709551615u64) by solve() using { 0u64 < n; };
        peel(full_width_count(n)) using {
            to_integer(0u64) <= to_integer(n - 1u64);
            to_integer(n - 1u64) < to_integer(18446744073709551615u64);
        };
        rewrite(full_width_count(n - 1u64) == to_integer(n - 1u64));
        have to_integer(1u64) <= to_integer(n);
        have to_integer(n - 1u64) == to_integer(n) - to_integer(1u64);
        rewrite(to_integer(n - 1u64) == to_integer(n) - to_integer(1u64));
        solve() using {};
    }
}
```

```expect
pass
```
