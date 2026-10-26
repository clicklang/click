# A uint64 induction proves a full-width range fold

```click
import click::integer;

function full_width_count(n: uint64) -> Integer {
    (0..n).fold(0, |acc, k| { acc + to_integer(1) })
}

theorem full_width_count_is_its_length(n: uint64) {
    ensures full_width_count(n) == to_integer(n) by {
        induct(n) as ih;
        if n <= 0u64 {
            peel(full_width_count(n)) using { n <= 0u64; };
            have n == 0u64 by solve() using { n <= 0u64; };
            rewrite(n == 0u64);
            normalize();
        } else {
            have 0u64 < n by solve();
            have 1u64 <= n by solve() using { 0u64 < n; };
            have to_integer(n - 1u64) < to_integer(n) by solve() using { 0u64 < n; };
            have to_integer(0u64) <= to_integer(n - 1u64) by normalize();
            have to_integer(n - 1u64) < to_integer(18446744073709551615u64) by solve() using { 0u64 < n; };
            apply(ih(n - 1u64)) using { to_integer(n - 1u64) < to_integer(n); };
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
}
```

```expect
pass
```
