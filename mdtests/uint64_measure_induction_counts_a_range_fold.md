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
            have n == 0u64 by arithmetic() using { n <= 0u64; };
            rewrite(n == 0u64);
            normalize();
        } else {
            have 0u64 < n by simp();
            have 1u64 <= n by arithmetic() using { 0u64 < n; };
            have n - 1u64 < n by arithmetic() using { 0u64 < n; };
            have 0u64 <= n - 1u64 by normalize();
            have n - 1u64 < 18446744073709551615u64 by arithmetic() using { 0u64 < n; };
            apply(ih(n - 1u64)) using { n - 1u64 < n; };
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
}
```

```expect
pass
```
