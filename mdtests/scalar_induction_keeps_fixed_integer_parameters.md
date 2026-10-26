# Scalar induction keeps fixed Integer parameters

The induction hypothesis varies the native measure and retains the same
mathematical seed, including requirements on that seed.

```click
function carry_seed(n: int32, seed: Integer) -> Integer {
    (0..n).fold(seed, |acc, k| { acc + to_integer(0) })
}

theorem carry_seed_returns_the_same_integer(n: int32, seed: Integer) {
    requires 0 <= n;
    requires 0 < seed;
    ensures carry_seed(n, seed) == seed by {
        induct(n) as ih;
        if n <= 0 {
            peel(carry_seed(n, seed)) using { n <= 0; };
            normalize();
        } else {
            have 0 < n by solve();
            have 0 <= to_integer(n - 1) by solve() using { 0 < n; };
            have to_integer(n - 1) < 2147483647 by solve() using { 0 < n; };
            have to_integer(n - 1) < to_integer(n);
            apply(ih(n - 1));
            peel(carry_seed(n, seed)) using {
                0 <= to_integer(n - 1);
                to_integer(n - 1) < 2147483647;
            };
            normalize();
        }
    }
}
```

```expect
pass
```
