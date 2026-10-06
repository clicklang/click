# Remainder signs exclude correction endpoints

These lemmas use reconstruction and scaled bounds. They require no native
operation and no implicit multiplication ordering.

```click
theorem derived_lower_correction_bound(n: Integer, d: Integer, q: Integer, r: Integer, lower: Integer) {
    requires lower <= q;
    requires lower * d <= n;
    requires n == q * d + r;
    requires r < 0;
    ensures lower + 1 <= q by {
        if lower + 1 <= q {
            assumption();
        } else {
            have q == lower by { arithmetic() using { lower <= q; not (lower + 1 <= q); } }
            have n == lower * d + r by {
                rewrite(lower == q);
                assumption();
            }
            have not (r < 0) by { arithmetic() using { lower * d <= n; n == lower * d + r; } }
            contradiction(r < 0);
        }
    }
}

theorem derived_upper_correction_bound(n: Integer, d: Integer, q: Integer, r: Integer, upper: Integer) {
    requires q <= upper;
    requires n <= upper * d;
    requires n == q * d + r;
    requires 0 < r;
    ensures q <= upper + -1 by {
        if q <= upper + -1 {
            assumption();
        } else {
            have q == upper by { arithmetic() using { q <= upper; not (q <= upper + -1); } }
            have n == upper * d + r by {
                rewrite(upper == q);
                assumption();
            }
            have not (0 < r) by { arithmetic() using { n <= upper * d; n == upper * d + r; } }
            contradiction(0 < r);
        }
    }
}

theorem use_lower_correction_bound(n: Integer, d: Integer, q: Integer, r: Integer, bound: Integer) {
    requires bound <= q; requires bound * d <= n;
    requires n == q * d + r;
    requires r < 0;
    ensures bound + 1 <= q by { apply(integer_lower_correction_bound(n, d, q, r, bound)); }
}
theorem use_upper_correction_bound(n: Integer, d: Integer, q: Integer, r: Integer, bound: Integer) {
    requires q <= bound; requires n <= bound * d;
    requires n == q * d + r;
    requires 0 < r;
    ensures q <= bound + -1 by { apply(integer_upper_correction_bound(n, d, q, r, bound)); }
}
```

```expect
pass
```
