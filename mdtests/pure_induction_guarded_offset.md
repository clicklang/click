# Numeric induction preserves guarded index expressions

The hypothesis keeps every requirement at its smaller argument. Its guarded
addition uses those premises during lowering and expanded proof replay.

```click
function guarded_countdown(n: int32) -> int32
    decreases n
{
    if n <= 0 { 0 } else { guarded_countdown(n - 1) }
}

theorem guarded_count(base: int32, n: int32) {
    requires 0 <= base;
    requires 0 <= n;
    requires base <= 1000000;
    requires n <= 1000000;
    requires defined(base + n);
    ensures guarded_countdown(n) == 0 and base + n == base + n by {
        induct(n) as ih;
        if n <= 0 {
            both { unfold(guarded_countdown(n)); normalize() using { n <= 0; } }
            and { normalize(); }
        } else {
            have 0 < n by { simp(); }
            have 0 <= n - 1 by { arithmetic() using { 0 < n; } }
            have n - 1 < n by { arithmetic() using { 0 < n; } }
            have defined(n - 1) by { simp(); }
            have base <= 2147483647 - (n - 1) by { arithmetic() using { 0 <= base; base <= 1000000; 0 <= n; n <= 1000000; 0 < n; } }
            have n - 1 <= 1000000 by { arithmetic() using { 0 < n; n <= 1000000; } }
            apply(int32_nonnegative_add_within_max_is_defined(base, n - 1));
            have defined(base + (n - 1)) by { assumption(); }
            apply(ih(n - 1));
            both {
                unfold(guarded_countdown(n));
                rewrite(guarded_countdown(n - 1) == 0);
                normalize() using { not(n <= 0); }
            } and { normalize(); }
        }
    }
}
```

```expect
pass
```
