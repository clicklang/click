# explicit induction certificate uses only checked operations

This is the fully expanded form of the smart proof in
`pure_induction_countdown.md`. The induction application names its exact side
conditions, and recursive evaluation is exposed by one-layer function
`unfold` operations.

```click
function countdown_explicit(n: int32) -> int32
    decreases n
{
    if n <= 0 { 0 } else { countdown_explicit(n - 1) }
}

theorem countdown_explicit_is_zero(n: int32) {
    requires n >= 0;
    ensures countdown_explicit(n) == 0 by {
        induct(n) as ih;
        if n <= 0 {
            unfold(countdown_explicit(n));
            normalize() using { n <= 0; };
        } else {
            have 0 <= to_integer(n - 1);
            have to_integer(n - 1) < to_integer(n);
            apply(ih(n - 1)) using {
                0 <= to_integer(n - 1);
                to_integer(n - 1) < to_integer(n);
                to_integer(n - 1) >= 0;
            };
            unfold(countdown_explicit(n));
            rewrite(countdown_explicit(n - 1) == 0);
            normalize();
        }
    }
}
```

```expect
pass
```
