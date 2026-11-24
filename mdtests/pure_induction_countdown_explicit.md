# explicit induction certificate uses only checked operations

This is the fully expanded form of the smart proof in
`pure_induction_countdown.md`. Two `have` steps state the induction premises, and recursive evaluation is exposed by one-layer function
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
        let ih = induct(n);
        if n <= 0 {
            unfold(countdown_explicit(n));
            close() using { n <= 0; };
        } else {
            have 0 <= to_integer(n - 1);
            have to_integer(n - 1) < to_integer(n);
            apply(ih(n - 1));
            unfold(countdown_explicit(n));
            rewrite(countdown_explicit(n - 1), 0);
            close();
        }
    }
}
```

```expect
pass
```
