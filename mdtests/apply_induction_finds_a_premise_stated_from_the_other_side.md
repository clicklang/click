# `apply(ih(m))` finds a premise stated from the other side

`apply(ih(n - 1))` uses facts already in scope before asking the solver.
It finds an order premise stated from the other side:
`to_integer(n - 1) >= 0` for `0 <= to_integer(n - 1)`, and
`to_integer(n) > to_integer(n - 1)` for `to_integer(n - 1) < to_integer(n)`.

```click
function countdown(n: int32) -> int32
    decreases n
{
    if n <= 0 { 0 } else { countdown(n - 1) }
}

theorem countdown_is_zero(n: int32) {
    requires n >= 0;
    ensures countdown(n) == 0 by {
        let ih = induct(n);
        if n <= 0 {
            unfold(countdown(n));
            close() using { n <= 0; };
        } else {
            have to_integer(n - 1) >= 0;
            have to_integer(n) > to_integer(n - 1);
            apply(ih(n - 1));
            unfold(countdown(n));
            rewrite(countdown(n - 1), 0);
            known();
        }
    }
}
```

```expect
pass
```
