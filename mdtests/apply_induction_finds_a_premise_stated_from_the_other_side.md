# `apply(ih(m))` finds a premise stated from the other side

The elided `apply(ih(n - 1))` looks its premises up among the available
facts and proves none. As in an `apply(ih(m)) using { ... }` list, a premise
is also found when the proof states the same order claim from the other side:
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
        induct(n) as ih;
        if n <= 0 {
            unfold(countdown(n));
            normalize() using { n <= 0; };
        } else {
            have to_integer(n - 1) >= 0;
            have to_integer(n) > to_integer(n - 1);
            apply(ih(n - 1));
            unfold(countdown(n));
            rewrite(countdown(n - 1) == 0);
            normalize();
        }
    }
}
```

```expect
pass
```
