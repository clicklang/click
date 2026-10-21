# `unfold` rewrites each occurrence of the exact call

`unfold(f(n))` adds the defining equation of `f(n)` and replaces every
occurrence of the call `f(n)` in the goal by one layer of its body. A call of
the same function at another argument, `f(m)`, stays folded, and so does the
recursive call in the body of `steps`. The refreshed goal is lowered again,
which evaluates the constant `if` condition of `steps(2)`; a refreshed goal
that is merely true still needs a closer, here `normalize()`.

```click
function f(x: int32) -> int32 { x }

function steps(n: int32) -> int32
    decreases n
{
    if n <= 0 { 0 } else { steps(n - 1) }
}

theorem every_occurrence(n: int32, m: int32) {
    requires f(m) == m;
    ensures f(n) + f(n) == n + n implies f(m) == m by {
        unfold(f(n));
        intro();
        assumption();
    }
}

theorem one_layer() {
    requires steps(1) == 0;
    ensures steps(2) == 0 by {
        unfold(steps(2));
    }
}

theorem refreshed_to_true() {
    ensures f(3) == 3 by {
        unfold(f(3));
        normalize();
    }
}
```

```expect
pass
```
