# `arithmetic` proves a wrapper function's bound once the wrapper is unfolded

`arithmetic` decides linear claims over the atoms it is given; it does not open
function definitions. `w2(a, b)` is one atom until the proof unfolds it, and
then the goal is `0 <= d(a) + d(b)`, which follows linearly from the two listed
bounds. The recursive `d` applications stay atoms throughout. The same holds
with a wrapper on both sides of a strict comparison.

```click
spec enum Ctx { Top, Up(Ctx) }

function d(c: Ctx) -> Integer decreases c {
    match c { Ctx::Top => 0, Ctx::Up(u) => 1 + d(u) }
}

function w2(a: Ctx, b: Ctx) -> Integer { d(a) + d(b) }

theorem bound_through_wrapper(a: Ctx, b: Ctx) {
    requires 0 <= d(a);
    requires 0 <= d(b);
    ensures 0 <= w2(a, b) by {
        unfold(w2(a, b));
        arithmetic() using { 0 <= d(a); 0 <= d(b); }
    }
}

theorem bound_between_wrappers(a: Ctx, b: Ctx, c: Ctx) {
    requires d(a) < d(b);
    ensures w2(a, c) < w2(b, c) by {
        unfold(w2(a, c));
        unfold(w2(b, c));
        arithmetic() using { d(a) < d(b); }
    }
}
```

```expect
pass
```
