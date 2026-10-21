# normalize using decides an algebraic equality goal

A cited algebraic equality decides a goal that states it, in either
orientation, and a cited negation decides its `not`, as it does a
conditional-expression guard.

```c filename=normalize_using_decides_an_algebraic_equality_goal.c
void unused(void) {}
```

```click
verifying "normalize_using_decides_an_algebraic_equality_goal.c";

theorem same<T>(xs: List<T>, ys: List<T>) {
    requires xs == ys;
    ensures xs == ys by { normalize() using { xs == ys; }; }
    ensures ys == xs by { normalize() using { xs == ys; }; }
}

theorem different<T>(xs: List<T>, ys: List<T>) {
    requires not(xs == ys);
    ensures not(xs == ys) by { normalize() using { not(xs == ys); }; }
}
```

```expect
pass
```
