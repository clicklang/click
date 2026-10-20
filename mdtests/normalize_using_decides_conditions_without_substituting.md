# `normalize using` decides conditions; it does not substitute terms

A cited `x == 7` decides every condition the cited equalities settle, such as
the guard `x == 7` of a conditional expression, and puts `x` in the same
equality class as `7`. It does not replace `x` by `7` in the goal, so the
order goal `x < 8` is not reduced; `rewrite(x == 7)` followed by
`normalize()` proves it.

```click
theorem guard_is_decided(x: int32) {
    requires x == 7;
    ensures (if x == 7 { 1 } else { 2 }) == 1 by {
        normalize() using { x == 7; };
    }
}

theorem rewrite_substitutes(x: int32) {
    requires x == 7;
    ensures x < 8 by {
        rewrite(x == 7);
        normalize();
    }
}

theorem order_goal_is_not_substituted(x: int32) {
    requires x == 7;
    ensures x < 8 by {
        normalize() using { x == 7; };
    }
}
```

```expect
fail: `normalize using` goal did not normalize to true using the listed conditions
```
