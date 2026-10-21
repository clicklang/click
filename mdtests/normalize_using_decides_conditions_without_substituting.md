# `normalize using` decides conditions; it does not substitute terms

A cited `x == 7` decides every condition the cited equalities settle, such as
the guard `x == 7` of a conditional expression, and a comparison of `x` itself
with a constant, such as `x < 8`. It does not replace `x` by `7` inside
another term, so the goal `x * 2 < 15` is not reduced; `rewrite(x == 7)`
followed by `normalize()` proves it.

```click
theorem guard_is_decided(x: int32) {
    requires x == 7;
    ensures (if x == 7 { 1 } else { 2 }) == 1 by {
        normalize() using { x == 7; };
    }
}

theorem constant_comparison_is_decided(x: int32) {
    requires x == 7;
    ensures x < 8 by {
        normalize() using { x == 7; };
    }
}

theorem rewrite_substitutes(x: int32) {
    requires x == 7;
    ensures x * 2 < 15 by {
        rewrite(x == 7);
        normalize();
    }
}

theorem product_is_not_substituted(x: int32) {
    requires x == 7;
    ensures x * 2 < 15 by {
        normalize() using { x == 7; };
    }
}
```

```expect
fail: `normalize using` goal did not normalize to true using the listed conditions
```
