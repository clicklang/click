# Integer certificates by refutation and by rounding

Arithmetic search expands to ordinary proof steps, with the selected premises
stated explicitly in `solve() using { ... }`.

```click
theorem refute_the_negated_goal(x: Integer) {
    requires 2 * x <= 10;
    ensures x <= 5 by {
        solve() using { 2 * x <= 10; };
    }
}

theorem contradictory_premises_prove_any_bound(x: Integer, y: Integer) {
    requires x <= 0;
    requires 1 <= x;
    ensures y <= 7 by {
        solve() using { x <= 0; 1 <= x; };
    }
}

theorem round_a_halved_bound(x: Integer) {
    requires 2 * x <= 5;
    ensures x <= 2 by {
        solve() using { 2 * x <= 5; };
    }
}
```

```expect
pass
```
