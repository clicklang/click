# `have P` without a proof proves a linear bound with the solver

Arithmetic search expands to ordinary proof steps, with the selected premises
stated explicitly in `solve() using { ... }`.

```click
theorem solver_chains_bounds(i: Integer, n: Integer, total: Integer) {
    requires i < n;
    requires n <= 1000;
    requires total <= 255 * i;
    ensures total <= 255000 by {
        have total <= 255000;
        known();
    }
}
```

```expect
pass
```
