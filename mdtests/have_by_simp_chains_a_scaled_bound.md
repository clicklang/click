# `solve` chains a scaled bound

The same bound as `have_by_auto_refutes_a_linear_bound.md`, proved with
`solve`. On an arithmetic goal `solve` runs arithmetic from the facts connected
to the goal, so it refutes the integer negation of `total <= 255000` from all
three requirements, as the omitted proof does.

```click
theorem simp_chains_scaled_bound(i: Integer, n: Integer, total: Integer) {
    requires i < n;
    requires n <= 1000;
    requires total <= 255 * i;
    ensures total <= 255000 by {
        have total <= 255000 by solve();
        assumption();
    }
}
```

```expect
pass
```
