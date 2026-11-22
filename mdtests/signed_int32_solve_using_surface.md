# An explicit signed int32 `solve() using`

```click quick-solve
theorem signed_int32_solve_using_surface(x: int32) {
    requires x <= 1;
    ensures x <= 1 by {
        solve() using { x <= 1; };
    }
}
```

```expect
pass
```
