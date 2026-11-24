# An explicit signed int32 `close() using`

```click quick-solve
theorem signed_int32_solve_using_surface(x: int32) {
    requires x <= 1;
    ensures x <= 1 by {
        close() using { x <= 1; };
    }
}
```

```expect
pass
```
