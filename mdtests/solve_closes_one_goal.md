# `solve` closes one goal

`solve()` closes the first open goal from the available facts and runs no C.
`solve() using { ... }` reads only the listed premises. The removed spelling
`solve` is refused.

```c filename=solve_closes_one_goal.c
int32 solve_one(int32 x) {
    return x;
}
```

```click
verifying "solve_closes_one_goal.c";

int32 solve_one(int32 x) {
    requires x == 3;
    ensures add_zero: result == x + 0 by { step_until(function.exit); solve(); }
    ensures listed: x + 1 == 4 by { step_until(function.exit); solve() using { x == 3; }; }
}
```

```expect
pass
```
