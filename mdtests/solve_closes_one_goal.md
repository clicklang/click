# `solve` closes one goal, and `simp` is its older spelling

`solve()` closes the first open goal from the available facts and runs no C.
`solve() using { ... }` reads only the listed premises. `simp()` and
`simp() using { ... }` are the same tactic under its older name.

```c filename=solve_closes_one_goal.c
int32 solve_one(int32 x) {
    return x;
}
```

```click
verifying "solve_closes_one_goal.c";

int32 solve_one(int32 x) {
    requires x == 3;
    ensures add_zero: result == x + 0 by { execute(); solve(); }
    ensures listed: x + 1 == 4 by { execute(); solve() using { x == 3; }; }
    ensures older_spelling: result == x by { execute(); simp(); }
}
```

```expect
pass
```
