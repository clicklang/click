# arithmetic proves any goal from contradictory premises

`x < 0` beside `x >= 0` leaves no value for `x`, so they prove any goal. The
signed planner, which plans an interval for every operand it needs defined,
declines the empty interval rather than planning a certificate the kernel would
refuse. `arithmetic()` then refutes the goal's negation by simplex, its last
engine, and the kernel checks that refutation.

```c filename=arithmetic_proves_any_goal_from_contradictory_premises.c
int32 pick(int32 x, int32 y) {
    return y;
}
```

```click
verifying "arithmetic_proves_any_goal_from_contradictory_premises.c";

int32 pick(int32 x, int32 y) {
    requires x >= 0 and y >= 0 and y <= 2147483647;
    ensures result == y;
} by {
    have x < 0 implies to_integer(y) < to_integer(y - x) by { intro(); solve() using { x < 0; x >= 0; }; }
    step();
    solve();
}
```

```expect
pass
```
