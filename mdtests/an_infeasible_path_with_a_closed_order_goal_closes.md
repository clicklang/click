# An infeasible path whose goal is a closed comparison closes

The arms of `cases` rejoin, so the implicit tail runs the `if` under
`x == 1 or x == 2 or x == 3` alone. On the `x <= 0` path `result >= 1`
lowers to the closed comparison `0 >= 1`, which lowering keeps as written.
Like the goal `false`, it is proved by refuting the path: each disjunct
contradicts `x <= 0`. The equality form of this proof is
[`cases_at_a_frontier_finishes_each_arm.md`](cases_at_a_frontier_finishes_each_arm.md).

```c filename=an_infeasible_path_with_a_closed_order_goal_closes.c
int32 f(int32 x) {
    if (x > 0) {
        return 1;
    }
    return 0;
}
```

```click
verifying "an_infeasible_path_with_a_closed_order_goal_closes.c";

int32 f(int32 x) {
    requires x == 1 or x == 2 or x == 3;
    ensures result >= 1;
} by {
    cases {
        x == 1 => { }
        x == 2 => { }
        x == 3 => { }
    }
}
```

```expect
pass
```
