# assumption sends an evaluated goal to normalize

Binding `value` to the assigned constant `1` makes `have value == 1` the goal
`true`. `assumption()` closes goals from facts, so it refuses and names
`normalize()`, which closes goals true by evaluation.

```c filename=assumption_sends_an_evaluated_goal_to_normalize.c
int f(int x) { int r; r = 1; return r; }
```

```click
verifying "assumption_sends_an_evaluated_goal_to_normalize.c";

int32 f(int32 x) {
    ensures result == 1;
} by {
    step();
    let { result: value } = step();
    have value == 1 by assumption();
    execute();
    simp();
}
```

```expect
fail: this goal is true by evaluation alone; close it with `normalize()`
```
