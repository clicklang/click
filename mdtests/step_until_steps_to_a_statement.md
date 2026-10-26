# `step_until` steps to a statement

`step_until(statement(i))` repeats `step()` up to the selected statement, and
the proof continues there. The removed spelling `execute_until` is refused.

```c filename=step_until_steps_to_a_statement.c
int32 add_twice(int32 x) {
    int32 y = x + 1;
    int32 z = y + 1;
    return z;
}
```

```click
verifying "step_until_steps_to_a_statement.c";

int32 add_twice(int32 x) {
    requires x < 100;
    ensures result == x + 2;
} by {
    step_until(statement(2));
    have z == x + 2;
}
```

```expect
pass
```
