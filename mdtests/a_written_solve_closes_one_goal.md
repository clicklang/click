# A written `close()` closes one goal

The first `close()` discharges the first open goal. The second `close()`
discharges the second goal.

```c filename=a_written_solve_closes_one_goal.c
int32 f(int32 n) {
    return n;
}
```

```click
verifying "a_written_solve_closes_one_goal.c";

int32 f(int32 n) {
    requires n == 1;
    ensures result == 1;
    ensures result == n;
} by {
    step_until(function.exit);
    close();
    close();
}
```

```expect
pass
```
