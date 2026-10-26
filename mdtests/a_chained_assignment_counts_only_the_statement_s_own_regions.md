# A chained assignment counts only the statement's own regions

`.assignment(x, j)` counts the regions of the statement it follows, not the
regions of the statements nested in it. An `if` has one region of its own,
its test, so `statement(2).assignment(y, 0)` names nothing; the stores to `y`
are `statement(2).statement(0)` and `statement(2).statement(1)`.

```c filename=own_assignment.c
int32 stored(int32 c) {
    int32 x = 0;
    int32 y = 0;
    if (c == 0) {
        y = 1;
        y = 2;
    }
    return x + y;
}
```

```click
verifying "own_assignment.c";
int32 stored(int32 c) {
    ensures 0 <= result and result <= 2;
} by {
    step_until(statement(2).assignment(y, 0));
}
```

```expect
fail: `statement(2)` has 0 atomic region(s) of its own that assign `y`, so it has no `assignment(y, 0)`
```
