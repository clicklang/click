# A written `auto` closes one goal

Written as a step of a script, `auto();` is the older spelling of `solve();`:
it closes the first open goal, and the next closer, here `normalize()`, takes
the second.

```c filename=a_written_auto_closes_one_goal.c
int32 f(int32 n) {
    return n;
}
```

```click
verifying "a_written_auto_closes_one_goal.c";

int32 f(int32 n) {
    requires n == 1;
    ensures result == 1;
    ensures result == n;
} by {
    execute();
    auto();
    normalize();
}
```

```expect
pass
```
