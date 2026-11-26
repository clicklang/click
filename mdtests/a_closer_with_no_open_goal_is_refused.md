# A closer with no open goal is refused

The companion of `closers_after_execution_close_a_resource_goal_first.md`
with an extra `all` closer. Once its source clauses and contract-closing
obligations are closed there is nothing left
for a closer to act on, and the extra closer is refused rather than silently
ignored.

```c filename=a_closer_with_no_open_goal_is_refused.c
int32 g(int32 p[]) {
    return 7;
}
```

```click
verifying "a_closer_with_no_open_goal_is_refused.c";

int32 g(int32 p[]) {
    owns p[0..1];
    ensures result == 7;
} by {
    step_until(function.exit);
    close();
    close();
    close(); close(); close();
    all { result == 7 => { close(); } true => { close(); } }
}
```

```expect
fail: `all` has no goal to close
```
