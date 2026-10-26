# `step_until` in a `branch` arm that falls through names the arm limit

A `branch` arm that does not return ends at the C `if`'s shared
continuation: `return 0;` runs after the arms join, not inside the `else`
arm. `step_until(function.exit)` there is refused naming that limit and what
to write instead, as `step()` past the end of an arm is
(`execute_branch_arm_stops_at_shared_continuation.md`). The same proof with
the `else` arm empty, or with a proof `if x < 0` before the C, verifies.

```c filename=sign.c
int32 sign(int32 x) {
    if (x < 0) {
        return 1;
    }
    return 0;
}
```

```click
verifying "sign.c";

int32 sign(int32 x) {
    ensures result == 0 or result == 1;
} by {
    branch {
        step_until(function.exit);
    } else {
        step_until(function.exit);
    }
}
```

```expect
fail: `step_until` cannot step past the end of this `branch` arm: an arm that does not return stops at the C `if`'s shared continuation
```
