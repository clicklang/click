# `step_until` runs inside a `branch` arm

An arm of a `branch` is a path of its own, and `step_until` steps along it as
anywhere else: here each arm returns, so `step_until(function.exit)` runs it
to its exit, and the proof continues on that path, where `result` is the
arm's returned value.

```c filename=step_until_runs_inside_a_branch_arm.c
int32 clamp(int32 x) {
    if (x > 10) {
        return 10;
    } else {
        return x;
    }
}
```

```click
verifying "step_until_runs_inside_a_branch_arm.c";

int32 clamp(int32 x) {
    ensures result <= 10;
} by {
    branch {
        step_until(function.exit);
        have result == 10;
    } else {
        step_until(function.exit);
        have result == x;
    }
}
```

```expect
pass
```
