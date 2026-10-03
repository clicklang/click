# The body of `do ... while (0)` runs once

The loop's false condition does not let a proof skip the body.

```c filename=c_do_while_body_runs_before_its_condition.c
int32 run(int32 v) {
    do {
        v = 3;
    } while (0);
    return v;
}
```

```click
verifying "c_do_while_body_runs_before_its_condition.c";

int32 run(int32 v) {
    ensures result == v by auto;
}
```

```expect
fail: left side evaluated to 3, right side evaluated to v
```
