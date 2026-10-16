# A bare `transport` inside a `have` is refused by the premise planner

The write `p[i] = 7` may store to `p[1]`, so the entry fact `p[1] == 6` does
not survive it. Neither source-local candidate checks, and the premise planner
runs over the frontier the `have` was opened on. Its refusal is the answer,
the same one the bare `transport` gets between top-level steps, not a report
that the `have` lost the execution frontier.

```c filename=w.c
int32 put(int32 p[3], int32 i) {
    p[i] = 7;
    return 0;
}
```

```click
verifying "w.c";
int32 put(int32 p[3], int32 i) {
    owns p[0..3];
    requires 1 <= i and i < 3;
    requires p[1] == 6;
    ensures true;
} by {
    step();
    have p[1] == 6 by {
        transport(at(function.entry, p[1] == 6), p[1] == 6);
    }
    execute();
    simp();
}
```

```expect
fail: could not make fact transport premises explicit
```
