# A ranked loop with no invariant closes a branching body

The loop declares a measure and no invariant, and its body is a two-armed
`if` that reaches the back edge on both arms. Each arm's decrease follows from
the guard and that arm's branch condition.

The `loop` step proves the back edge per arm and then steps the loop through
the rule it just verified. A loop whose only annotation was `decreases` used to
be executed again from scratch at that point instead, so the back-edge
conditions already proved came back as missing prerequisites.

```c filename=a_ranked_loop_with_no_invariant_closes_a_branching_body.c
int32 settle(int32 state) {
    while (state > 0) {
        if (state > 1) {
            state = 1;
        } else {
            state = 0;
        }
    }
    return 0;
}
```

```click
verifying "a_ranked_loop_with_no_invariant_closes_a_branching_body.c";

int32 settle(int32 state) {
    ensures result == 0;
} by {
    loop {
        decreases state;
    }
    execute();
    simp();
}
```

```expect
pass
```
