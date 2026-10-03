# A ranked loop with no invariant refuses an arm that does not descend

The negative counterpart of
`a_ranked_loop_with_no_invariant_closes_a_branching_body.md`: the then-arm
leaves `state` unchanged, so the measure does not decrease on that arm and the
loop is refused as an ordinary unclosed back edge.

```c filename=a_ranked_loop_with_no_invariant_refuses_an_arm_that_does_not_descend.c
int32 settle(int32 state) {
    while (state > 0) {
        if (state > 1) {
            state = state;
        } else {
            state = 0;
        }
    }
    return 0;
}
```

```click
verifying "a_ranked_loop_with_no_invariant_refuses_an_arm_that_does_not_descend.c";

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
fail: `state < state` remained open
```
