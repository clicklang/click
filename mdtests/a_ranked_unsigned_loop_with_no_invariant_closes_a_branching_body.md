# A ranked unsigned loop with no invariant closes a branching body

The `uint32` form of
`a_ranked_loop_with_no_invariant_closes_a_branching_body.md`, with the guard
and the branch written `0u < state` and `1u < state`. The then-arm's decrease
is its own branch condition.

```c filename=a_ranked_unsigned_loop_with_no_invariant_closes_a_branching_body.c
int32 settle(uint32 state) {
    while (0u < state) {
        if (1u < state) {
            state = 1u;
        } else {
            state = 0u;
        }
    }
    return 0;
}
```

```click
verifying "a_ranked_unsigned_loop_with_no_invariant_closes_a_branching_body.c";

int32 settle(uint32 state) {
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
