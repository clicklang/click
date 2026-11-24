# the automatic preservation planner ranks a body that ends in a branch

Arithmetic search expands to ordinary proof steps, with the selected premises
stated explicitly in `close() using { ... }`.

```c filename=loop_ranks_a_body_ending_in_a_branch.c
int32 flip_to_n(int32 n) {
    int32 i = 0;
    int32 parity = 0;

    while (i < n) {
        i = i + 1;
        if (parity < 1) {
            parity = 1;
        } else {
            parity = 0;
        }
    }
    return parity;
}
```

```click
verifying "loop_ranks_a_body_ending_in_a_branch.c";

int32 flip_to_n(int32 n) {
    ensures result >= 0;
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases n - i;
        invariant i >= 0;
        invariant parity >= 0 and parity <= 1;
        initialize by solve();
    }
    step();
    solve();
}
```

```expect
pass
```
