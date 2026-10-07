# A bare `branch` joins arms that end in different states

The `then` arm stores to `found` and the `else` arm does nothing, so the two
arms reach the statement after the `if` in different states. A `branch`
with no `ensuring` joins them all the same, keeping what both arms agree on:
`i` is untouched by either arm and is still known after the join, while
`found` is not. `ensuring { ... }` is what a proof adds to say more than
that about the state the arms meet in
([`a_written_branch_interface_carries_what_an_invariant_needs.md`](a_written_branch_interface_carries_what_an_invariant_needs.md)).

The function's result does not depend on `found`, so nothing more is needed.

```c filename=a_bare_branch_joins_arms_that_end_apart.c
int32 note(int32 x) {
    int32 i;
    int32 found;
    i = 7;
    found = 0;
    if (x == 3) {
        found = 1;
    }
    return i;
}
```

```click
verifying "a_bare_branch_joins_arms_that_end_apart.c";

int32 note(int32 x) {
    ensures result == 7;
} by {
    step();
    step();
    step();
    step();
    branch then {
        step();
    } else {
    }
    step();
    simp();
}
```

```expect
pass
```
