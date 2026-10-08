# `close_invariants by` takes one tactic call without braces

A one-step body after `close_invariants by` is written as the call alone,
`close_invariants by normalize();`, as it is after `have` and `ensures`.
It is the body `{ normalize(); }`. The bare `by simp;` form is in
`diverges_perpetual_loop.md`.

```c filename=close_invariants_takes_one_tactic_call_without_braces.c
int32 wait_for_zero(int32 x) {
    while (x != 0) {
    }
    return 1;
}
```

```click
verifying "close_invariants_takes_one_tactic_call_without_braces.c";

int32 wait_for_zero(int32 x) diverges {
    ensures result == 1;
} by {
    loop diverges {
        invariant x == x;
        initialize by simp;
        preserve by {
            step();
            close_invariants by normalize();
        }
    }
    step();
    simp();
}
```

```expect
pass
```
