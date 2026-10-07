# An automatically closed loop keeps only what its branches agree on

The arms of the C `if` store different values to `x`, and the increment
follows. The loop closer joins the arms, and the one path that continues
knows what both arms agree on. They do not agree on `x`, so the invariant
`0 <= x and x <= 1` cannot be closed and the loop is refused.

The closer does not fall back to walking the rest of the body once per arm
to recover it. What each arm establishes about `x` is said by writing the
body with `branch ensuring { ... }`
([`a_written_branch_interface_carries_what_an_invariant_needs.md`](a_written_branch_interface_carries_what_an_invariant_needs.md)).

```c filename=an_automatically_closed_loop_keeps_only_what_its_branches_agree_on.c
int32 flip(int32 n) {
    int32 i;
    int32 x;
    i = 0;
    x = 0;
    while (i < n) {
        if (i > 3) {
            x = 1;
        } else {
            x = 0;
        }
        i = i + 1;
    }
    return x;
}
```

```click
verifying "an_automatically_closed_loop_keeps_only_what_its_branches_agree_on.c";

int32 flip(int32 n) {
    requires 0 <= n;
    requires n <= 8;
    ensures 0 <= result and result <= 1;
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i and i <= n;
        invariant 0 <= x and x <= 1;
    }
    step();
    simp();
}
```

```expect
fail: The automatic loop closer joined the arms of a C `if`
```
