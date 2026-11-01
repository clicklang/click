# An automatically closed loop closes each arm of its C `if`

The arms of the C `if` store different values to `x`, and the increment
follows. With no written `preserve` proof, the loop closer walks the body as a
function's implicit tail walks a function: it splits at the `if`, runs each
arm on through the increment to the back edge, and closes the invariants on
each path with what that arm established. Each arm sets `x` to 0 or 1, so
`0 <= x and x <= 1` closes on both.

Splitting multiplies paths at sequential `if`s, under the implicit tail's
split limit
([`a_loop_body_stops_at_the_split_limit.md`](a_loop_body_stops_at_the_split_limit.md));
`branch ensuring { ... }` joins an `if` explicitly
([`a_written_branch_interface_carries_what_an_invariant_needs.md`](a_written_branch_interface_carries_what_an_invariant_needs.md)).

```c filename=an_automatically_closed_loop_closes_each_branch_arm.c
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
verifying "an_automatically_closed_loop_closes_each_branch_arm.c";

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
    solve();
}
```

```expect
pass
```
