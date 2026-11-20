# Loop exits that reach different states join through the loop's binders

A loop statement has one successor, so the exits joined into it must be
described by one state. The guard-false exit stands at the loop's own exit
state, where every local the body writes is abstract; this `break` leaves after
assigning `r`, so the two exits do not agree on `r`. A23 refused exactly this.

The join gives `r` one name after the loop. On the guard-false exit the
invariant gives `r == 0`. On the break exit the assignment gives `r == 1`.
Both exits establish `r == 0 or r == 1`, which the postcondition uses.

A claim stronger than the disjunction still fails. See
[`loop_body_break_exit_joined_state_rejected.md`](loop_body_break_exit_joined_state_rejected.md).

```c filename=assign_then_break.c
int32 assign_then_break(int32 n) {
    int32 i = n;
    int32 r = 0;

    while (i != 0) {
        r = 1;
        break;
    }
    return r;
}
```

```click
verifying "assign_then_break.c";

int32 assign_then_break(int32 n) {
    requires n >= 0;
    ensures result == 0 or result == 1;
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases i;
        invariant i >= 0;
        invariant r == 0;

        initialize by solve();
        maintain by {
            step();
            have r == 0 or r == 1 by known();
            step();
        }
        otherwise {
            have r == 0 or r == 1 by known();
        }
    }
    step();
    solve();
}
```

```expect
pass
```
