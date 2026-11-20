# A `break` in a loop body is one of the loop's exits

The `loop` tactic certifies one body iteration. A path that ends in `break`
does not reach the back edge and is not asked to: it is an *exit*. The
invariants are not closed on it, no measure is required to decrease on it, and
its proof contributes to the loop's successor beside the guard-false exit
and every other `break`. A fact established at each exit can be used after
the loop.

`break_once` is the smallest case: the loop leaves either because `i > 0`
failed or because the body broke while `i > 0` held. Both exits stand at the
loop's own exit state, so the invariant `i >= 0` suffices for the result. A stronger claim such as
`result == 0` fails
([`loop_body_break_exit_claim_rejected.md`](loop_body_break_exit_claim_rejected.md)).

`stop_at` is the shape of Linux's `__rb_insert`: `while (true)`, which has no
guard-false exit at all, with every way out a `break` inside an `if`. The
successor is the join of the two `break` exits. Each exit proves
`i == 3 or i == 0` and the post-loop claim uses it.

Every loop here is ranked by `decreases i;`. A `break` path owes no decrease,
so `break_once` proves nothing about its measure; `stop_at` has one path that
does reach the back edge, and its `0 < i` comes from the C `if` that path
declined, which the closer names beside the invariants
([`the_back_edge_cites_a_branch_condition.md`](the_back_edge_cites_a_branch_condition.md)).

A `break` path whose state differs from the loop's other exits — one that
assigns or stores before leaving — is described through the loop's binders and
one fresh name per component the exits disagree about, with the disjunction of
what each exit said about them; see
[`loop_body_break_exit_joined_state.md`](loop_body_break_exit_joined_state.md).

```c filename=break_once.c
int32 break_once(int32 n) {
    int32 i = n;

    while (i > 0) {
        break;
    }
    return i;
}
```

```c filename=stop_at.c
int32 stop_at(int32 n) {
    int32 i = n;

    while (true) {
        if (i == 3) {
            break;
        }
        if (i == 0) {
            break;
        }
        i = 0;
    }
    return i;
}
```

`break_once_automatically` is `break_once` with both phases omitted: the
automation the `loop` keyword owns walks the body's `break` path itself, so an
exit needs no written proof.

```c filename=break_once_automatically.c
int32 break_once_automatically(int32 n) {
    int32 i = n;

    while (i > 0) {
        break;
    }
    return i;
}
```

`stop_at_automatically` uses the same C control flow. The preservation
proof follows the two nested C branches and states the same exit fact
before each `break`. The post-loop claim uses that fact after the join.

```c filename=stop_at_automatically.c
int32 stop_at_automatically(int32 n) {
    int32 i = n;

    while (true) {
        if (i == 3) {
            break;
        }
        if (i == 0) {
            break;
        }
        i = 0;
    }
    return i;
}
```

```click
verifying "break_once.c";
verifying "stop_at.c";
verifying "break_once_automatically.c";
verifying "stop_at_automatically.c";

int32 break_once(int32 n) {
    requires n >= 0;
    ensures result >= 0;
} by {
    step();
    step();
    loop {
        decreases i;
        invariant i >= 0;

        initialize by solve();
        maintain by {
            step();
        }
    }
    step();
    solve();
}

int32 stop_at(int32 n) {
    requires n >= 0;
    ensures result == 3 or result == 0;
} by {
    step();
    step();
    loop {
        decreases i;
        invariant i >= 0;

        initialize by solve();
        maintain by {
            if i == 3 {
                step();
                have i == 3 or i == 0 by known();
                step();
            } else {
                step();
                step();
                if i == 0 {
                    step();
                    have i == 3 or i == 0 by known();
                    step();
                } else {
                    step();
                    step();
                    step();
                }
            }
        }
    }
    step();
    solve();
}

int32 break_once_automatically(int32 n) {
    requires n >= 0;
    ensures result >= 0;
} by {
    step();
    step();
    loop {
        decreases i;
        invariant i >= 0;
    }
    step();
    solve();
}

int32 stop_at_automatically(int32 n) {
    requires n >= 0;
    ensures result == 3 or result == 0;
} by {
    step();
    step();
    loop {
        decreases i;
        invariant i >= 0;

        initialize by solve();
        maintain by {
            if i == 3 {
                step();
                have i == 3 or i == 0 by known();
                step();
            } else {
                step();
                step();
                if i == 0 {
                    step();
                    have i == 3 or i == 0 by known();
                    step();
                } else {
                    step();
                    step();
                    step();
                }
            }
        }
    }
    step();
    solve();
}
```

```expect
pass
```
