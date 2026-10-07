# A written `branch` interface carries what an invariant needs

The arms of the C `if` store different values to `x`, and the invariant
bounds `x`. Joining the arms keeps what both agree on, which says nothing
about `x`, so the automatic loop closer cannot close this loop
([`an_automatically_closed_loop_keeps_only_what_its_branches_agree_on.md`](an_automatically_closed_loop_keeps_only_what_its_branches_agree_on.md)).

Written out, the `branch` says what both arms establish: `ensuring` exports
the bound on `x`, each arm proves it from the value it stored, and the one
path that leaves the `if` carries it to the back edge. The rest of the body
is still checked once.

```c filename=a_written_branch_interface_carries_what_an_invariant_needs.c
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
verifying "a_written_branch_interface_carries_what_an_invariant_needs.c";

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
        initialize by simp;
        preserve by {
            branch ensuring {
                fact 0 <= x and x <= 1;
            } then {
                step();
            } else {
                step();
            }
            step();
            close_invariants();
        }
    }
    step();
    simp();
}
```

```expect
pass
```
