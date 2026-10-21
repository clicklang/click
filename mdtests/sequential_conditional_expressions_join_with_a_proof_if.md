# Sequential conditional expressions join with a proof `if`

A `?:` splits `execute()`'s paths inside one statement, so a function of
sequential conditional expressions gives it `2^n` paths, as sequential C
`if`s do (`sequential_branches_join_with_branch_ensuring.md`). `branch` needs
a C `if`; here a proof `if` on each condition, with an `ensuring` interface,
decides the expression in each arm and joins the arms after the statement,
so the proof stays linear in the number of expressions.

```c filename=joined_conditionals.c
int32 f(int32 x, int32 a0, int32 b0, int32 a1, int32 b1, int32 a2, int32 b2, int32 a3, int32 b3) {
    x = (a0 < b0) ? x : x + 1;
    x = (a1 < b1) ? x : x + 1;
    x = (a2 < b2) ? x : x + 1;
    x = (a3 < b3) ? x : x + 1;
    return x;
}
```

```click
verifying "joined_conditionals.c";

int32 f(int32 x, int32 a0, int32 b0, int32 a1, int32 b1, int32 a2, int32 b2, int32 a3, int32 b3) {
    requires x >= 0 and x < 1000;
    ensures result >= 0 by {
        if a0 < b0 ensuring {
            fact x >= 0;
            fact x <= 1000;
        } then {
            step();
            have x >= 0;
            have x <= 1000;
        } else {
            step();
            have x >= 0;
            have x <= 1000;
        }
        if a1 < b1 ensuring {
            fact x >= 0;
            fact x <= 1001;
        } then {
            step();
            have x >= 0;
            have x <= 1001;
        } else {
            step();
            have x >= 0;
            have x <= 1001;
        }
        if a2 < b2 ensuring {
            fact x >= 0;
            fact x <= 1002;
        } then {
            step();
            have x >= 0;
            have x <= 1002;
        } else {
            step();
            have x >= 0;
            have x <= 1002;
        }
        if a3 < b3 ensuring {
            fact x >= 0;
            fact x <= 1003;
        } then {
            step();
            have x >= 0;
            have x <= 1003;
        } else {
            step();
            have x >= 0;
            have x <= 1003;
        }
        step();
        simp();
    }
}
```

```expect
pass
```
