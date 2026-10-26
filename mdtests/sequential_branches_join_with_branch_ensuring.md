# Sequential branches join with `branch ensuring`

The implicit tail follows each arm of a C `if` to function exit, so
sequential branches multiply its paths
(`execute_stops_at_its_split_limit_on_sequential_branches.md`). A
`branch ensuring` at each branch joins its two arms right after the `if`,
keeping the facts the interface states, so the proof has one path between
branches and its work is linear in their number. Each arm proves the
interface facts with a `have`.

```c filename=joined_branches.c
int32 f(int32 x, int32 a0, int32 b0, int32 a1, int32 b1, int32 a2, int32 b2, int32 a3, int32 b3) {
    if (a0 >= b0) { x = x + 1; }
    if (a1 >= b1) { x = x + 1; }
    if (a2 >= b2) { x = x + 1; }
    if (a3 >= b3) { x = x + 1; }
    return x;
}
```

```click
verifying "joined_branches.c";

int32 f(int32 x, int32 a0, int32 b0, int32 a1, int32 b1, int32 a2, int32 b2, int32 a3, int32 b3) {
    requires x >= 0 and x < 1000;
    ensures result >= 0 by {
        branch ensuring {
            fact x >= 0;
            fact x <= 1000;
        } then {
            step();
            have x >= 0;
            have x <= 1000;
        } else {
            have x >= 0;
            have x <= 1000;
        }
        branch ensuring {
            fact x >= 0;
            fact x <= 1001;
        } then {
            step();
            have x >= 0;
            have x <= 1001;
        } else {
            have x >= 0;
            have x <= 1001;
        }
        branch ensuring {
            fact x >= 0;
            fact x <= 1002;
        } then {
            step();
            have x >= 0;
            have x <= 1002;
        } else {
            have x >= 0;
            have x <= 1002;
        }
        branch ensuring {
            fact x >= 0;
            fact x <= 1003;
        } then {
            step();
            have x >= 0;
            have x <= 1003;
        } else {
            have x >= 0;
            have x <= 1003;
        }
        step();
        solve();
    }
}
```

```expect
pass
```
