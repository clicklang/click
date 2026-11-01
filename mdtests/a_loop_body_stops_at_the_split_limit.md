# A loop body stops at the implicit tail's split limit

With no written `preserve` proof, the loop closer splits at each C `if` of the
body, as a function's implicit tail does, so eleven sequential branches give
it 2,047 splits. Past 1,024 it stops and names the explicit join, as
`execute_stops_at_its_split_limit_on_sequential_branches.md` does for a
function body.

```c filename=a_loop_body_stops_at_the_split_limit.c
int32 f(int32 n, int32 a0, int32 a1, int32 a2, int32 a3, int32 a4, int32 a5, int32 a6, int32 a7, int32 a8, int32 a9, int32 a10) {
    int32 i;
    int32 x;
    i = 0;
    x = 0;
    while (i < n) {
        if (a0 > 0) { x = 1; }
        if (a1 > 0) { x = 1; }
        if (a2 > 0) { x = 1; }
        if (a3 > 0) { x = 1; }
        if (a4 > 0) { x = 1; }
        if (a5 > 0) { x = 1; }
        if (a6 > 0) { x = 1; }
        if (a7 > 0) { x = 1; }
        if (a8 > 0) { x = 1; }
        if (a9 > 0) { x = 1; }
        if (a10 > 0) { x = 1; }
        i = i + 1;
    }
    return 0;
}
```

```click
verifying "a_loop_body_stops_at_the_split_limit.c";

int32 f(int32 n, int32 a0, int32 a1, int32 a2, int32 a3, int32 a4, int32 a5, int32 a6, int32 a7, int32 a8, int32 a9, int32 a10) {
    requires 0 <= n;
    ensures result == 0;
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i and i <= n;
    }
    step();
    solve();
}
```

```expect
fail: split at more than 1024 C branches
```
