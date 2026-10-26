# A chained region ends in an assignment or a read

`.assignment(x, j)` and `.read(j)` end a chained region, as `.call(f, j)`
does: each counts, from zero, the statement's own atomic regions that assign
local `x` or load from memory. `step_until` stops before that region, and
`at` reads its states. Here `statement(2).statement(1).read(0)` is the load
`x = (int32)*p;` inside the `if`, and `statement(2).statement(2).assignment(y,
0)` is the store `y = 2;` after it.

```c filename=chained_kinds.c
int32 loaded(const uint8* p) {
    int32 x = 0;
    int32 y = 0;
    if (x == 0) {
        y = 1;
        x = (int32)*p;
        y = 2;
    }
    return x + y;
}
```

```click
verifying "chained_kinds.c";
int32 loaded(const uint8* p) {
    views p[0..1];
    ensures 2 <= result and result <= 257;
} by {
    step_until(statement(2).statement(1).read(0));
    step();
    have 0 <= x and x <= 255;
    step_until(statement(2).statement(2).assignment(y, 0));
    have at(statement(2).statement(1).read(0).entry, y) == 1 by solve();
}
```

```expect
pass
```
