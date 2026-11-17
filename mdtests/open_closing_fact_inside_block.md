# An in-block fact can restore an opened resource

A `have` at the end of an `open` block gives the closing fold its body fact.
The first scope closes before the next C statement. The second reaches
function exit and proves the closing fact in the outcome state.

```c filename=open_by.c
void set(int32* p, int32* q, int32 x) { p[0] = x; q[0] = 1; }
void set_last(int32* p, int32 x) { p[0] = x; }
```

```click
resource cell(p: int32*) { owns p[0..1]; fact p[0] > 0 or p[0] < -1; }
verifying "open_by.c";
void set(int32* p, int32* q, int32 x) {
    requires x > 0;
    owns cell(p);
    owns q[0..1];
} by {
    open(cell(p)) {
        step();
        have p[0] > 0 or p[0] < -1 by { solve(); }
    }
}
void set_last(int32* p, int32 x) {
    requires x > 0;
    owns cell(p);
} by {
    open(cell(p)) {
        step_until(function.exit);
        have p[0] > 0 or p[0] < -1 by { solve(); }
    }
    solve();
}
```

```expect
pass
```
