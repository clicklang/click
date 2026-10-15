# `open(r) { ... } by { ... }` proves the closing fold's open body fact

Closing an `open` scope folds its resource again. When that fold leaves a body
fact open, the `by` after the block proves it, as `fold(r) by { ... }` proves
a fold's. The scope in `set` closes before the next statement; the one in
`set_last` reaches function exit, so its close is checked after execution.
The body fact is a disjunction, which the fold's exact checks do not settle.

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
    open(cell(p)) { step(); } by { simp(); }
    execute(); simp();
}
void set_last(int32* p, int32 x) {
    requires x > 0;
    owns cell(p);
} by {
    open(cell(p)) { execute(); } by { simp(); }
    simp();
}
```

```expect
pass
```
