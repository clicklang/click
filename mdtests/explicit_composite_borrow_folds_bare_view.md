# A fold moves the hold of a returned bare view into the composite

```c filename=fold_bare_view.c
void lend(int *p);
void drop(int *p);

void use(int *p) {
    lend(p);
    drop(p);
    *p = 7;
}
```

```click
resource cursor(p: int32*) {
    views *p;
}

verifying "fold_bare_view.c";

extern void lend(int32* p) {
    views *p as input;
    produces view(*p) from input;
}

extern void drop(int32* p) {
    consumes cursor(p);
}

void use(int32* p) {
    owns *p;
    ensures *p == 7;
} by {
    step();
    fold(cursor(p));
    step_until(function.exit);
    solve();
}
```

```expect
pass
```
