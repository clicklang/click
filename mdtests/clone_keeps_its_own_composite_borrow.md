# A clone gets its own hold on the borrow carried by the source cursor

```c filename=clone_borrow.c
void pack(int *p);
void duplicate(int *p);
void drop(int id, int *p);

void use(int *p) {
    pack(p);
    duplicate(p);
    drop(1, p);
    drop(2, p);
    *p = 7;
}
```

```click
resource cursor(id: int32, p: int32*) { views *p; }

verifying "clone_borrow.c";

extern void pack(int32* p) {
    views *p as input;
    produces cursor(1, p) from input;
}

extern void duplicate(int32* p) {
    views cursor(1, p) as input;
    produces cursor(2, p) from input;
}

extern void drop(int32 id, int32* p) {
    consumes cursor(id, p);
}

void use(int32* p) {
    owns *p;
    ensures *p == 7;
} by {
    step_until(function.exit);
    solve();
}
```

```expect
pass
```
