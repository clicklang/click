# Dropping one cursor leaves the other cursor’s borrow active

```c filename=remaining_borrowing_cursor.c
void package(int *p);
void drop(int id, int *p);

void use(int *p) {
    package(p);
    drop(1, p);
    *p = 7;
    drop(2, p);
}
```

```click
resource cursor(id: int32, p: int32*) {
    views *p;
}

verifying "remaining_borrowing_cursor.c";

extern void package(int32* p) {
    views *p as input;
    produces cursor(1, p) from input;
    produces cursor(2, p) from input;
}

extern void drop(int32 id, int32* p) {
    consumes cursor(id, p);
}

void use(int32* p) {
    owns *p;
    ensures *p == 7;
} by {
    step();
    unfold(cursor(1, p));
    fold(cursor(1, p));
    step();
    step();
}
```

```expect
fail: write ownership required
```
