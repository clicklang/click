# Dropping a cursor restores access to its automatic-storage backing

```c filename=local_borrowing_cursor.c
void package(int *p);
void drop(int *p);

int use(void) {
    int local = 0;
    package(&local);
    drop(&local);
    local = 7;
    return local;
}
```

```click
resource cursor(p: int32*) {
    views *p;
}

verifying "local_borrowing_cursor.c";

extern void package(int32* p) {
    views *p as input;
    produces cursor(p) from input;
}

extern void drop(int32* p) {
    consumes cursor(p);
}

int32 use() {
    ensures result == 7;
} by {
    step_until(function.exit);
    solve();
}
```

```expect
pass
```
