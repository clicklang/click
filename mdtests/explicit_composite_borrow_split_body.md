# A composite reuses one hold for all its viewed pieces

```c filename=split_borrowing_cursor.c
void package(int *p);
void drop_pair(int *p);

void use(int *p) {
    package(p);
    drop_pair(p);
    p[0] = 7;
}
```

```click
resource pair(p: int32*) {
    views p[0..1];
    views p[1..2];
}

verifying "split_borrowing_cursor.c";

extern void package(int32* p) {
    views p[0..2] as input;
    produces pair(p) from input;
}

extern void drop_pair(int32* p) {
    consumes pair(p);
}

void use(int32* p) {
    owns p[0..2];
    ensures p[0] == 7;
} by {
    step();
    unfold(pair(p));
    fold(pair(p));
    step_until(function.exit);
    solve();
}
```

```expect
pass
```
