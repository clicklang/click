# A refold must move all the pieces that share a borrow hold

```c filename=partial_borrowing_cursor.c
void package(int *p);

void use(int *p) {
    package(p);
    p[0] = 7;
}
```

```click
resource left(p: int32*) {
    views p[0..1];
}

resource pair(p: int32*) {
    views p[0..1];
    views p[1..2];
}

verifying "partial_borrowing_cursor.c";

extern void package(int32* p) {
    views p[0..2] as input;
    produces pair(p) from input;
}

void use(int32* p) {
    owns p[0..2];
    ensures p[0] == 7;
} by {
    step();
    unfold(pair(p));
    fold(left(p));
}
```

```expect
fail: `fold` must move every viewed piece sharing this borrow hold
```
