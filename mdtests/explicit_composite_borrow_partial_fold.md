# Refolding and consuming one piece leaves the other piece protected

```c filename=partial_borrowing_cursor.c
void package(int *p);
void drop_left(int *p);

void use(int *p) {
    package(p);
    drop_left(p);
    p[1] = 7;
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

extern void drop_left(int32* p) {
    consumes left(p);
}

void use(int32* p) {
    owns p[0..2];
    ensures p[1] == 7;
} by {
    step();
    unfold(pair(p));
    fold(left(p));
    step();
    step();
}
```

```expect
fail: missing resource fact `owns
```
