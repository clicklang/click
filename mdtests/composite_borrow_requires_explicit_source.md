# A newly returned borrowing composite needs an explicit source

```c filename=unlabelled_cursor.c
void make_cursor(int *p);
void caller(int *p) { make_cursor(p); }
```

```click
resource cursor(p: int32*) {
    views *p;
}

verifying "unlabelled_cursor.c";

extern void make_cursor(int32* p) {
    views *p;
    produces cursor(p);
}

void caller(int32* p) {
    owns *p;
} by {
    step();
}
```

```expect
fail: needs an explicit borrow source declared with `from`
```
