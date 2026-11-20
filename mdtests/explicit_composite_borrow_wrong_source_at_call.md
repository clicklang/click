# A call names the returned composite and both views when the named source misses

```c filename=wrong_cursor_call.c
void package(int *p, int *q);

void use(int *p, int *q) {
    package(p, q);
}
```

```click
resource cursor(p: int32*) {
    views *p;
}

verifying "wrong_cursor_call.c";

extern void package(int32* p, int32* q) {
    views *p;
    views *q as source;
    produces cursor(p) from source;
}

void use(int32* p, int32* q) {
    owns *p;
    owns *q;
} by {
    step();
}
```

```expect
fail: cannot produce `cursor(p)` as a borrow. The selected input `views q[0]` does not establish coverage of `views p[0]`
```
