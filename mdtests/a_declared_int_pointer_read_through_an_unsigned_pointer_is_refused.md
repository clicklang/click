# A declared `int *` read through an `unsigned *` lvalue is refused

A local `int *` whose address is taken records its type on its block. A
pointer class keeps its pointee's signedness, so reading it through an
`unsigned **` is refused.

```c filename=pointers.c
int local_ptr(void) {
    int x = 3;
    int *p = &x;
    void *v = &p;
    unsigned **q = v;
    return **q;
}
```

```click
verifying "pointers.c";

int32 local_ptr() {
    ensures result == 3;
} by {
    execute();
    simp();
}
```

```expect
fail: an object of type `int *` accessed through an lvalue of type `unsigned int *`
```
