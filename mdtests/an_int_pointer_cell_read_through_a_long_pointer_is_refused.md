# An `int *` cell read through a `long *` lvalue is refused

GCC at `-O2` assumes an `int *` object is never read as a `long *` (the
`ptrs` probe in `design/effective-types.md`). An `int **` parameter's
pointee is an `int *` object, so after a `void *` round trip a `long **`
read of it is refused.

```c filename=pointers.c
int ptrs(int **a) {
    void *v = a;
    long **b = v;
    return *b == 0;
}
```

```click
verifying "pointers.c";

int32 ptrs(int32 **a) {
    views a[0..1];
    ensures true;
} by {
    execute();
}
```

```expect
fail: an object of type `int *` accessed through an lvalue of type `long *`
```
