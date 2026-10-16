# An integer round trip does not retype a pointer object

The original object is an `int *` cell. Encoding its address in an integer
and decoding it as `long **` must retain that original class, so the
incompatible `long *` access is refused.

```c filename=pointers.c
int ptrs(int **a) {
    uint64 v = (uint64)a;
    long **b = (long **)v;
    return *b == 0;
}
```

```click
verifying "pointers.c";
int32 ptrs(int32 **a) {
    views a[0..1];
    ensures true;
} by { execute(); }
```

```expect
fail: an object of type `int *` accessed through an lvalue of type `long *`
```
