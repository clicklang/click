# A consumed scalar transfer can accompany a borrowed return

The returned initialized cell keeps its checked consumed source even when
another return occurrence restores a borrowed cell.

```c filename=mixed_scalar_transfer.c
void caller(int *p, int *q) {
    reset_and_borrow(p, q);
}
```

```click
verifying "mixed_scalar_transfer.c";

extern void reset_and_borrow(int32* p, int32* q) {
    consumes uninitialized(p[0..1]);
    owns q[0..1];
    produces p[0..1];
}

void caller(int32* p, int32* q) {
    consumes uninitialized(p[0..1]);
    owns q[0..1];
    produces p[0..1];
} by {
    step();
    step();
}
```

```expect
pass
```
