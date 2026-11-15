# A consumed scalar returns beside its retained neighbor

A checked call consumes an uninitialized scalar and produces that same
scalar initialized. Its entry reservation supplies the ownership transfer
back into the residual frame, including when the original owner covered both
cells. The caller returns ownership of both cells after the call.

```c filename=scalar_transfer.c
void caller(int *p) {
    reset(p);
}
```

```click
verifying "scalar_transfer.c";

extern void reset(int32* p) {
    consumes uninitialized(p[0..1]);
    produces p[0..1];
}

void caller(int32* p) {
    owns p[0..2];
} by {
    step();
    step();
}
```

```expect
pass
```
