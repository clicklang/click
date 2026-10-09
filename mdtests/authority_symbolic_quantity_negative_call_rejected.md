# An implicit quantity guard remains an obligation at the caller

This call regression exercises the shared quantity guard directly;
calls with symbolic batches remain a separate unsupported
transfer capability.

```c filename=negative_quantity.c
void inspect(int32* pool, int32 n) {}
void caller(int32* pool) { inspect(pool, -1); }
```

```click
resource slot(pool: int32*) {}
verifying "negative_quantity.c";
void inspect(int32* pool, int32 n) {
    owns n of slot(pool);
    ensures 0 <= n;
} by {
    execute(); simp();
}
void caller(int32* pool) {
    ensures 0 == 0;
} by {
    execute(); simp();
}
```

```expect
fail: declared resource quantity is not known nonnegative
```
