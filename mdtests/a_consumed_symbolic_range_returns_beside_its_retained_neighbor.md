# A consumed symbolic range returns beside its retained neighbor

The summary returns the same parameter-bounded footprint that entry reserved.
The caller keeps the final cell while the call initializes the selected prefix.

```c filename=symbolic_transfer.c
void caller(int *p, int n) {
    reset(p, n);
}
```

```click
verifying "symbolic_transfer.c";

extern void reset(int32* p, int32 n) {
    requires 1 <= n and n <= 16;
    consumes uninitialized(p[0..n]);
    produces p[0..n];
}

void caller(int32* p, int32 n) {
    requires 1 <= n and n <= 16;
    owns p[0..n + 1];
} by {
    step();
    step();
}
```

```expect
pass
```
