# A parameter-bounded composite returns beside the caller's retained neighbor

The summary packages exactly the prefix reserved at entry. The caller keeps
the adjacent cell and opens the returned packet before returning its full range.

```c filename=parameter_packet.c
void caller(int *p, int n) {
    package(p, n);
}
```

```click
resource packet(base: int32*, length: int32) {
    owns base[0..length];
}

verifying "parameter_packet.c";

extern void package(int32* p, int32 n) {
    requires 1 <= n and n <= 16;
    consumes uninitialized(p[0..n]);
    produces packet(p, n);
}

void caller(int32* p, int32 n) {
    requires 1 <= n and n <= 16;
    owns p[0..n + 1];
} by {
    step();
    unfold(packet(p, n));
    step();
}
```

```expect
pass
```
