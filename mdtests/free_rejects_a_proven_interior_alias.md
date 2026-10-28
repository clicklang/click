# Equality with an interior address does not authorize free

```c filename=free_interior_base.c
void dispose(int32* p, int32* q) { free(q); }
```

```click
verifying "free_interior_base.c";
void dispose(int32* p, int32* q) {
    consumes allocation(p, 8);
    consumes p[0..2];
    requires q == p + 1;
} by { step(); }
```

```expect
fail: cannot free
```
