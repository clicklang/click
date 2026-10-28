# Retiring an alias retires the allocation itself

```c filename=free_alias_twice.c
void dispose(int32* p, int32* q) { free(q); free(p); }
```

```click
verifying "free_alias_twice.c";
void dispose(int32* p, int32* q) {
    consumes allocation(p, 4);
    consumes p[0..1];
    requires q == p;
} by { step(); step(); }
```

```expect
fail: cannot free an allocation whose lifetime has already ended
```
