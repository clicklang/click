# An interior call-result alias cannot be read after its allocation is freed

The helper returns an alias eight bytes into the allocation. Reading through
that alias after `free(p)` must be refused. The sibling control reads before
the free and verifies, establishing that the helper and store are accepted.

The current refusal is missing read authority at `return *q`, not a
deallocated-address diagnostic. This does not establish that the cached cell
was retired.

```c filename=free_interior_alias_probe.c
int32* interior(int32* p) { return p + 2; }

int32 probe() {
    int32* p = malloc(12);
    if (p == 0) { return 0; }
    p[0] = 1;
    p[1] = 2;
    p[2] = 3;
    int32* q = interior(p);
    *q = 7;
    free(p);
    return *q;
}
```

```click
verifying "free_interior_alias_probe.c";

int32* interior(int32* p) {
    views p[0..3];
    ensures result == p + 2;
}

int32 probe() {
    ensures result == 0 or result == 7;
}
```

```expect
fail: missing resource fact `views ((char *)q)[0..4]`
```
