# An interior call-result alias can be read before its allocation is freed

Positive control for `an_interior_call_alias_cannot_be_read_after_free.md`: save the value while
the allocation is live, free it, and return the saved integer.

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
    int32 result = *q;
    free(p);
    return result;
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
pass
```
