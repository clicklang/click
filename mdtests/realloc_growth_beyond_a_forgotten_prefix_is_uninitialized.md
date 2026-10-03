# realloc growth beyond a forgotten prefix is uninitialized

The negative next door to
`mdtests/realloc_keeps_a_forgotten_initialized_prefix_initialized.md`. The
old block's initialized bytes move to the new block, but only those: the
element `realloc` grows the allocation by was never written, so reading
`q[2]` is a read of uninitialized storage.

```c filename=realloc_growth_beyond_a_forgotten_prefix_is_uninitialized.c
void touch(int32* p) {
    p[0] = 7;
}

int32 grow() {
    int32* p;
    int32* q;
    int32 result;
    p = malloc(2 * sizeof(int32));
    if (p == 0) {
        return 0;
    }
    p[0] = 5;
    p[1] = 5;
    touch(p);
    q = realloc(p, 3 * sizeof(int32));
    if (q == 0) {
        free(p);
        return 0;
    }
    result = q[2];
    free(q);
    return result;
}
```

```click
verifying "realloc_growth_beyond_a_forgotten_prefix_is_uninitialized.c";

void touch(int32* p) {
    owns p[0..2];
} by auto;

int32 grow() {
    ensures result == result;
} by auto;
```

```expect
fail: read of uninitialized storage
```
