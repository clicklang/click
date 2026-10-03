# realloc keeps a forgotten initialized prefix initialized

A successful `realloc` preserves the old contents up to the smaller of the
old and new sizes (C11 7.22.3.5p2). The modeled `realloc` carried over the
old block's cached cells, and nothing else, so bytes that were written but
whose cached values a call had forgotten arrived uninitialized: reading
`q[1]` was refused as a read of uninitialized storage. The pending
reallocation now carries the old block's initialization record, cut at the
new size, so `q[1]` is an initialized element of unknown value.
`mdtests/realloc_growth_beyond_a_forgotten_prefix_is_uninitialized.md` and
`mdtests/realloc_shrink_cuts_a_forgotten_initialized_prefix.md` are the
negatives next door.

```c filename=realloc_keeps_a_forgotten_initialized_prefix_initialized.c
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
    result = q[1];
    free(q);
    return result;
}
```

```click
verifying "realloc_keeps_a_forgotten_initialized_prefix_initialized.c";

void touch(int32* p) {
    owns p[0..2];
} by auto;

int32 grow() {
    ensures result == result;
} by auto;
```

```expect
pass
```
