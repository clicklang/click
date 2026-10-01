# realloc shrink cuts a forgotten initialized prefix

The second negative next door to
`mdtests/realloc_keeps_a_forgotten_initialized_prefix_initialized.md`. The
old block's initialization record is cut at the new size: shrinking to one
element keeps only `q[0]` initialized, so growing back to three elements
leaves `r[1]` as never-written storage, although the first block had
initialized it. Reading it is a read of uninitialized storage.

```c filename=realloc_shrink_cuts_a_forgotten_initialized_prefix.c
void touch(int32* p) {
    p[0] = 7;
}

int32 shrink_then_grow() {
    int32* p;
    int32* q;
    int32* r;
    int32 result;
    p = malloc(2 * sizeof(int32));
    if (p == 0) {
        return 0;
    }
    p[0] = 5;
    p[1] = 5;
    touch(p);
    q = realloc(p, sizeof(int32));
    if (q == 0) {
        free(p);
        return 0;
    }
    r = realloc(q, 3 * sizeof(int32));
    if (r == 0) {
        free(q);
        return 0;
    }
    result = r[1];
    free(r);
    return result;
}
```

```click
verifying "realloc_shrink_cuts_a_forgotten_initialized_prefix.c";

void touch(int32* p) {
    owns p[0..2];
} by auto;

int32 shrink_then_grow() {
    ensures result == result;
} by auto;
```

```expect
fail: read of uninitialized storage
```
