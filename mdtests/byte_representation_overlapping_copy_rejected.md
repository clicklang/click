# An overlapping copy is refused by the disjoint owned and viewed ranges

The `memcpy` contract owns its destination and views its source, and the
`owns` and `views` clauses of one contract are disjoint: it is a
non-overlapping copy primitive. Copying within one allocation with
overlapping source and destination would lend `buf[0..8]` as a view while
lending `buf[2..10]` as owned, so the call is refused. No byte moves and no
representation is established.

```c filename=overlapping_memcpy.c
void *malloc(unsigned long size);
void free(void *ptr);
void *memcpy(void *dest, const void *src, unsigned long n);
int f(void) {
    unsigned char *buf = malloc(16);
    if (buf == 0) { return -1; }
    memcpy(buf + 2, buf, 8);
    free(buf);
    return 0;
}
```

```click
verifying "overlapping_memcpy.c";

int f() {
    ensures result == 0 or result == -1;
} by {
    execute();
    simp();
}
```

```expect
fail: a required resource overlaps a live borrowed footprint
```
