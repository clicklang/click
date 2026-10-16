# A partial owned call rejoins the cell's byte pieces

`memset` owns the first two bytes of the four-byte `unsigned int` cell. After
it returns, the caller's two byte pieces are rejoined, as they are when the
call also lends a view (`byte_representation_partial_copy_frontier.md`), so
the typed load of `dst->x` is decided by the cell's contents rather than by
missing authority. Every byte is initialized here, the high bytes by the store
of `7u` and the low ones by `memset`, so the load is defined; its value is not
fixed by any fact, so `result == 7` would not be proved.
`byte_representation_partial_memset_fresh_cell_uninitialized.md` is the same
call on a fresh allocation.

```c filename=partial_memset.c
void *malloc(unsigned long size);
void free(void *ptr);
void *memset(void *dest, int c, unsigned long n);
struct box { unsigned int x; };
int h(void) {
    struct box *dst = malloc(sizeof(struct box));
    if (dst == 0) { return -1; }
    dst->x = 7u;
    memset((unsigned char *)(void *)dst, 0, 2);
    int out = (int)dst->x;
    free(dst);
    return out;
}
```

```click
verifying "partial_memset.c";
int h() { ensures true; } by { execute(); simp(); }
```

```expect
pass
```
