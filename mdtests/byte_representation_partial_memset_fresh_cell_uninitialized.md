# A partial `memset` of a fresh cell leaves it uninitialized

The same partial `memset` as `byte_representation_partial_memset_rejoins_cell.md`
on a fresh allocation. The caller's byte pieces are rejoined after the call,
so the load of `dst->x` holds the authority it needs and is refused for what
the cell contains: its two high bytes were never written.

```c filename=fresh_memset.c
void *malloc(unsigned long size);
void free(void *ptr);
void *memset(void *dest, int c, unsigned long n);
struct box { unsigned int x; };
int h(void) {
    struct box *dst = malloc(sizeof(struct box));
    if (dst == 0) { return -1; }
    memset((unsigned char *)(void *)dst, 0, 2);
    int out = (int)dst->x;
    free(dst);
    return out;
}
```

```click
verifying "fresh_memset.c";
int h() { ensures true; } by { execute(); simp(); }
```

```expect
fail: read of uninitialized storage
```
