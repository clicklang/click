# A partial owned call leaves abutting byte pieces unjoined

Soundness: not soundness. Both paths refuse the read; only the reason
differs.

After a call that owns the first two bytes of a four-byte `unsigned int` cell
the caller owns, the caller keeps `owns dst[0..2]` and `owns dst[2..4]` as
separate byte pieces, and a later typed load of the whole cell is refused as
`missing resource fact `views *dst``, although the function owns all four
bytes. Whether the pieces are rejoined depends on an unrelated event: when the
same call also lends another range under `views`, as `memcpy` does since it
reads its source under `views`, the loan's return rejoins the pieces and the
same load is refused for the right reason, `read of uninitialized storage`
(`mdtests/byte_representation_partial_copy_frontier.md`). The invariant
violated: resource normalization after a call does not depend on whether the
call also borrowed something.

## Reproduction

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

Observed on 2026-10-16 on master `40d34180` plus the M3 `memcpy`/`memcmp` contract change, which does not touch this path: `missing resource fact
`views *dst`` at `int out = (int)dst->x;`. `click verify --trace-proof h`
shows `owns memory(dst[Int32:2..4], stride=1)` and
`owns memory(dst[Int32:0..2], stride=1)` held separately after the call, in
the call's retained caller-owned frame.

## Acceptance

- The pieces are rejoined after the call whether or not it borrowed, so the
  load is decided by the cell's contents after the call, here refused as a
  read that does not fit the cell or as uninitialized, not for missing
  authority the function holds.
- The reproduction is kept as an mdtest with the corrected expectation.
- Rejoining stays local to the blocks the call touched.
