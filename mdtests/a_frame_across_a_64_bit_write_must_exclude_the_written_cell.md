# A frame across a 64-bit write must exclude the written cell

The contract of `a_frame_holds_across_a_write_at_a_64_bit_index.md` with
`k != i` dropped from the frame. It then claims the written element is
unchanged too, which is false when `v` differs from the old value, so the
proof is refused.

```c filename=a_frame_across_a_64_bit_write_must_exclude_the_written_cell.c
struct E { unsigned long v; };
struct S { int *p; struct E e; };
int *at(const struct S *s, unsigned long i) { return s->p + i; }
int set_at(struct S *s, unsigned long i, int v) { int *e = at(s, i); *e = v; return *e; }
```

```click
verifying "a_frame_across_a_64_bit_write_must_exclude_the_written_cell.c";
int32* at(const struct S* s, uint64 i) {
    views s->p;
    views s->e.v;
    views s->p[0..s->e.v];
    requires i < s->e.v;
    ensures result == s->p + i;
} by { execute(); simp(); }
int32 set_at(struct S* s, uint64 i, int32 v) {
    views s->p;
    views s->e.v;
    owns s->p[0..s->e.v];
    requires i < s->e.v;
    ensures result == v;
    ensures s->p[i] == v;
    ensures forall (k: uint64) { k < s->e.v implies s->p[k] == old(s->p[k]) };
} by {
    execute();
    have s->p == old(s->p) by simp();
    have s->e.v == old(s->e.v) by simp();
    transport(
        forall (k: uint64) { k < s->e.v implies old(s->p[k]) == old(s->p[k]) },
        forall (k: uint64) { k < s->e.v implies s->p[k] == old(s->p[k]) }
    );
    simp();
}
```

```expect
fail: found no frame evidence
```
