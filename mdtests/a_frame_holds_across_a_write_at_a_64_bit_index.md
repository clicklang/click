# A frame holds across a write at a 64-bit index

`set_at` writes one element through a pointer `at` returned, and its
contract says every other element is unchanged. The extent is a field of
a nested struct, as `std::span` keeps it.

Two 64-bit indices held unequal are different cells: the offset of an
element is the exact product of its index and the element width, and
different indices have different products. So `k != i` carries
`s->p[k]` across the write at `s->p[i]`, with nothing said about how
large either index is.

`a_frame_over_a_64_bit_indexed_write_must_exclude_its_cell.md` is a smaller
store whose frame drops `k != i` and is refused.

```c filename=a_frame_holds_across_a_write_at_a_64_bit_index.c
struct E { unsigned long v; };
struct S { int *p; struct E e; };
int *at(const struct S *s, unsigned long i) { return s->p + i; }
int set_at(struct S *s, unsigned long i, int v) { int *e = at(s, i); *e = v; return *e; }
```

```click
verifying "a_frame_holds_across_a_write_at_a_64_bit_index.c";
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
    ensures forall (k: uint64) { k < s->e.v and k != i implies s->p[k] == old(s->p[k]) };
} by {
    execute();
    have s->p == old(s->p) by simp();
    have s->e.v == old(s->e.v) by simp();
    transport(
        forall (k: uint64) { k < s->e.v and k != i implies old(s->p[k]) == old(s->p[k]) },
        forall (k: uint64) { k < s->e.v and k != i implies s->p[k] == old(s->p[k]) }
    );
    simp();
}
```

```expect
pass
```
