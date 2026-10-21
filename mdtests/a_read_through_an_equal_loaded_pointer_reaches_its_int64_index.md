# A read through an equal loaded pointer reaches its int64 index

`a[p->q->idx]` loads its int64 index through the pointer `p->q` read from
memory. With `p->q == r` known, that read lands on the cell `r->idx`, so the
goal is the stated `a[r->idx] == 5` without a rewrite, whatever the index's
width.

```c filename=rewrite_through_a_int64_index_load.c
struct S { int64 idx; };
struct P { struct S *q; };
void f(struct P *p, struct S *r, int32 *a) {
}
```

```click
verifying "rewrite_through_a_int64_index_load.c";
void f(struct P* p, struct S* r, int32* a) {
    views p->q;
    views r->idx;
    views a[0..10];
    requires p->q == r;
    requires 0 <= r->idx;
    requires r->idx < 10;
    requires a[r->idx] == 5;
    ensures 1 == 1;
} by {
    have a[p->q->idx] == 5 by assumption();
    execute();
    simp();
}
```

```expect
pass
```
