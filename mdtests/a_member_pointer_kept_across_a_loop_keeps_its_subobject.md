# A member pointer kept across a loop keeps its subobject

A loop rewrites `h->link = &p->first`, and its invariant says so. After
the loop the field's value is the invariant's, which designates `first`, so
reading one element past it is refused.

```c filename=loop_member.c
struct Pair { int32 first; int32 second; };
struct Holder { int32* link; };
int32 probe(struct Pair* p, struct Holder* h, int32 n) {
    int32 i;
    h->link = &p->first;
    for (i = 0; i < n; i++) { h->link = &p->first; }
    return h->link[1];
}
```

```click
verifying "loop_member.c";
int32 probe(struct Pair* p, struct Holder* h, int32 n) {
    requires 0 <= n;
    views p->first;
    views p->second;
    owns h->link;
    ensures true;
} by {
    step();
    step();
    step();
    loop {
        decreases n - i;
        invariant i >= 0 and i <= n;
        invariant h->link == &p->first;
        preserve by {
            step();
            step();
            close_invariants() by simp();
        }
    }
    execute();
    simp();
}
```

```expect
fail: access outside the subobject the pointer designates
```
