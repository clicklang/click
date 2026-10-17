# A member pointer kept across a loop keeps its subobject

A loop reassigns `q = &p->first`, and its invariant says so. After the loop
`q` is the invariant's value, which designates `first`, so reading one
element past it is refused, though the function views `p->second`.

```c filename=loop_member.c
struct Pair { int32 first; int32 second; };
int32 probe(struct Pair* p, int32 n) {
    int32 i;
    int32* q = &p->first;
    for (i = 0; i < n; i++) { q = &p->first; }
    return q[1];
}
```

```click
verifying "loop_member.c";
int32 probe(struct Pair* p, int32 n) {
    requires 0 <= n;
    views p->first;
    views p->second;
    ensures true;
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases n - i;
        invariant i >= 0 and i <= n;
        invariant q == &p->first;
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
