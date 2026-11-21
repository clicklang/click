# A private body requires separation from an active view

The entry contract does not establish that the two pointers are equal or
disjoint. Opening the private body still requires separation from the view.

```c filename=population_private_body_overlap_view.c
int update(int *pool, int *p, int *q) {
    p[0] = 7;
    return 7;
}
```

```click
authorized resource slot(pool: int32*, p: int32*) { owns p[0..1]; }
verifying "population_private_body_overlap_view.c";
int32 update(int32 *pool, int32 *p, int32 *q) {
    owns slot(pool, p);
    views q[0..1];
    ensures result == 7;
} by {
    with(slot(pool, p)) { step(); }
}
```

```expect
fail: member private body requires separation from active borrows
```
