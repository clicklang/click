# Simp relates descriptors that share one buffer pointer

Four descriptors each hold the same buffer pointer `p`, stated as four
separate equalities, and the function compares the first and last
descriptors' pointers. `simp` must chain the equalities through `p` to
show the comparison is true. The four aliases of one pointer offset are
recorded in a persistent set whose insertion order forces rebalancing, so
this also catches a rotation in that set that loses or misorders an alias.

```c filename=simp_relates_descriptors_sharing_one_buffer_pointer.c
struct slot { int32* data; };

int32 same_buffer(int32* p, struct slot* a, struct slot* b, struct slot* c, struct slot* d) {
    return a->data == d->data;
}
```

```click
verifying "simp_relates_descriptors_sharing_one_buffer_pointer.c";

int32 same_buffer(int32* p, struct slot* a, struct slot* b, struct slot* c, struct slot* d) {
    views a->data;
    views b->data;
    views c->data;
    views d->data;
    requires a->data == p;
    requires b->data == p;
    requires c->data == p;
    requires d->data == p;
    ensures result == 1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
