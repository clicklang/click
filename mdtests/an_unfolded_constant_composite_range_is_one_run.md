# An unfolded composite range of constant length is one run of cells

`block(a)` owns a thousand elements. Unfolding it exposes every element as
a known cell, the load of that element before the unfold, and those cells
are one run rather than a thousand separate ones. A store into the range
replaces one slot and keeps the others, so the stored value reads back and
a neighbouring element keeps its old value. Before the run, the store after
the unfold compared itself with every element and exhausted the smart
budget.

`pointers(p)` holds pointer elements. Their cells keep the word their load
names, as each element's named cell did, and a store of one pointer leaves
the next unchanged.

`an_unfolded_constant_composite_range_is_one_run_negative.md` is the
negative: a symbolic element may be the one the store wrote.

```c filename=an_unfolded_constant_composite_range_is_one_run.c
int32 put(int32 *a) {
    a[3] = 5;
    return a[3];
}

void put_pointer(int32 **p, int32 *q) {
    p[1] = q;
}
```

```click
verifying "an_unfolded_constant_composite_range_is_one_run.c";

resource block(p: int32*) { owns p[0..1000]; }
resource pointers(p: int32**) { owns p[0..1000]; }

int32 put(int32 *a) {
    consumes block(a);
    produces block(a);
    ensures result == 5;
    ensures a[3] == 5;
    ensures a[4] == old(a[4]);
} by {
    unfold(block(a));
    execute();
    fold(block(a));
    simp();
}

void put_pointer(int32 **p, int32 *q) {
    consumes pointers(p);
    produces pointers(p);
    ensures p[2] == old(p[2]);
    ensures p[1] == q;
} by {
    unfold(pointers(p));
    execute();
    fold(pointers(p));
    simp();
}
```

```expect
pass
```
