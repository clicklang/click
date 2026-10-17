# Equality reaches a load through a loaded pointer

`o->in->cells[2]` reads memory at an address that is itself read from
memory. The complete-pointer precondition lets entry normalization retain
`a` as the value of `o->in`, including its bounds, before naming the nested
read. Both sides therefore name the same cell and `normalize()` closes the
goal. `simp()` checks the adjacent cell through the same relationship.

The per-cell arena pipeline uses this pattern: its contracts are stated
through `region->arena`, and the caller's invariant through `arena`.

```c filename=rewrite_through_a_loaded_pointer_field.c
struct inner {
    int* cells;
};

struct outer {
    struct inner* in;
};

int same(struct outer* o, struct inner* a) {
    return 0;
}
```

```click
verifying "rewrite_through_a_loaded_pointer_field.c";

int32 same(struct outer* o, struct inner* a) {
    owns *o;
    owns *a;
    owns a->cells[0..4];
    requires o->in == a;
    ensures result == 0;
} by {
    have o->in->cells[2] == a->cells[2] by {
        normalize();
    }
    have o->in->cells[3] == a->cells[3] by {
        simp();
    }
    execute();
    simp();
}
```

```expect
pass
```
