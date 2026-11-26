# Equality reaches a load through a loaded pointer

`o->in->cells[2]` reads memory at an address that is itself read from
memory. The read of `o->in` keeps its own name: only the precondition
`o->in == a` relates it to `a`, and lowering never rewrites through a fact
(`docs/internals/raise-lower-principle.md`). `rewrite(o->in, a)` moves the nested
read to `a->cells[2]`, named as lowering names it, and the array-read lemma closes
the resulting equality. The adjacent cell cites the pointer equality at
function entry explicitly.

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

theorem same_array_cell(base: int32*, alias: int32*, index: int32) {
    requires base == alias;
    requires 0 <= index and index < 4;
    requires viewable(base[0..4]);
    ensures alias[index] == base[index] by {
        rewrite(alias, base);
        close();
    }
}

int32 same(struct outer* o, struct inner* a) {
    owns *o;
    owns *a;
    owns a->cells[0..4];
    requires o->in == a;
    ensures result == 0;
} by {
    have viewable(a->cells[0..4]) by {
        observe(a->cells[0..4]);
    }
    have o->in->cells == a->cells by {
        rewrite(o->in, a);
        close();
    }
    have o->in->cells[2] == a->cells[2] by {
        rewrite(o->in, a);
        apply(same_array_cell(a->cells, o->in->cells, 2));
        close();
    }
    have o->in->cells[3] == a->cells[3] by {
        rewrite(at(function.entry, o->in), at(function.entry, a));
        apply(same_array_cell(a->cells, o->in->cells, 3));
        close();
    }
}
```

```expect
pass
```
