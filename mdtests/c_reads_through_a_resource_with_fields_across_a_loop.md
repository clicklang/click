# C reads through a resource with fields before, inside and after a loop

`count` holds `c: counted(p)` folded for the whole function. Its loop body
reads `p->value` on every iteration and it returns `p->other` after the loop.
Holding the resource lets C read the memory its body owns, and the loop,
which declares the resource, hands it back at its exit with that read
authority attached to it again.

No `unfold` is written. Before 2026-10-08 a resource with fields and a plain
body gave no read authority in a proof that contained a loop.

```c filename=c_reads_through_a_resource_with_fields_across_a_loop.c
struct cell { int32 value; int32 other; };

int32 count(struct cell* p, int32 n) {
    int32 i;
    int32 seen;
    i = 0;
    seen = 0;
    while (i < n) {
        seen = p->value;
        i = i + 1;
    }
    return p->other;
}
```

```click
resource counted(p: struct cell*) {
    field v: int32;
    owns p->value;
    owns p->other;
    fact p->value == v;
}

verifying "c_reads_through_a_resource_with_fields_across_a_loop.c";

int32 count(struct cell* p, int32 n) {
    requires n >= 0;
    owns c: counted(p);
    ensures c.v == old(c.v);
} by {
    step();
    step();
    step();
    step();
    loop {
        owns c: counted(p);
        decreases n - i;
        invariant 0 <= i and i <= n;
        invariant c.v == old(c.v);
    }
    execute();
    simp();
}
```

```expect
pass
```
