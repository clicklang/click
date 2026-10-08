# C reads memory an owned resource with fields owns directly

`peek` holds `c: counted(p)` folded and reads `p->value`. The resource has a
field and a plain body that owns the cell, so holding it authorizes the read
with no `unfold`, as for a resource without fields
(`c_reads_through_an_owned_resource.md`).

The read does not open the resource: the fact `p->value == v` stays inside
it. `a_read_through_a_resource_with_fields_does_not_expose_its_facts.md`
claims the result is `c.v` and is refused.

```c filename=c_reads_through_an_owned_resource_with_fields.c
struct cell { int32 value; int32 other; };

int32 peek(struct cell* p) {
    return p->value;
}
```

```click
resource counted(p: struct cell*) {
    field v: int32;
    owns p->value;
    owns p->other;
    fact p->value == v;
}

verifying "c_reads_through_an_owned_resource_with_fields.c";

int32 peek(struct cell* p) {
    owns c: counted(p);
    ensures c.v == old(c.v);
} by {
    execute();
    simp();
}
```

```expect
pass
```
