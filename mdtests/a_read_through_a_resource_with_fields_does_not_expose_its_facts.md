# A read through a resource with fields does not expose its facts

`peek` reads `p->value` through the folded `c: counted(p)` and claims the
result is the field `c.v`. The read is authorized, but the fact that ties
the cell to the field is inside the resource, and nothing unfolded it. The
claim is refused; `unfold(c)` before the read is what proves it.

```c filename=a_read_through_a_resource_with_fields_does_not_expose_its_facts.c
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

verifying "a_read_through_a_resource_with_fields_does_not_expose_its_facts.c";

int32 peek(struct cell* p) {
    owns c: counted(p);
    ensures result == c.v;
} by {
    execute();
    simp();
}
```

```expect
fail: `ensures result == c.v` failed
```
