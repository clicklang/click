# C does not write through a folded resource with fields

`poke` holds `c: counted(p)` folded and stores to `p->other`. Holding the
resource authorizes reads of the memory it owns directly; a store needs the
cell itself, which `unfold(c)` produces. The store is refused.

```c filename=c_does_not_write_through_an_owned_resource_with_fields.c
struct cell { int32 value; int32 other; };

void poke(struct cell* p) {
    p->other = 7;
}
```

```click
resource counted(p: struct cell*) {
    field v: int32;
    owns p->value;
    owns p->other;
    fact p->value == v;
}

verifying "c_does_not_write_through_an_owned_resource_with_fields.c";

void poke(struct cell* p) {
    owns c: counted(p);
} by {
    execute();
}
```

```expect
fail: missing resource fact `owns p->other`
```
