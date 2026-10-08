# C does not write through a folded owned resource

`poke` holds `flat(p)` folded and stores to `p->value`. Holding the resource
authorizes reads of the memory it owns directly and nothing more: a store
needs the field itself, which `unfold(flat(p))` would produce. The store is
refused.

The read is `c_reads_through_an_owned_resource.md`.

```c filename=c_does_not_write_through_an_owned_resource.c
struct cell {
    int32 value;
    int32 other;
};

void poke(struct cell* p) {
    p->value = 7;
}
```

```click
resource flat(p: struct cell*) {
    owns p->value;
    owns p->other;
}

verifying "c_does_not_write_through_an_owned_resource.c";

void poke(struct cell* p) {
    owns flat(p);
} by {
    execute();
}
```

```expect
fail: missing resource fact `owns p->value`
```
