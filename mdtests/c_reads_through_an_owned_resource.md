# C reads memory an owned resource owns directly

`peek` holds `flat(p)` folded and reads `p->value`. The resource owns that
field directly, so holding it authorizes the read: the proof has no `unfold`
and no loop. The result is the field's entry value, which the folded resource
does not constrain, so the contract claims only that the resource comes back.

The write is `c_does_not_write_through_an_owned_resource.md`.

```c filename=c_reads_through_an_owned_resource.c
struct cell {
    int32 value;
    int32 other;
};

int32 peek(struct cell* p) {
    return p->value;
}
```

```click
resource flat(p: struct cell*) {
    owns p->value;
    owns p->other;
}

verifying "c_reads_through_an_owned_resource.c";

int32 peek(struct cell* p) {
    owns flat(p);
} by {
    execute();
    simp();
}
```

```expect
pass
```
