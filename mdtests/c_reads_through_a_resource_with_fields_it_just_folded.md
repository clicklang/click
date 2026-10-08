# C reads through a resource with fields it has just folded

`bump` unfolds `c: counted(p)` to store to `p->value`, folds it with the new
field value, and then reads `p->other` through the folded resource. The
fold makes a new instance; it publishes read authority for the cells it
consumed, attached to that instance, so the read after it needs no second
`unfold`.

```c filename=c_reads_through_a_resource_with_fields_it_just_folded.c
struct cell { int32 value; int32 other; };

int32 bump(struct cell* p) {
    p->value = 7;
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

verifying "c_reads_through_a_resource_with_fields_it_just_folded.c";

int32 bump(struct cell* p) {
    owns c: counted(p);
    ensures c.v == 7;
} by {
    unfold(c);
    step();
    let c = fold(counted(p), { v: 7 });
    step();
    simp();
}
```

```expect
pass
```
