# An owned resource unfolds after C read through it

`bump` reads `p->other` through the folded `flat(p)`, then unfolds the
resource to store to `p->value`, and folds it again. The read leaves nothing
behind that outlives the owner: the unfold exchanges exactly the resource for
its body, and the fold gives the resource back.

```c filename=an_owned_resource_unfolds_after_a_read_through_it.c
struct cell {
    int32 value;
    int32 other;
};

void bump(struct cell* p) {
    int32 seen = p->other;
    p->value = seen;
}
```

```click
resource flat(p: struct cell*) {
    owns p->value;
    owns p->other;
}

verifying "an_owned_resource_unfolds_after_a_read_through_it.c";

void bump(struct cell* p) {
    owns flat(p);
} by {
    step();
    unfold(flat(p));
    execute();
    fold(flat(p));
    simp();
}
```

```expect
pass
```
