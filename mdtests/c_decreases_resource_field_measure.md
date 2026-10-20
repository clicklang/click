# a structural measure over a field reads through the field's narrowing

A contract's measure may name a field of a parameter, `nodes(self->next)`.
The field's subobject narrowing changes neither the value the C guard
`if (next)` tests nor which child the recursive call passes, so the guard
selects the resource's nonempty arm and the call passes its direct child.
This is the shape of the Rust drop glue of a struct holding a box of its own
type.

```c filename=c_decreases_resource_field_measure.c
struct node {
    int32 value;
    struct node *next;
};

void drop_next(struct node *self) {
    struct node *next = self->next;
    if (next) {
        drop_next(next);
    }
    free(next);
}
```

```click
resource nodes(node: struct node*) {
    if node != 0 {
        owns allocation(node, sizeof(struct node));
        owns *node;
        owns nodes(node->next);
        fact aligned(node, 8);
    }
}

verifying "c_decreases_resource_field_measure.c";

void drop_next(struct node* self) {
    owns *self;
    consumes nodes(self->next);
    decreases nodes(self->next);
} by {
    if self->next == 0 {
        unfold(nodes(self->next));
        execute();
        simp();
    } else {
        unfold(nodes(self->next));
        execute();
        simp();
    }
}
```

```expect
pass
```
