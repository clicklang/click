# a call keeps a caller's nonempty recursive resource

`clear_beside` holds two lists it does not pass to `clear`: `head`, known
nonempty, and `spare`, whose nullness is undecided. To frame the call, the
caller's kept resources are opened to the cells they own: `list(head)` opens
to its head cell, and its recursive child `list(head->next)` is left as a head
because `list` is already being opened, while `list(spare)` has no decided arm
and stays opaque. Both lists survive the call. This catches a frame expansion
that recurses into a resource it is already opening, or that drops a
composite whose body it could not open.

```c filename=call_keeps_a_nonempty_recursive_resource.c
struct node {
    struct node *next;
};

void clear(int32 *count) {
    *count = 0;
}

void clear_beside(struct node *head, struct node *spare, int32 *count) {
    clear(count);
}
```

```click
resource list(node: struct node*) {
    if node != 0 {
        owns node->next;
        owns list(node->next);
    }
}

verifying "call_keeps_a_nonempty_recursive_resource.c";

void clear(int32 *count) {
    owns *count;
} by {
    execute();
    simp();
}

void clear_beside(struct node *head, struct node *spare, int32 *count) {
    requires head != 0;
    owns list(head);
    owns list(spare);
    owns *count;
} by {
    execute();
    simp();
}
```

```expect
pass
```
