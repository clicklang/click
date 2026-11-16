# a helper cannot return an unrelated witness under the child's old name

The helper may change the child's structure while preserving the resource
contract. Its returned witness has no retained height bound relative to the
caller's entry witness. Equal pointer arguments are insufficient.

```c filename=c_decreases_resource_rejects_a_replaced_child_witness.c
struct node { struct node *next; };
void change(struct node *node);

void walk(struct node *node) {
    if (node != 0) {
        struct node *next = node->next;
        change(next);
        walk(next);
    }
}
```

```click
verifying "c_decreases_resource_rejects_a_replaced_child_witness.c";

resource list(node: struct node*) {
    if node != 0 {
        owns node->next;
        owns list(node->next);
    }
}

extern void change(struct node* node) { owns list(node); }

void walk(struct node* node) {
    decreases list(node);
    consumes list(node);
} by {
    if node == 0 {
        unfold(list(node));
        step_until(function.exit);
    } else {
        unfold(list(node));
        step_until(function.exit);
    }
}
```

```expect
fail: must receive a retained child witness of the entry resource
```
