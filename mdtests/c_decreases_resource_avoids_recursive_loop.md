# anonymous structural descent completes through the ordinary proof

The false loop creates no call obligation. The live call passes an observed
child; completion must consume that proof instead of walking the C body again.

```c filename=c_decreases_resource_avoids_recursive_loop.c
struct node { struct node* next; };

void walk(struct node* node) {
    while (0) { walk(node); }
    if (node != 0) {
        walk(node->next);
    }
}
```

```click
resource list(node: struct node*) {
    if node != 0 {
        owns node->next;
        owns list(node->next);
    }
}

verifying "c_decreases_resource_avoids_recursive_loop.c";

void walk(struct node* node) {
    decreases list(node);
    views list(node);
} by {
    if node == 0 {
        step_until(function.exit);
    } else {
        observe(list(node));
        step_until(function.exit);
    }
}
```

```expect
pass
```
