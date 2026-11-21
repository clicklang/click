# Folded resource authority supplies an entry-point pointer read

```c filename=entry_pointer_probe.c
struct node {
    struct node* right;
    int32 augmented;
};
void peek(struct node* node) {}
```

```click
resource pair(node: struct node*) { field weight: int32; owns node->right; }
verifying "entry_pointer_probe.c";

void peek(struct node* node) {
    requires node != 0;
    owns links: pair(node);
    owns node->right->augmented;
}
```

```expect
pass
```
