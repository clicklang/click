# Recursive returns retain a finite frontier across repeated calls

A checked return exposes the visible node once and retains its recursive
child as a folded occurrence. Reusing that return does not recursively
follow the next pointers.

```c filename=finite_recursive_returns.c
struct node { struct node* next; };
void keep(struct node* node) {}
void forward(struct node* node) { keep(node); keep(node); }
```

```click
resource list(node: struct node*) {
    if node != 0 {
        owns node->next;
        owns list(node->next);
    }
}
verifying "finite_recursive_returns.c";
void keep(struct node* node) {
    requires node != 0;
    owns list(node);
}
void forward(struct node* node) {
    requires node != 0;
    owns list(node);
}
```

```expect
pass
```
