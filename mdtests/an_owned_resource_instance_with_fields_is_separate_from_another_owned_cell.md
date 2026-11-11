# An owned resource instance with fields is separate from another owned cell

A contract that owns a resource instance and a cell holds them together, so
they are separate. A resource that declares a `field` is only ever owned
whole; it is still an owned member the separation can name.

```c filename=owned.c
struct node { struct node *next; };
void caller(struct node *child, int *slot) { }
```

```click
verifying "owned.c";
resource box(p: struct node*) {
    field tag: int32;
    if p != 0 { owns p->next; }
}
void caller(struct node* child, int32* slot) {
    owns b: box(child);
    owns *slot;
} by {
    have separate(b, memory(*slot)) by { assumption(); }
}
```

```expect
pass
```
