# A folded resource instance is not separate from its own cell

After a `fold`, the state owns the resource instance, not the cell its body
owns. That cell is no owned member of the state, so nothing separates the
instance from it.

```c filename=owned.c
struct node { struct node *next; };
void caller(struct node *child, int *slot) { }
```

```click
verifying "owned.c";
resource box(p: struct node*) {
    field tag: int32;
    owns p->next;
}
void caller(struct node* child, int32* slot) {
    owns b: box(child);
    owns *slot;
    requires b.tag == 0;
} by {
    unfold(b);
    let d = fold(box(child), { tag: 0 });
    have separate(d, memory(child->next)) by { assumption(); }
}
```

```expect
fail: `assumption` requires the current goal as an available semantic fact
```
