# A folded resource instance is separate from another owned cell

After a `fold`, the proof state owns the new resource instance beside the
cell the contract owns. Two different resources the state owns exactly are
separate, whatever kind each is.

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
    have separate(d, memory(*slot)) by { assumption(); }
}
```

```expect
pass
```
