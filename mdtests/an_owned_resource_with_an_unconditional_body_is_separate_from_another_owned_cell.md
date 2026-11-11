# An owned resource with an unconditional body is separate from another owned cell

A contract that owns a named resource and a cell holds them together, so they
are separate at the first tactic. The entry expands a resource whose body is
unconditional into what the body owns; the resource itself must still be an
owned member the separation can name.

```c filename=owned.c
struct node { struct node *next; };
void caller(struct node *child, int *slot) { }
```

```click
verifying "owned.c";
resource plain(p: struct node*) { owns p->next; }
void caller(struct node* child, int32* slot) {
    owns plain(child);
    owns *slot;
} by {
    have separate(plain(child), memory(*slot)) by { assumption(); }
}
```

```expect
pass
```
