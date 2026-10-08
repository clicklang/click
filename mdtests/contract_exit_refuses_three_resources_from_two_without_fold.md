# A contract exit cannot return three exclusive resources from two without a fold

As in the folded form, but the proof leaves `pair(a)` open. The final state
holds `&a->next`, `cell(c)` and `cell(b)`; the contract returns `pair(a)`
(which must take `&a->next` and `cell(b)`), `cell(b)` and `cell(c)`, so
`cell(b)` is claimed twice.

```c filename=three_from_two_open.c
struct node { int32 value; struct node* next; };
int32 f(struct node* a, struct node* b, struct node* c) {
    a->next = b;
    return 0;
}
```

```click
resource cell(p: struct node*) {
    owns p->value;
}
resource pair(p: struct node*) {
    owns p->next;
    contains cell(p->next);
}
verifying "three_from_two_open.c";
int32 f(struct node* a, struct node* b, struct node* c) {
    requires a != 0;
    requires a->next == c;
    owns pair(a);
    owns cell(b);
    produces cell(c);
} by {
    unfold(pair(a));
    execute();
    simp();
}
```

```expect
fail: missing resource fact
```
