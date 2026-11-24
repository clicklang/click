# An exact and an ordinary read of one pointer cell are one load

A load's identity is its version point and its cell (`design/loads.md`,
"Terms"). At function entry nothing has written `h->next`, so its ordinary
read names the entry point, and `exact(h->next)` names the same point
exactly: one point, one cell, one load, whichever selection named it. The two
reads are one pointer value, and so is every field read through them, with
no fact to find. After the store to `*q`, `old(..)` reads both at the entry
point again and they are still one load.

```c filename=an_exact_and_an_ordinary_read_of_one_pointer_cell_are_one_load.c
struct node { struct node *next; int v; };
void touch(struct node *h, int *q) { *q = 1; }
```

```click
verifying "an_exact_and_an_ordinary_read_of_one_pointer_cell_are_one_load.c";
void touch(struct node* h, int32* q) {
    owns h->next;
    owns h->next->v;
    owns *q;
    ensures *q == 1;
} by {
    have exact(h->next) == h->next by known();
    have exact(h->next)->v == h->next->v by known();
    step_until(function.exit);
    have old(exact(h->next)) == old(h->next) by known();
    have old(exact(h->next)->v) == old(h->next->v) by known();
}
```

```expect
pass
```
