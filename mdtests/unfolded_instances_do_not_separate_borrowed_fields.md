# Separation after instance unfolds

A view may alias an owned field exposed by an unfold. Observing the live partition must not treat the view as exclusive.

```c filename=unfolded_instances_do_not_separate_borrowed_fields.c
struct node { uint64 tag; };
void user(struct node *p, struct node *q) {}
```

```click
verifying "unfolded_instances_do_not_separate_borrowed_fields.c";
resource owned(p: struct node*) { field model: int32; owns p->tag; }
void user(struct node* p, struct node* q) {
    consumes a: owned(p);
    produces p->tag;
    views q->tag;
    ensures separate(memory(p->tag), memory(q->tag));
} by {
    unfold(a);
    have separate(memory(p->tag), memory(q->tag)) by { assumption(); }
    execute(); simp();
}
```

```expect
fail: `assumption` requires the current goal as an available semantic fact
```
