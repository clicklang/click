# Separation after instance unfolds with a checked incoming loan

A checked incoming loan and usable ownership occupy separate custody partitions.
Opening a named owner exposes that existing separation. Two views still do not
prove separation, and a caller cannot lend the owner it transfers; see
`named_unfold_does_not_separate_two_views.md` and
`named_unfold_rejects_aliasing_owner_and_loan.md`.

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
    have separate(memory(p->tag), memory(q->tag)) by assumption();
}
```

```expect
pass
```
