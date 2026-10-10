# A fold must prove its proposed parent alias

The proposed model changes the parent identity to `q`. Folding must prove
that new equality; the opening rule cannot grant facts of a proposed model.

```c filename=probe.c
struct node { unsigned long tag; struct node *other; struct node *next; };
void helper(struct node *q) { q->tag = 0; }
void probe(struct node *p, struct node *q) { helper(q); }
```

```click
verifying "probe.c";
spec enum Tag { At(struct node*, Child) }
spec enum Child { Empty }
resource child(p: struct node*) { field model: Child; owns p->tag; }
resource frame(p: struct node*) {
    field model: Tag;
    match model {
        Tag::At(id, cm) => {
            owns p->other;
            owns kid: child(p->other);
            fact kid.model == cm;
            fact p == id;
        },
    }
}
void helper(struct node *q) { owns q->tag; } by { execute(); simp(); }
void probe(struct node *p, struct node *q) {
    owns q->tag;
    consumes a: frame(p);
    produces b: frame(p);
    ensures b.model == old(a.model);
} by {
    match a.model {
        Tag::At(id, cm) => {
            let {kid: kid} = unfold(a);
            have p == id by assumption();
            step();
            let b = fold(frame(p), {model: Tag::At(q, cm)}, {kid: kid});
            execute(); simp();
        },
    }
}
```

```expect
fail: fold requires the instance body facts
```
