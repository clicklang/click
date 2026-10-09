# A parent alias keeps its child across stores and a call

The parent introduces `p == id` while exposing a named child. The kernel and
surface materializer must use the same checked alias context to name its
pointer field, so the unchanged child can be returned after stores and a call.

```c filename=probe.c
struct node { unsigned long tag; struct node *other; struct node *next; };
void helper(struct node *q) { q->tag = 0; }
void probe(struct node *p, struct node *q) { q->next = p; helper(q); q->other = p; }
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
            owns id->other;
            owns kid: child(id->other);
            fact kid.model == cm;
            fact p == id;
        },
    }
}
void helper(struct node *q) { owns q->tag; } by { execute(); simp(); }
void probe(struct node *p, struct node *q) {
    owns q->tag; owns q->next; owns q->other;
    consumes a: frame(p);
    produces b: frame(p);
    ensures b.model == old(a.model);
} by {
    match a.model {
        Tag::At(id, cm) => {
            let {kid: kid} = unfold(a);
            have p == id by { assumption(); }
            step(); step(); step();
            let b = fold(frame(p), {model: Tag::At(id, cm)}, {kid: kid});
            execute(); simp();
        },
    }
}
```

```expect
pass
```
