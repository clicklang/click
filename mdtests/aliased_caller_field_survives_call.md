# A caller keeps aliased field ownership across a call

The field belongs to an unfolded modeled node. The call frame must find the
kept field through the checked parent alias and cover the full pointer width.
No explicit separation from the helper's tag is supplied.

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
    requires separate(memory(p->other), memory(q->next));
    requires separate(memory(p->other), memory(q->other));
} by {
    match a.model {
        Tag::At(id, cm) => {
            let {kid: kid} = unfold(a);
            have p == id by assumption();
            step(); mark before; step(); step();
            have p->other == at(before, p->other) by {
                transport(at(before, p->other) == at(before, p->other), p->other == at(before, p->other)) using {
                    separate(memory(p->other), memory(q->next));
                    separate(memory(p->other), memory(q->other));
                    p == id;
                };
            }
            execute(); simp();
        },
    }
}
```

```expect
pass
```
