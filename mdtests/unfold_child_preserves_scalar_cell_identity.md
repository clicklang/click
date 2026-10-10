# Unfold keeps scalar cell names consistent with its checked body facts

The selected arm has a named child, so its facts become available at unfold.
Its new `p == id` fact must not make cell materialization choose a different
address spelling from the kernel rewrite that produced the scalar equation.
The child remains folded and is returned unchanged by the parent refold.

```c filename=probe.c
struct node { unsigned long tag; struct node *other; struct node *next; };
void probe(struct node *p) {}
```

```click
verifying "probe.c";
spec enum Child { Empty }
spec enum Tag { At(struct node*, struct node*, Child) }
resource child(p: struct node*) {
    field model: Child;
    owns p->tag;
    fact p != 0;
}
resource frame(p: struct node*) {
    field model: Tag;
    match model {
        Tag::At(id, gp, child_model) => {
            owns id->tag;
            owns id->other;
            owns kid: child(id->other);
            fact kid.model == child_model;
            fact p == id;
            fact id != 0;
            fact aligned(id, 8);
            fact aligned(gp, 8);
            fact id->tag == address(gp) + (id->tag & 1);
            fact (id->tag & 1) == 1;
        },
    }
}
void probe(struct node *p) {
    consumes a: frame(p);
    produces b: frame(p);
    ensures b.model == old(a.model);
} by {
    match a.model {
        Tag::At(id, gp, child_model) => {
            let {kid: kid} = unfold(a);
            have id->tag == address(gp) + (id->tag & 1) by assumption();
            have p != 0 by { rewrite(p == id); assumption(); }
            have aligned(p, 8) by { rewrite(p == id); assumption(); }
            let b = fold(frame(p), {model: Tag::At(id, gp, child_model)}, {kid: kid});
            execute(); simp();
        },
    }
}
```

```expect
pass
```
