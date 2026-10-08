# An entry interface must hold in both arms

The arms establish the original value, not an unrelated pointer chosen by
the interface. Binding function parameters must not authorize that equality.

```c filename=probe.c
struct node { unsigned long tag; struct node *other; struct node *next; };
void probe(struct node *p, struct node *q, struct node *value) {}
```

```click
verifying "probe.c";
spec enum Tag { Top, At(struct node*) }
resource link(p: struct node*, value: struct node*) {
    field model: Tag;
    match model {
        Tag::Top => { owns p->next; fact p->next == value; },
        Tag::At(id) => { owns id->other; owns id->next; fact p == id; fact id->next == value; },
    }
}
resource frame(p: struct node*) {
    field model: Tag;
    match model {
        Tag::Top => { },
        Tag::At(id) => { owns id->other; fact p == id; },
    }
}
void probe(struct node *p, struct node *q, struct node *value) {
    consumes a: link(p, value);
    produces p->next;
    produces b: frame(p);
    ensures p->next == value;
} by {
    match a.model ensuring {
        owns p->next;
        owns b: frame(p);
        fact p->next == q;
    } {
        Tag::Top => {
            unfold(a);
            let b = fold(frame(p), {model: Tag::Top});
            have p->next == value;
        },
        Tag::At(id) => {
            unfold(a);
            have p->next == id->next;
            have p->next == value;
            let b = fold(frame(p), {model: Tag::At(id)});
            have p->next == value;
        },
    }
    execute(); simp();
}
```

```expect
fail: `branch ensuring` did not establish fact
```
