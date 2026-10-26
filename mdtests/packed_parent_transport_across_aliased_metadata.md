# A packed parent pointer survives metadata writes through an alias

The numeric word and its complete pointer designation must both cross the
metadata-only call. The explicit transport lists the two disjoint write
regions, while the resource retains the word through the loaded child alias.

```c filename=frame.c
struct node { unsigned long word; struct node *left; struct node *right; };
struct sized { struct node rb; int32 size; };
void update(struct node *p, struct node *q) {
    ((struct sized *)(void *)p)->size = 1;
    ((struct sized *)(void *)q)->size = 2;
}
struct node *caller(struct node *p, struct node *q, struct node *parent) {
    update(p, q);
    return (struct node *)(p->word & ~3);
}
```

```click
resource metadata(p: struct node*) {
    field value: int32;
    owns ((struct sized*)(void*)p)->size;
    fact ((struct sized*)(void*)p)->size == value;
}
resource packed(p: struct node*, parent: struct node*) {
    field bits: uint64;
    owns p->word;
    fact p->word == bits;
    fact ((struct node*)(p->word & ~3)) == parent;
}
resource framed(p: struct node*, q: struct node*, parent: struct node*) {
    field bits: uint64;
    field first: int32;
    field second: int32;
    owns q->left;
    owns child: packed(q->left, parent);
    owns a: metadata(p);
    owns b: metadata(q);
    fact p == q->left;
    fact child.bits == bits;
    fact a.value == first;
    fact b.value == second;
}
tactic word_metadata_separation(p: struct node*, q: struct node*) {
    owns p->word;
    owns b: metadata(q);
    ensures b.value == old(b.value);
    ensures separate(memory(p->word), memory(((struct sized*)(void*)q)->size));
} by { unfold(b); have separate(memory(p->word), memory(((struct sized*)(void*)q)->size)) by assumption(); fold(b); }
verifying "frame.c";
void update(struct node* p, struct node* q) {
    owns a: metadata(p);
    owns b: metadata(q);
    ensures a.value == 1;
    ensures b.value == 2;
} by { unfold(a); unfold(b); execute(); let a = fold(metadata(p), { value: 1 }); let b = fold(metadata(q), { value: 2 }); solve(); }
struct node* caller(struct node* p, struct node* q, struct node* parent) {
    consumes f: framed(p, q, parent);
    ensures result == parent;
} by {
    let { child: child, a: a, b: b } = unfold(f);
    unfold(child);
    have separate(memory(p->word), memory(((struct sized*)(void*)p)->size));
    word_metadata_separation(p, q, { b: b });
    mark before_update;
    have ((struct node*)(p->word & ~3)) == parent by solve();
    step(update, { a: a, b: b });
    have p->word == at(before_update, p->word) by { transport(at(before_update, p->word) == at(before_update, p->word), p->word == at(before_update, p->word)); }
    have ((struct node*)(p->word & ~3)) == parent by { transport(at(before_update, ((struct node*)(p->word & ~3))) == parent, ((struct node*)(p->word & ~3)) == parent) using { at(before_update, ((struct node*)(p->word & ~3))) == parent; p == at(before_update, q->left); separate(memory(p->word), memory(((struct sized*)(void*)p)->size)); separate(memory(p->word), memory(((struct sized*)(void*)q)->size)); }; }
}
```

```expect
pass
```
