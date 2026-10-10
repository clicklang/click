# Fold a fieldless resource at a model-bound pointer

```c filename=model_fold.c
struct node { uint64 tag; };
void pack(struct node *p, struct node *id) { p->tag = 7; }
```

```click
verifying "model_fold.c";
spec enum Identity { At(struct node*) }
resource modeled(p: struct node*) {
    field model: Identity;
    match model { Identity::At(id) => { owns p->tag; fact p == id; }, }
}
resource tag_at(p: struct node*) { owns p->tag; }
void pack(struct node* p, struct node* id) {
    consumes before: modeled(p);
    ensures 1 == 1;
} by {
    match before.model { Identity::At(id) => {
        unfold(before);
        fold(tag_at(id));
        unfold(tag_at(id));
        step();
        fold(tag_at(id));
        execute(); simp();
    }, }
}
```

```expect
pass
```
