# A resource fold follows a reassigned C parameter

```c filename=current_fold.c
struct node { uint64 tag; };
void pack(struct node *p, struct node *q) { p = q; p->tag = 7; }
void open(struct node *p, struct node *q) { p = q; p->tag = 7; }
struct node *finish(struct node *p, struct node *q) { p = q; return p; }
```

```click
verifying "current_fold.c";
resource tag_at(p: struct node*) { owns p->tag; }
void pack(struct node* p, struct node* q) {
    consumes q->tag;
    ensures 1 == 1;
} by {
    step();
    fold(tag_at(p));
    unfold(tag_at(p));
    step();
    execute(); simp();
}
void open(struct node* p, struct node* q) {
    consumes tag_at(q);
    ensures 1 == 1;
} by {
    step();
    unfold(tag_at(p));
    step();
    execute(); simp();
}
struct node* finish(struct node* p, struct node* q) {
    consumes q->tag;
    ensures 1 == 1;
} by {
    execute();
    fold(tag_at(result));
    unfold(tag_at(result));
    simp();
}
```

```expect
pass
```
