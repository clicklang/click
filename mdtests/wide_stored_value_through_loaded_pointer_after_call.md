# A selected pointer alias recovers a wide stored value after a named call

The C local holds a pointer loaded before the store. A named resource call
clears its cached read; the explicit alias must connect that read to the caller’s
kept ownership and the recorded eight-byte store.

```c filename=flat.c
struct Node { unsigned long tag; struct Node *next; };
void helper(struct Node *p) { p->tag = 0; }
void caller(struct Node *p, struct Node *q) {
    struct Node *r = p->next;
    r->tag = 7;
    helper(p);
}
```

```click
verifying "flat.c";
spec enum Tag { Here }
resource tag(p: struct Node*) { field model: Tag; owns p->tag; fact model == Tag::Here; }
void helper(struct Node *p) { consumes before: tag(p); produces after: tag(p); }
by { unfold(before); execute(); let after = fold(tag(p), {model: Tag::Here}); simp(); }
void caller(struct Node *p, struct Node *q) {
    consumes before: tag(p); produces after: tag(p);
    owns p->next; owns q->tag;
    requires p->next == q;
    ensures q->tag == 7;
} by {
    step(); step(); step();
    have r->tag == 7;
    have r == q;
    let {after: after} = step(helper(p), {before: before});
    have r == q;
    have r->tag == 7 by { normalize() using { r == q; }; }
    execute(); simp();
}
```

```expect
pass
```
