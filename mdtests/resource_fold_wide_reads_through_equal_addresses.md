# Wide read congruence composes with parent-address equality in a fold

The body fact is established through named pointers. Folding the same packed
word through pointer fields needs read congruence and substitution inside
`address(...)` together, without additional proof assertions.

```c filename=wide-read-packed.c
struct node { unsigned long tag; struct node *next; };
void inspect(struct node *p, struct node *q, struct node *zid, struct node *sid) { }
```

```click
verifying "wide-read-packed.c";
resource packed_at(p: struct node*, parent: struct node*) {
    owns p->tag;
    fact p->tag == address(parent) + (p->tag & 1);
}
void inspect(struct node *p, struct node *q, struct node *zid, struct node *sid) {
    owns p->next;
    owns q->next;
    consumes zid->tag;
    requires p->next == zid;
    requires q->next == sid;
    requires zid->tag == address(sid) + (zid->tag & 1);
    produces packed_at(p->next, q->next);
    ensures 1 == 1;
} by {
    execute();
    fold(packed_at(p->next, q->next));
    simp();
}
```

```expect
pass
```
