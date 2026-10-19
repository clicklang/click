# A read through an equal loaded pointer reaches its uint64 field

`r` holds the pointer loaded from `p->next`, which equals `q`. Reading
`r->tag` lands on the cell `q->tag`, so its stated fact applies directly.

```c filename=pointer_field_alias.c
struct Node { unsigned long tag; struct Node *next; };
void check(struct Node *p, struct Node *q) {
    struct Node *r = p->next;
}
```

```click
verifying "pointer_field_alias.c";
void check(struct Node* p, struct Node* q) {
    owns p->next;
    owns q->tag;
    requires p->next == q;
    requires (q->tag & 1) == 1;
} by {
    step(); step();
    have r == q;
    have (r->tag & 1) == 1 by assumption();
    execute(); simp();
}
```

```expect
pass
```
