# Transport a field fact through a loaded pointer alias

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
    have (r->tag & 1) == 1 by { rewrite(r == q); assumption(); }
    execute(); simp();
}
```

```expect
pass
```
