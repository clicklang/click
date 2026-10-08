# A contract exit returns a list whose tail it consumed

Control for the duplicate-return refusals: `relink` consumes `list(b)` and
returns `list(a)`, whose tail is now `list(b)`. The tail is returned once,
inside `list(a)`.

```c filename=relink.c
struct node { int32 value; struct node* next; };
int32 relink(struct node* a, struct node* b) {
    a->next = b;
    return 0;
}
```

```click
resource list(node: struct node*) {
    if node != 0 {
        owns node->value;
        owns node->next;
        owns list(node->next);
    }
}
verifying "relink.c";
int32 relink(struct node* a, struct node* b) {
    requires a != 0;
    owns list(a);
    consumes list(b);
    ensures a->next == b;
} by {
    unfold(list(a));
    execute();
    fold(list(a));
    simp();
}
```

```expect
pass
```
