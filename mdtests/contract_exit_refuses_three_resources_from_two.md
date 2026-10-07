# A contract exit cannot return three exclusive resources from two

`f` enters with `pair(a)`, whose body contains `cell(a->next)`, that is
`cell(c)`, and with `cell(b)`. After `a->next = b` the refolded `pair(a)`
contains `cell(b)`, so the final state holds `pair(a)` and `cell(c)`. The
contract returns `pair(a)`, `cell(b)` and `cell(c)`: `cell(b)` is only
inside the returned `pair(a)`, and the exit refuses it.

```c filename=three_from_two.c
struct node { int32 value; struct node* next; };
int32 f(struct node* a, struct node* b, struct node* c) {
    a->next = b;
    return 0;
}
```

```click
resource cell(p: struct node*) {
    owns p->value;
}
resource pair(p: struct node*) {
    owns &p->next;
    contains cell(p->next);
}
verifying "three_from_two.c";
int32 f(struct node* a, struct node* b, struct node* c) {
    requires a != 0;
    requires a->next == c;
    owns pair(a);
    owns cell(b);
    produces cell(c);
} by {
    unfold(pair(a));
    execute();
    fold(pair(a));
    simp();
}
```

```expect
fail: missing resource fact
```
