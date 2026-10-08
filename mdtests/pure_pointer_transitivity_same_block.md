# Pure pointer equalities compose with C parameter pointers

C parameters share the symbolic external address block. A chain through a
pure function result must still prove equality of the original parameters,
even though their comparison lowers to equality of byte offsets.

```c filename=probe.c
struct node { struct node *left; struct node *right; unsigned long color; };
void probe(struct node *p, struct node *q) {}
```

```click
verifying "probe.c";
function identity(p: struct node*) -> struct node* { p }
void probe(struct node *p, struct node *q) {
    requires p == identity(q);
    ensures p == q;
} by {
    have identity(q) == q by { unfold(identity(q)); normalize(); }
    have p == q by { normalize() using { } }
    execute(); simp();
}
```

```expect
pass
```
