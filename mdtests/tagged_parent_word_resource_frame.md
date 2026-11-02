# A framed parent word retains its complete pointer fact

```c filename=tagged.c
struct node { unsigned long tag; struct node *right; struct node *left; };
void keep(struct node *n, struct node *p) {
    p->left = n->right;
    n->right = p;
    p->tag = (unsigned long)n;
}
```

```click
verifying "tagged.c";
resource parent_word(n: struct node*, p: struct node*) {
    field bits: uint64;
    owns n->tag;
    fact n->tag == bits;
    fact ((n->tag & ~3) as (struct node *)) == p;
}
void keep(struct node* n, struct node* p) {
    owns n->tag;
    owns n->right;
    owns n->left;
    owns p->tag;
    owns p->right;
    owns p->left;
    requires ((n->tag & ~3) as (struct node *)) == p;
    ensures ((n->tag & ~3) as (struct node *)) == p;
} by {
    let saved = fold(parent_word(n, p), { bits: n->tag });
    step_until(function.exit);
    unfold(saved);
    have ((n->tag & ~3) as (struct node *)) == p by { assumption(); }
}
```

```expect
pass
```
