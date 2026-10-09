# An alias does not preserve a pointer field across its overwrite

The first store establishes the parent link, but the second clears it.
The earlier link value and the base alias must not prove the stale claim.

```c filename=link.c
struct node { uint64 tag; struct node *right; struct node *left; };
void link(struct node *p, struct node *q) {
    struct node *sibling = p->right;
    sibling->left = p;
    sibling->left = 0;
}
```

```click
verifying "link.c";
resource links(p: struct node*, next: struct node*) {
    field model: int32;
    owns p->tag; owns p->right; owns p->left;
    fact p->right == next;
    fact p->left == 0;
}
void link(struct node* p, struct node* q) {
    consumes x: links(p, q);
    consumes y: links(q, 0);
    produces p->tag; produces p->right; produces p->left;
    produces q->tag; produces q->right; produces q->left;
    ensures q->left == p;
} by {
    unfold(x); unfold(y);
    step(); step(); step();
    have sibling == q by { simp(); }
    have sibling->left == p by { simp(); }
    mark stored;
    step();
    have q->left == p by { normalize() using { sibling == q; at(stored, sibling->left) == p; } }
    execute(); simp();
}
```

```expect
fail: `normalize using` goal did not normalize to true using the listed conditions
```
