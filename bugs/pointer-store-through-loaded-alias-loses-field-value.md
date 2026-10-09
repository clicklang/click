# Pointer store through a loaded alias loses the field value at the original name

A store through a pointer known equal to another pointer must establish the
same field value at either name. In the reduction below, `sibling == q` and
`sibling->left == p` both verify immediately after the store, but the explicit
normalization of `q->left == p` fails. There is no intervening call or write.
This blocks folding the rotated sibling in the frozen rbtree erase proof.

The failure reproduces with bounded typed pointer read-value normalization,
including offset goals and retained canonical projection sources. Do not
change the C or weaken the exact link postcondition.

```c filename=link.c
struct node { uint64 tag; struct node *right; struct node *left; };
void link(struct node *p, struct node *q) {
    struct node *sibling = p->right;
    sibling->left = p;
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
    have q->left == p by { normalize() using { sibling == q; sibling->left == p; } }
    execute(); simp();
}
```

Run `click verify link.click`. The failure is the final `have`, with
`normalize using` reporting that the listed conditions do not prove the goal.
Using `simp` there also fails in the larger three-node caller.

Acceptance: verify this unchanged caller; add a negative with a later
conflicting store or a missing alias; audit the successful proof; retain exact
pointer blocks, ABI widths, and bounded work as unrelated memory and facts grow.
Delete this bug when the fix and regressions land.
