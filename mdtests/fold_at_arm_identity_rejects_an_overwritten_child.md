# A refold at the arm identity sees an overwritten child field

The store of
[`fold_at_arm_identity_after_store_to_other_node.md`](fold_at_arm_identity_after_store_to_other_node.md)
moved onto the node's own `right` field. The read of `id->right` finds the
run slot the store rewrote and returns the stored null pointer, so the old
right child no longer matches and the refold is refused.

```c filename=fold_at_arm_identity_rejects_an_overwritten_child.c
struct node { struct node *left; struct node *right; int tag; };
void roundtrip(struct node *p) { p->right = 0; }
```

```click
verifying "fold_at_arm_identity_rejects_an_overwritten_child.c";

spec enum Tree { Empty, Node(struct node*, Tree, Tree) }

resource tree(p: struct node*) {
    field model: Tree;
    match model {
        Tree::Empty => { fact p == 0; },
        Tree::Node(id, lm, rm) => {
            owns &p->left;
            owns &p->right;
            owns &p->tag;
            owns left: tree(p->left);
            owns right: tree(p->right);
            fact p != 0;
            fact p == id;
            fact left.model == lm;
            fact right.model == rm;
        },
    }
}

void roundtrip(struct node* p) {
    owns t: tree(p);
    requires t.model != Tree::Empty;
    ensures t.model == old(t.model);
} by {
    match t.model {
        Tree::Empty => { contradiction(t.model == Tree::Empty); },
        Tree::Node(id, lm, rm) => {
            let { left: l, right: r } = unfold(t);
            step();
            let t = fold(tree(id), { model: Tree::Node(id, lm, rm) }, { left: l, right: r });
            execute();
            simp();
        },
    }
}
```

```expect
fail: selected child does not satisfy the proposed parent model
```
