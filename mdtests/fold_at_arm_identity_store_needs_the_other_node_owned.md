# The store to the other node still needs its ownership

[`fold_at_arm_identity_after_store_to_other_node.md`](fold_at_arm_identity_after_store_to_other_node.md)
without `owns &q->tag`. Nothing keeps `q` apart from `p`, and the store itself
is refused before any refold is reached.

```c filename=fold_at_arm_identity_store_needs_the_other_node_owned.c
struct node { struct node *left; struct node *right; int tag; };
void roundtrip(struct node *p, struct node *q) { q->tag = 1; }
```

```click
verifying "fold_at_arm_identity_store_needs_the_other_node_owned.c";

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

void roundtrip(struct node* p, struct node* q) {
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
fail: missing resource fact `owns q[4..5]`
```
