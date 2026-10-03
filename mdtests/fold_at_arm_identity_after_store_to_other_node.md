# A refold at the arm identity after a store to another owned node

Unfold `tree(p)`, write a field of a separately owned node `q`, and refold at
the pointer the arm bound, `id`, with the same children. The children's
arguments are `id->left` and `id->right`. The unfold seeded those cells as one
run based at `p`, and the store leaves them cached, since owned memory keeps
`q->tag` apart from them.

The load's equal-cell scan names a run slot from the byte shift between the
load and the run's base. `id` reached the base through the stated alias
`p == id`, which is filed under exactly `id`; `id + 8` has no such entry, so
the field at offset 8 missed its slot and became a fresh load after the store,
unequal to the child the unfold produced. The scan now re-expresses the load in
the run's block through the equality graph's affine class relation, which
already holds `id + 8 == p + 8`, as the per-cell path does for single cells.
`fold(tree(p), ...)` always verified.

The negatives are
[`fold_at_arm_identity_rejects_an_overwritten_child.md`](fold_at_arm_identity_rejects_an_overwritten_child.md),
[`fold_at_arm_identity_rejects_a_store_through_an_alias.md`](fold_at_arm_identity_rejects_a_store_through_an_alias.md),
and
[`fold_at_arm_identity_store_needs_the_other_node_owned.md`](fold_at_arm_identity_store_needs_the_other_node_owned.md).

```c filename=fold_at_arm_identity_after_store_to_other_node.c
struct node { struct node *left; struct node *right; int tag; };
void roundtrip(struct node *p, struct node *q) { q->tag = 1; }
```

```click
verifying "fold_at_arm_identity_after_store_to_other_node.c";

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
    owns &q->tag;
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
pass
```
