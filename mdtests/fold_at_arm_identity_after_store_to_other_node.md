# A refold at the arm identity after a store to another owned node

Unfold `tree(p)`, write a field of the separately owned node `q`, and refold at
the pointer `id` bound by the arm. Two explicit transport certificates preserve
the child pointers across the store, using separation from the live ownership
partition. The effect names the C store's four-byte footprint explicitly.

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
            owns p->left;
            owns p->right;
            owns p->tag;
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
    owns q->tag;
    requires t.model != Tree::Empty;
    ensures t.model == old(t.model);
} by {
    match t.model {
        Tree::Empty => { contradiction(t.model == Tree::Empty); },
        Tree::Node(id, lm, rm) => {
            let { left: l, right: r } = unfold(t);
            have separate(memory((&q->tag as (int32 *))[0..1]), memory(p->left));
            have separate(memory((&q->tag as (int32 *))[0..1]), memory(p->right));
            mark before_store;
            step();
            mark after_store;
            have p->left == at(before_store, p->left) by {
                transport_certificate {
                    premise 0: changes_only(before_store, after_store, memory((&q->tag as (int32 *))[0..1]))
                        => changes_only(before_store, after_store, memory((&q->tag as (int32 *))[0..1]));
                    premise 1: at(before_store, separate(memory((&q->tag as (int32 *))[0..1]), memory(p->left)))
                        => at(before_store, separate(memory((&q->tag as (int32 *))[0..1]), memory(p->left)));
                    preserve 0, 1 => p->left == at(before_store, p->left);
                    conclusion 2;
                }
            }
            have p->right == at(before_store, p->right) by {
                transport_certificate {
                    premise 0: changes_only(before_store, after_store, memory((&q->tag as (int32 *))[0..1]))
                        => changes_only(before_store, after_store, memory((&q->tag as (int32 *))[0..1]));
                    premise 1: at(before_store, separate(memory((&q->tag as (int32 *))[0..1]), memory(p->right)))
                        => at(before_store, separate(memory((&q->tag as (int32 *))[0..1]), memory(p->right)));
                    preserve 0, 1 => p->right == at(before_store, p->right);
                    conclusion 2;
                }
            }
            let t = fold(tree(id), { model: Tree::Node(id, lm, rm) }, { left: l, right: r });
            step_until(function.exit);
            solve();
        },
    }
}
```

```expect
pass
```
