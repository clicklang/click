# A node's link frames across a store to its parent's link in a loop

The loop rotates a parent's right subtree (the `__rb_erase_color` case 3
shape). After `parent->right` is overwritten, the sibling's own `right` link
is compared with its value before the stores. The two reads are pointer loads
of one cell at two snapshots, so the goal is a same-block pointer equality.
The execution frontier's checked load-equality bridge proves it: the parent's
store is separated from the sibling's field by the two owned nodes of the
current composition. `assumption()` closes it only once that bridge has
published the goal.

```c filename=rotate.c
#define WRITE_ONCE(x, value) ({ typeof(x) __value = (value); (*(volatile typeof(x) *)&(x)) = __value; __value; })
struct node { unsigned long tag; struct node *right; struct node *left; };
void rotate(struct node *parent) {
    struct node *sibling, *tmp1, *tmp2;
    while (1) {
        sibling = parent->right;
        tmp2 = sibling->left;
        tmp1 = tmp2->right;
        WRITE_ONCE(sibling->left, tmp1);
        WRITE_ONCE(tmp2->right, sibling);
        WRITE_ONCE(parent->right, tmp2);
        break;
    }
}
```

```click
verifying "rotate.c";
spec enum Tree { Empty, Node(struct node*, Tree, Tree) }
resource tree(p: struct node*) {
    field model: Tree;
    match model {
        Tree::Empty => { fact p == 0; },
        Tree::Node(id, lm, rm) => {
            owns p->tag;
            owns p->right;
            owns p->left;
            owns left: tree(p->left);
            owns right: tree(p->right);
            fact p != 0;
            fact p == id;
            fact left.model == lm;
            fact right.model == rm;
        },
    }
}
void rotate(struct node* parent) {
    consumes t: tree(parent);
    requires t.model != Tree::Empty;
    requires parent->right != 0;
    requires parent->right->left != 0;
} by {
    execute_until(loop(0));
    loop {
        owns t: tree(parent);
        invariant t.model != Tree::Empty;
        invariant parent->right != 0;
        invariant parent->right->left != 0;
        decreases 0;
        initialize by simp();
        preserve by {
            match t.model {
                Tree::Empty => { contradiction(t.model == Tree::Empty); },
                Tree::Node(id, lm, rm) => {
                    let { left: l, right: s } = unfold(t);
                    match s.model {
                        Tree::Empty => {
                            unfold(s);
                            contradiction(parent->right == 0);
                        },
                        Tree::Node(sid, slm, srm) => {
                            let { left: sl, right: sr } = unfold(s);
                            match sl.model {
                                Tree::Empty => {
                                    unfold(sl);
                                    contradiction(parent->right->left == 0);
                                },
                                Tree::Node(iid, ilm, irm) => {
                                    let { left: il, right: ir } = unfold(sl);
                                    step(); step(); step(); // Read the three links.
                                    have sibling == sid;
                                    have tmp2 == iid;
                                    mark inner_inputs;
                                    step(); step(); step(); // The three link stores.
                                    have parent->right == iid;
                                    have iid->right == sid;
                                    have sid->left == tmp1;
                                    // Only the parent's store lies between the snapshot and
                                    // this read of a different node's field.
                                    have sid->right == at(inner_inputs, sid->right) by assumption();
                                    let s = fold(tree(iid->right), { model: Tree::Node(sid, irm, srm) }, { left: ir, right: sr });
                                    let i = fold(tree(parent->right), { model: Tree::Node(iid, ilm, Tree::Node(sid, irm, srm)) }, { left: il, right: s });
                                    let t = fold(tree(parent), { model: Tree::Node(id, lm, Tree::Node(iid, ilm, Tree::Node(sid, irm, srm))) }, { left: l, right: i });
                                    step(); // Leave the loop.
                                },
                            }
                        },
                    }
                },
            }
        }
    }
    execute();
}
```

```expect
pass
```
