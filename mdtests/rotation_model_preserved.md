# A left rotation preserves the modeled tree

The positive counterpart to `rotation_model_rejects_swapped_order.md`. The C
performs an ordinary left rotation: it moves the pivot's left subtree to the root's
right slot and hangs the root under the pivot. The contract consumes one
modeled tree and produces the returned tree with model
`heap_rotate_left(old(t.model))`, so the claim names every node address, every
payload, and all three subtrees.

The proof matches the entry model, closes the empty cases, and unfolds the
root and pivot. It checks the writes and the child pointers they preserve
before folding the lower node and the returned pivot. The swapped-order
fixture folds the tree its C actually builds and rejects the model equation.

```c filename=rotation_model_preserved.c
struct tree_node {
    int value;
    struct tree_node *left;
    struct tree_node *right;
};

struct tree_node *rotate_left(struct tree_node *root) {
    struct tree_node *pivot;
    struct tree_node *middle;

    pivot = root->right;
    middle = pivot->left;
    root->right = middle;
    pivot->left = root;
    return pivot;
}
```

```click
verifying "rotation_model_preserved.c";

spec enum HeapTree {
    Empty,
    Node(struct tree_node*, int, HeapTree, HeapTree),
}

resource tree_at(p: struct tree_node*) {
    field model: HeapTree;
    match model {
        HeapTree::Empty => { fact p == 0; },
        HeapTree::Node(identity, value, left_model, right_model) => {
            owns p->value;
            owns p->left;
            owns p->right;
            owns left: tree_at(p->left);
            owns right: tree_at(p->right);
            fact p != 0;
            fact p == identity;
            fact p->value == value;
            fact left.model == left_model;
            fact right.model == right_model;
        },
    }
}

function heap_right(tree: HeapTree) -> HeapTree {
    match tree {
        HeapTree::Empty => HeapTree::Empty,
        HeapTree::Node(node, value, left, right) => right,
    }
}

function heap_rotate_left(tree: HeapTree) -> HeapTree {
    match tree {
        HeapTree::Empty => HeapTree::Empty,
        HeapTree::Node(node, value, left, right) => match right {
            HeapTree::Empty => tree,
            HeapTree::Node(pivot_node, pivot_value, middle, far_right) =>
                HeapTree::Node(pivot_node, pivot_value,
                    HeapTree::Node(node, value, left, middle), far_right),
        },
    }
}

struct tree_node* rotate_left(struct tree_node* root) {
    consumes t: tree_at(root);
    requires t.model != HeapTree::Empty;
    requires heap_right(t.model) != HeapTree::Empty;
    produces rotated: tree_at(result);
    ensures rotated.model == heap_rotate_left(old(t.model));
} by {
    match t.model {
        HeapTree::Empty => { contradiction(t.model == HeapTree::Empty); },
        HeapTree::Node(node, value, left_model, right_model) => {
            have heap_right(t.model) == right_model by {
                rewrite(t.model, HeapTree::Node(node, value, left_model, right_model));
                unfold(heap_right(HeapTree::Node(node, value, left_model, right_model)));
                normalize();
            }
            have right_model != HeapTree::Empty by {
                rewrite(right_model, heap_right(t.model));
                close();
            }
            match right_model {
                HeapTree::Empty => { contradiction(right_model == HeapTree::Empty); },
                HeapTree::Node(pivot_node, pivot_value, middle_model, far_right_model) => {
                    let { left: l, right: r } = unfold(t);
                    let { left: m, right: z } = unfold(r);
                    step_until(function.exit);
                    have separate(memory(root->left), memory(root->right)) by { close(); }
                    have separate(memory(root->left), memory(result->left)) by { close(); }
                    have separate(statement(4).footprint, memory(root->left)) by {
                        normalize() using { separate(memory(root->left), memory(root->right)); };
                    }
                    have separate(statement(5).footprint, memory(root->left)) by {
                        normalize() using { separate(memory(root->left), memory(result->left)); };
                    }
                    have at(statement(4).exit, root->left) == at(statement(4).entry, root->left) by {
                        preserve(memory(root->left), statement(4));
                    }
                    have at(statement(5).exit, root->left) == at(statement(5).entry, root->left) by {
                        preserve(memory(root->left), statement(5));
                    }
                    have root->left == old(root->left) by {
                        rewrite(at(statement(5).exit, root->left), at(statement(5).entry, root->left));
                        rewrite(at(statement(4).exit, root->left), at(statement(4).entry, root->left));
                        close();
                    }
                    have at(statement(4).exit, root->right) == old(root->right->left) by { close(); }
                    have separate(memory(root->right), memory(result->left)) by { close(); }
                    have separate(statement(5).footprint, memory(root->right)) by {
                        normalize() using { separate(memory(root->right), memory(result->left)); };
                    }
                    have at(statement(5).exit, root->right) == at(statement(5).entry, root->right) by {
                        preserve(memory(root->right), statement(5));
                    }
                    have root->right == old(root->right->left) by {
                        rewrite(at(statement(5).exit, root->right), at(statement(5).entry, root->right));
                        close();
                    }
                    let lower = fold(tree_at(root), {
                        model: HeapTree::Node(node, value, left_model, middle_model),
                        left: l, right: m
                    });
                    have separate(memory(result->right), memory(root->right)) by { close(); }
                    have separate(statement(4).footprint, memory(result->right)) by {
                        normalize() using { separate(memory(result->right), memory(root->right)); };
                    }
                    have at(statement(4).exit, pivot->right) == at(statement(4).entry, pivot->right) by {
                        preserve(memory(result->right), statement(4));
                    }
                    have result->right == old(root->right->right) by {
                        rewrite(at(statement(4).exit, pivot->right), at(statement(4).entry, pivot->right));
                        close();
                    }
                    let rotated = fold(tree_at(result), {
                        model: HeapTree::Node(pivot_node, pivot_value,
                            HeapTree::Node(node, value, left_model, middle_model), far_right_model),
                        left: lower, right: z
                    });
                    have rotated.model == heap_rotate_left(old(t.model)) by {
                        rewrite(old(t.model), HeapTree::Node(node, value, left_model, right_model));
                        rewrite(right_model, HeapTree::Node(pivot_node, pivot_value, middle_model, far_right_model));
                        unfold(heap_rotate_left(HeapTree::Node(node, value, left_model,
                            HeapTree::Node(pivot_node, pivot_value, middle_model, far_right_model))));
                        normalize();
                    }
                    close();
                },
            }
        },
    }
}
```

```expect
pass
```
