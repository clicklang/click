# A matched-arm child of another resource family

The frame `ctx_at` is keyed by the node it holds and owns a `tree_at` child,
a resource of another family, whose model field its arm relates to a
constructor field; `Context::Top => {}` owns nothing and folds from an empty
child map.

```c filename=resource_child_of_another_family.c
struct tree_node {
    int value;
    struct tree_node *left;
    struct tree_node *right;
};

void frame_top(struct tree_node *node) {}

void frame_push(struct tree_node *node, struct tree_node *up, int value) {
    node->value = value;
}
```

```click
verifying "resource_child_of_another_family.c";

spec enum HeapTree {
    Empty,
    Node(struct tree_node*, int, HeapTree, HeapTree),
}

spec enum Context {
    Top,
    Left(struct tree_node*, int, HeapTree, Context),
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

resource ctx_at(node: struct tree_node*) {
    field model: Context;
    match model {
        Context::Top => {},
        Context::Left(up_node, value, right_model, up_model) => {
            owns node->value;
            owns node->left;
            owns node->right;
            owns right: tree_at(node->right);
            owns up: ctx_at(up_node);
            fact node != 0;
            fact node->value == value;
            fact right.model == right_model;
            fact up.model == up_model;
        },
    }
}

void frame_top(struct tree_node* node) {
    produces ctx: ctx_at(node);
    ensures ctx.model == Context::Top;
} by {
    execute();
    let ctx = fold(ctx_at(node), { model: Context::Top }, {});
    simp();
}

void frame_push(struct tree_node* node, struct tree_node* up, int value) {
    consumes node->value;
    consumes node->left;
    consumes node->right;
    consumes r: tree_at(node->right);
    consumes u: ctx_at(up);
    requires node != 0;
    produces ctx: ctx_at(node);
    ensures ctx.model == Context::Left(up, value, old(r.model), old(u.model));
} by {
    execute();
    let ctx = fold(ctx_at(node), {
        model: Context::Left(up, value, r.model, u.model)
    }, { right: r, up: u });
    simp();
}
```

```expect
pass
```
