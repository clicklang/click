# A theorem premise retains the match arm's source names

The proof establishes `parent_is(t.model, node_parent) == 1` inside a match
arm and cites it with `apply(parent_is_holds(t.model, node_parent))`. The
selector uses the theorem's own requirement to retain a checked source
spelling of that premise. The certificate preserves the written arguments
instead of replacing the named pointer with an unspellable kernel value.

```c filename=parent_value.c
struct node {
    struct node *parent;
    int value;
};

int read_parent_value(struct node *n)
{
    struct node *p = n->parent;
    return 0;
}
```

```click
verifying "parent_value.c";

spec enum Tree {
    Empty,
    Node(struct node*, struct node*, int),
}

function parent_is(tree: Tree, q: struct node*) -> int32 {
    match tree {
        Tree::Empty => 0,
        Tree::Node(identity, parent, value) => if parent == q { 1 } else { 0 },
    }
}

theorem parent_is_holds(tree: Tree, q: struct node*) {
    requires parent_is(tree, q) == 1;

    ensures parent_is(tree, q) == 1 by assumption();
}

resource tree_at(p: struct node*) {
    field model: Tree;
    match model {
        Tree::Empty => { fact p == 0; },
        Tree::Node(identity, parent, value) => {
            owns p->parent;
            owns p->value;
            fact p != 0;
            fact p == identity;
            fact p->parent == parent;
            fact p->value == value;
        },
    }
}

int read_parent_value(struct node* n) {
    consumes t: tree_at(n);
    requires t.model != Tree::Empty;
    produces u: tree_at(n);
    ensures result == 0;
} by {
    match t.model {
        Tree::Empty => { contradiction(t.model == Tree::Empty); },
        Tree::Node(identity, node_parent, value) => {
            have parent_is(t.model, node_parent) == 1 by {
                rewrite(t.model == Tree::Node(identity, node_parent, value));
                unfold(parent_is(Tree::Node(identity, node_parent, value), node_parent));
                normalize();
            }
            have parent_is(t.model, node_parent) == 1 by {
                apply(parent_is_holds(t.model, node_parent));
                assumption();
            }
            unfold(t);
            step();
            step();
            let u = fold(tree_at(n), { model: old(t.model) });
            execute();
            simp();
        },
    }
}
```

```expect
pass
```
