# A full pointer rewrite keeps a constructor field's checked object type

The model's parent equals the pointer loaded into the C local. Rewriting that
complete value inside a typed constructor preserves its checked object type,
even when the equality's spelling does not itself need that evidence.

```c filename=parent.c
struct node { unsigned long word; struct node *left; struct node *right; };
int parent(struct node *node) {
    struct node *gparent = (struct node *)(node->word & ~3UL);
    return 0;
}
```

```click
verifying "parent.c";

spec enum Tree { Empty, Leaf(int32) }
spec enum Wrapped { Node(struct node*, struct node*, Tree, Tree) }

resource tree(p: struct node*) {
    field model: Wrapped;
    match model {
        Wrapped::Node(id, parent, left, right) => {
            owns p->word;
            fact p == id;
            fact ((p->word & ~3) as (struct node *)) == parent;
        },
    }
}

int parent(struct node* node) {
    owns t: tree(node);
    ensures result == 0;
} by {
    match t.model {
        Wrapped::Node(id, unp, left, right) => {
            unfold(t);
            step(); step();
            have unp == gparent by { solve(); }
            have Wrapped::Node(id, unp, left, right) == Wrapped::Node(id, gparent, left, right) by {
                rewrite(unp == gparent);
                normalize();
            }
            let t = fold(tree(node), { model: Wrapped::Node(id, unp, left, right) });
            step_until(function.exit);
        },
    }
    solve();
}
```

```expect
pass
```
