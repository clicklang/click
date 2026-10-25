# An unfold through an alias keeps the owner's cell names

The loop havocs `t`, so `s = t` gives `s` a fresh symbolic value that the
invariant relates to `p->right` only by a fact. The node's cells are cached
at the owner's spelling `p->right`. Folding and unfolding `tree(s)` must not
cache those cells again at the alias: a second copy would carry unrelated load
names, so `s->left` and `p->right->left` would read the same cell as two
values. The read through `s` resolves through the equality to the cell already
cached at `p->right`, so the two reads are one value.
The original is line 2249 of
`examples/rbtree/rbtree-erase/rbtree_erase_color_flips_red_all.click`, where
`tmp1 = sibling->rb_left` after `unfold(ns)` disagreed with `zid->rb_left`.

```c filename=an_unfold_through_an_alias_keeps_the_owners_cell_names.c
struct node { unsigned long color; struct node *right; struct node *left; };
struct node *h(struct node *p) {
    struct node *t = p->right;
    struct node *s = 0;
    struct node *r = 0;
    int i = 0;
    while (i < 1) {
        s = t;
        r = s->left;
        t = s;
        i = i + 1;
    }
    return r;
}
```

```click
verifying "an_unfold_through_an_alias_keeps_the_owners_cell_names.c";

spec enum Tree {
    Empty,
    Node(Tree, Tree),
}

resource tree(p: struct node*) {
    field model: Tree;
    match model {
        Tree::Empty => { fact p == 0; },
        Tree::Node(l, r) => {
            owns p->color;
            owns p->left;
            owns p->right;
            owns left: tree(p->left);
            owns right: tree(p->right);
            fact left.model == l;
            fact right.model == r;
            fact p != 0;
        }
    }
}

struct node* h(struct node* p) {
    owns p->color;
    owns p->left;
    owns p->right;
    owns p->right->color;
    owns p->right->left;
    owns p->right->right;
    owns tl: tree(p->right->left);
    owns tr: tree(p->right->right);
    requires p->right != 0;
    ensures true;
} by {
    step(); step(); step(); step(); step(); step(); step(); step();
    loop {
        decreases 1 - i;
        invariant i >= 0;
        invariant t == p->right;
        invariant t != 0;
        owns p->color;
        owns p->left;
        owns p->right;
        owns p->right->color;
        owns p->right->left;
        owns p->right->right;
        owns tl: tree(p->right->left);
        owns tr: tree(p->right->right);
        initialize by simp();
        preserve by {
            step();
            have s == p->right by simp();
            let ns = fold(tree(s), { model: Tree::Node(tl.model, tr.model) }, { left: tl, right: tr });
            let { left: nl, right: nr } = unfold(ns);
            have s->left == p->right->left by assumption();
            step();
            step(); step();
            close_invariants();
        }
    }
}
```

```expect
pass
```
