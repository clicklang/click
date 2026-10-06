# A changed cell cannot frame through an equal pointer spelling

```c filename=spelling.c
struct node { struct node *left; struct node *right; int tag; };
void roundtrip(struct node *p, struct node *q) { q->tag = 1; }
```

```click
verifying "spelling.c";
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
    requires q == p;
    requires p->tag == 0;
    ensures t.model == old(t.model);
} by {
    match t.model {
        Tree::Empty => { contradiction(t.model == Tree::Empty); },
        Tree::Node(id, lm, rm) => {
            let { left: l, right: r } = unfold(t);
            mark m;
            step();
            have id->tag == at(m, id->tag) by { simp(); }
            let t = fold(tree(p), { model: Tree::Node(id, lm, rm) }, { left: l, right: r });
            execute();
            simp();
        },
    }
}
```

```expect
fail: could not establish `id->tag == at(m, id->tag)`
```
