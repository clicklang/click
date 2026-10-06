# Equal pointer spellings frame across an unrelated store

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
    owns &q->tag;
    requires t.model != Tree::Empty;
    ensures t.model == old(t.model);
} by {
    match t.model {
        Tree::Empty => { contradiction(t.model == Tree::Empty); },
        Tree::Node(id, lm, rm) => {
            let { left: l, right: r } = unfold(t);
            mark m;
            step();
            have id->right == p->right by { simp(); }
            have id->left == p->left by { simp(); }
            have id->tag == p->tag by { simp(); }
            have id->right == at(m, id->right) by { simp(); }
            have id->left == at(m, id->left) by { simp(); }
            have id->tag == at(m, id->tag) by { simp(); }
            let t = fold(tree(p), { model: Tree::Node(id, lm, rm) }, { left: l, right: r });
            execute();
            simp();
        },
    }
}
```

```expect
pass
```
