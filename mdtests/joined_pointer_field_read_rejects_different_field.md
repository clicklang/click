# A joined pointer read does not identify a different field

```c filename=joined-pointer-field-read.c
struct node { uint64 tag; struct node *right; struct node *left; };
void inspect(struct node *parent) {
    struct node *root = parent;
    struct node *sibling;
    struct node *child;
    while (true) {
        sibling = parent->left;
        child = sibling->left;
        parent = child;
        break;
    }
}
```

```click
verifying "joined-pointer-field-read.c";
spec enum Identity { At(struct node*) }
spec enum Pair { At(struct node*, Identity) }
spec enum Focus { Empty, Live(struct node*) }
resource focus_at(p: struct node*) {
    field model: Focus;
    match model {
        Focus::Empty => { fact p == 0; },
        Focus::Live(identity) => { owns p->right; fact p == identity; fact p != 0; },
    }
}
resource leaf_at(p: struct node*) {
    field model: Identity;
    match model { Identity::At(identity) => { owns p->right; fact p == identity; }, }
}
resource cell(p: struct node*) {
    field model: Pair;
    match model {
        Pair::At(identity, child) => {
            owns p->left;
            owns l: leaf_at(p->left);
            fact p == identity;
            fact l.model == child;
        },
    }
}
spec enum Parent { At(struct node*, Pair, Focus) }
function parent_identity(m: Parent) -> struct node* {
    match m { Parent::At(identity, sm, fm) => identity, }
}
resource parent_at(p: struct node*) {
    field model: Parent;
    match model {
        Parent::At(identity, sm, fm) => {
            owns identity->left;
            owns identity->right;
            owns c: cell(identity->left);
            owns f: focus_at(identity->right);
            fact c.model == sm;
            fact f.model == fm;
        },
    }
}
void inspect(struct node* parent) {
    owns tree_context: parent_at(parent);
    requires parent == parent_identity(tree_context.model);
    ensures 1 == 1;
} by {
    execute_until(loop(0));
    loop {
        owns tree_context: parent_at(root);
        invariant parent == parent_identity(tree_context.model);
        decreases 0;
        initialize by simp;
        preserve by {
            match tree_context.model {
                Parent::At(pid, sm, fm) => {
                    have parent == parent_identity(Parent::At(pid, sm, fm)) by { rewrite(Parent::At(pid, sm, fm) == tree_context.model); assumption(); }
                    have parent == pid by { unfold(parent_identity(Parent::At(pid, sm, fm))); simp(); }
                    let { c: c, f: f } = unfold(tree_context);
            match c.model {
                Pair::At(model, lm) => {
                    let { l: l } = unfold(c);
                    step();
                    mark split;
                    match f.model ensuring {
                        owns nf: focus_at(parent->right);
                        fact nf.model == at(split, f.model);
                    } {
                        Focus::Empty => {
                            have at(split, f.model) == Focus::Empty;
                            unfold(f);
                            let nf = fold(focus_at(parent->right), { model: Focus::Empty });
                            have nf.model == at(split, f.model);
                        },
                        Focus::Live(identity) => {
                            have at(split, f.model) == Focus::Live(identity);
                            unfold(f);
                            let nf = fold(focus_at(parent->right), { model: Focus::Live(identity) });
                            have nf.model == at(split, f.model);
                        },
                    }
                    step();
                    match lm {
                        Identity::At(leaf) => {
                            unfold(l);
                            have sibling == model;
                            have child == leaf;
                            have sibling->left == child;
                            have model->right == leaf by {
                                rewrite(model == sibling); rewrite(leaf == child); normalize() using { sibling->left == child; }
                            }
                            let l = fold(leaf_at(parent->left->left), { model: Identity::At(leaf) });
                            let c = fold(cell(parent->left), { model: Pair::At(model, Identity::At(leaf)) }, { l: l });
                            have nf.model == fm;
                            let tree_context = fold(parent_at(root), { model: Parent::At(pid, Pair::At(model, Identity::At(leaf)), fm) }, { c: c, f: nf });
                            step(); step();
                        },
                    }
                },
            }
                },
            }
        }
    }
    execute(); simp();
}
```

```expect
fail: `normalize using` goal did not normalize to true
```
