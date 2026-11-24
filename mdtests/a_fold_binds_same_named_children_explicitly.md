# A fold binds same-named children explicitly

A fold names each child of the selected arm in its input map, even when
the held resource has the same name as the slot. A fold of a leaf supplies
no children.

```c filename=a_fold_binds_same_named_children_explicitly.c
int32 read_left(int32* p, int32* lp, int32* rp) { return *lp; }
void init(int32* p, int32* lp, int32* rp, int32 value) { *p = value; }
```

```click
verifying "a_fold_binds_same_named_children_explicitly.c";

spec enum Tree { Leaf(int32), Branch(int32, int32*, Tree, int32*, Tree) }
resource tree(p: int32*) {
    field model: Tree;
    match model {
        Tree::Leaf(value) => { owns p[0..1]; fact p[0] == value; },
        Tree::Branch(value, lp, lm, rp, rm) => {
            owns p[0..1];
            owns left: tree(lp);
            owns right: tree(rp);
            fact p[0] == value;
            fact left.model == lm;
            fact right.model == rm;
        },
    }
}

int32 read_left(int32* p, int32* lp, int32* rp) {
    owns root: tree(p);
    requires root.model == Tree::Branch(1, lp, Tree::Leaf(2), rp, Tree::Leaf(3));
    ensures result == 2;
    ensures root.model == old(root.model);
} by {
    let { left: left, right: right } = unfold(root);
    unfold(left);
    step_until(function.exit);
    let left = fold(tree(lp), { model: Tree::Leaf(2) });
    let root = fold(tree(p), { model: old(root.model), left: left, right: right });
    close();
}

void init(int32* p, int32* lp, int32* rp, int32 value) {
    consumes p[0..1];
    consumes left: tree(lp);
    consumes r: tree(rp);
    produces root: tree(p);
    ensures root.model == Tree::Branch(value, lp, old(left.model), rp, old(r.model));
} by {
    step_until(function.exit);
    let root = fold(tree(p), { model: Tree::Branch(value, lp, left.model, rp, r.model), left: left, right: r });
    close();
}
```

```expect
pass
```
