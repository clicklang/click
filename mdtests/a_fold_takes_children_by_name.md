# A fold takes its children by name

A `fold` whose child map leaves out a slot takes the in-scope resource of the
slot's own name: `{ left: left, right: r }` is written `{ right: r }`, and a
map whose every child defaults is left out. Only the children of the arm the
model selects are taken, so folding a leaf beside an owned `right` leaves
`right` alone. The kernel checks the completed map as a written one.

```c filename=a_fold_takes_children_by_name.c
int32 read_left(int32* p, int32* lp, int32* rp) { return *lp; }
void init(int32* p, int32* lp, int32* rp, int32 value) { *p = value; }
```

```click
verifying "a_fold_takes_children_by_name.c";

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
    execute();
    let left = fold(tree(lp), { model: Tree::Leaf(2) });
    let root = fold(tree(p), { model: old(root.model) });
    simp();
}

void init(int32* p, int32* lp, int32* rp, int32 value) {
    consumes p[0..1];
    consumes left: tree(lp);
    consumes r: tree(rp);
    produces root: tree(p);
    ensures root.model == Tree::Branch(value, lp, old(left.model), rp, old(r.model));
} by {
    execute();
    let root = fold(tree(p), { model: Tree::Branch(value, lp, left.model, rp, r.model) }, { right: r });
    simp();
}
```

```expect
pass
```
