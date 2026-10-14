# A fold does not take an unfolded child by name

A child the fold's map leaves out defaults to the in-scope resource of the
same name only while that resource is owned in folded form. Here `left` was
unfolded and not folded again, so the fold names the missing child and why
the in-scope `left` does not fill it.

```c filename=a_fold_does_not_take_an_unfolded_child_by_name.c
int32 read_left(int32* p, int32* lp, int32* rp) { return *lp; }
```

```click
verifying "a_fold_does_not_take_an_unfolded_child_by_name.c";

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
    let root = fold(tree(p), { model: old(root.model) });
    simp();
}
```

```expect
fail: fold of `tree` must supply its named child `left` in its child map: `{ left: name }`; the in-scope `left` is not owned in folded form here
```
