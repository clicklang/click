# A fold does not take a child of another family by name

A slot left out of a fold's child map is taken by name only from an owned
resource of the family the slot declares. Here the in-scope `left` is a
`cell`, while `tree`'s `left` slot owns a `tree`, so it is not taken and the
fold names the missing child.

```c filename=a_fold_does_not_take_a_child_of_another_family_by_name.c
void join(int32* p, int32* lp, int32* rp, int32* q, int32 value) { *p = value; }
```

```click
verifying "a_fold_does_not_take_a_child_of_another_family_by_name.c";

spec enum Tree { Leaf(int32), Branch(int32, int32*, Tree, int32*, Tree) }
resource cell(p: int32*) {
    field v: int32;
    owns p[0..1];
    fact p[0] == v;
}
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

void join(int32* p, int32* lp, int32* rp, int32* q, int32 value) {
    consumes p[0..1];
    consumes l: tree(lp);
    consumes right: tree(rp);
    owns left: cell(q);
    produces root: tree(p);
} by {
    execute();
    let root = fold(tree(p), { model: Tree::Branch(value, lp, l.model, rp, right.model) });
    simp();
}
```

```expect
fail: fold of `tree` must supply its named child `left` in its child map: `{ left: name }`
```
