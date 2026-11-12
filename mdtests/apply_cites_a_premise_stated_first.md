# `apply` accepts a premise stated first with `have`

A pure theorem application exposes its formal premises as obligations. A
preceding `have` makes their implicit proofs immediate; otherwise ordinary
`solve` attempts them. Explicit `apply using` still requires selected evidence
(`apply_does_not_prove_a_missing_premise.md`).

```click
theorem needs_nonnegative(x: int32) {
    requires x >= 0;

    ensures x >= 0 by {
        assumption();
    }
}

theorem positive_premise(x: int32) {
    requires x > 0;

    ensures x >= 0 by {
        have x >= 0;
        apply(needs_nonnegative(x));
        assumption();
    }
}

spec enum Tree {
    Leaf,
    Node(int, Tree, Tree),
}

function left_of(tree: Tree) -> Tree {
    match tree {
        Tree::Leaf => Tree::Leaf,
        Tree::Node(value, left, right) => left,
    }
}

function size(tree: Tree) -> Integer
    decreases tree
{
    match tree {
        Tree::Leaf => 0,
        Tree::Node(value, left, right) => size(left) + size(right) + 1,
    }
}

theorem leaf_left_size(value: int, left: Tree, right: Tree) {
    requires left == Tree::Leaf;
    ensures size(Tree::Node(value, left, right)) == size(right) + 1 by {
        rewrite(left == Tree::Leaf);
        unfold(size(Tree::Node(value, Tree::Leaf, right)));
        unfold(size(Tree::Leaf));
        normalize();
    }
}

theorem left_leaf_from_a_match(tree: Tree, value: int, left: Tree, right: Tree) {
    requires tree == Tree::Node(value, left, right);
    requires left_of(tree) == Tree::Leaf;
    ensures size(Tree::Node(value, left, right)) == size(right) + 1 by {
        have left == Tree::Leaf;
        apply(leaf_left_size(value, left, right));
        assumption();
    }
}
```

```expect
pass
```
