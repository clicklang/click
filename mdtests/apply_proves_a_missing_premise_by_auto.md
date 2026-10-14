# `apply` proves a missing premise by `auto`

`apply(theorem(args))` selects each of the theorem's premises from the
context. A premise that is not an available fact is proved as a `have` by
`auto`, as a proof writes it by hand, and the application cites it: here
`x >= 0` from `x > 0`, and `left == Tree::Leaf` from `left_of(tree) ==
Tree::Leaf` and the constructor equation for `tree`. Expansion prints each such
`have` before the application's `using` block.

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

function size(tree: Tree) -> int
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
        apply(leaf_left_size(value, left, right));
        assumption();
    }
}
```

```expect
pass
```
