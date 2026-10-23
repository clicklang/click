# `apply` cites a premise stated first with `have`

`apply(theorem(args))` looks each of the theorem's premises up among the
available facts and proves none. A premise that is not yet a fact is stated
first with a `have`, and the application cites it: here `x >= 0` from `x > 0`,
and `left == Tree::Leaf` from `left_of(tree) == Tree::Leaf` and the
constructor equation for `tree`. Without the `have`, the application is a
search miss (`apply_does_not_prove_a_missing_premise.md`).

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
