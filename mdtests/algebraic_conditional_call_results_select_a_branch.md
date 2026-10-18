# Algebraic results in conditionals select a branch

A conditional whose branches are algebraic is an algebraic value: here a
nested conditional whose branches are pure calls. It validates like any other
algebraic expression, and unfolding the function and normalizing with the
condition decided leaves the selected branch.

```click
spec enum Tree { Empty, Node(Tree, Tree) }
function identity(tree: Tree) -> Tree { tree }
function select(tree: Tree, flag: int32) -> Tree {
    match tree {
        Tree::Empty => Tree::Empty,
        Tree::Node(left, right) =>
            if flag == 0 { identity(left) } else { identity(right) },
    }
}

theorem select_left(left: Tree, right: Tree) {
    ensures select(Tree::Node(left, right), 0) == left by {
        unfold(select(Tree::Node(left, right), 0));
        unfold(identity(left));
        normalize();
    }
}

theorem select_right(left: Tree, right: Tree, flag: int32) {
    requires flag != 0;
    ensures select(Tree::Node(left, right), flag) == right by {
        unfold(select(Tree::Node(left, right), flag));
        unfold(identity(right));
        normalize() using { flag != 0; };
    }
}
```

```expect
pass
```
