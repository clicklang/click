# `auto` reads a condition out of a function's definition

A fact `balanced(Node(left, right)) == 1` says the definition took the way to
its `1`. When the definition reaches `1` only through `if balanced(left) == 1`,
the fact forces that condition. `auto` proves it as a proof would by hand:
`if` the condition holds it is the goal; otherwise it splits on each condition
met before it, and at each end unfolds the definition at the constructor,
normalizes with the conditions taken to a constant other than `1`, and
contradicts the fact. A fact over a value that a connected equation names as
a constructor, `balanced(tree) == 1` beside `tree == Node(..)`, is first
restated over the constructor by rewriting with that equation.

```click
spec enum Tree {
    Leaf,
    Node(int, Tree, Tree),
}

function depth(tree: Tree) -> int
    decreases tree
{
    match tree {
        Tree::Leaf => 0,
        Tree::Node(value, left, right) => depth(left) + 1,
    }
}

function balanced(tree: Tree) -> int
    decreases tree
{
    match tree {
        Tree::Leaf => 1,
        Tree::Node(value, left, right) =>
            if balanced(left) == 1 {
                if balanced(right) == 1 {
                    if depth(left) == depth(right) {
                        if value > 0 { 1 } else { 2 }
                    } else {
                        0
                    }
                } else {
                    0
                }
            } else {
                0
            },
    }
}

theorem left_balanced(value: int, left: Tree, right: Tree) {
    requires balanced(Tree::Node(value, left, right)) == 1;
    ensures balanced(left) == 1 by auto();
}

theorem right_balanced(value: int, left: Tree, right: Tree) {
    requires balanced(Tree::Node(value, left, right)) == 1;
    ensures balanced(right) == 1 by auto();
}

theorem same_depth(value: int, left: Tree, right: Tree) {
    requires balanced(Tree::Node(value, left, right)) == 1;
    ensures depth(left) == depth(right) by auto();
}

theorem positive_value(value: int, left: Tree, right: Tree) {
    requires 1 == balanced(Tree::Node(value, left, right));
    ensures value > 0 by auto();
}

theorem through_a_constructor_equation(tree: Tree, value: int, left: Tree, right: Tree) {
    requires tree == Tree::Node(value, left, right);
    requires balanced(tree) == 1;
    ensures balanced(left) == 1 by auto();
}

theorem in_a_have(value: int, left: Tree, right: Tree) {
    requires balanced(Tree::Node(value, left, right)) == 1;
    ensures balanced(left) + balanced(right) == 2 by {
        have balanced(left) == 1 by auto();
        have balanced(right) == 1 by auto();
        normalize() using { balanced(left) == 1; balanced(right) == 1; }
    }
}
```

```expect
pass
```
