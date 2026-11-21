# Scalar return checking retains algebraic constructor payload types

A matched `Color` stays algebraic when checking a conditional in an
`int32`-returning function.

```click
spec enum Color { Red, Black, }
spec enum Tree { Empty, Node(Color, Tree, Tree), }

function black(t: Tree) -> int32 {
    match t {
        Tree::Empty => 1,
        Tree::Node(c, l, r) => if c == Color::Black { 1 } else { 0 },
    }
}

theorem black_node() {
    ensures black(Tree::Node(Color::Black, Tree::Empty, Tree::Empty)) == 1 by {
        unfold(black(Tree::Node(Color::Black, Tree::Empty, Tree::Empty)));
        known();
    }
}

theorem red_node() {
    ensures black(Tree::Node(Color::Red, Tree::Empty, Tree::Empty)) == 0 by {
        unfold(black(Tree::Node(Color::Red, Tree::Empty, Tree::Empty)));
        known();
    }
}
```

```expect
pass
```
