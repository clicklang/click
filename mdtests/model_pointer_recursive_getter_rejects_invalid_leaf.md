# Recursion cannot hide an incompatible return leaf

```click
spec enum Tree { Empty, Node(struct other*, Tree), }
function parent(t: Tree) -> struct node* decreases t {
    match t {
        Tree::Empty => 0,
        Tree::Node(p, left) => match left {
            Tree::Empty => p,
            Tree::Node(q, rest) => parent(left),
        },
    }
}
theorem unrelated() { ensures 1 == 1 by normalize(); }
```

```expect
fail: function `parent` return value requires original object class `struct node` or null
```
