# An algebraic conditional's branches have one type

Both branches of an algebraic `if` are values of the same datatype.

```click
spec enum Tree { Empty, Node(Tree, Tree) }
spec enum Shade { Light, Dark }
function pick(flag: int32) -> Tree {
    if flag == 0 { Tree::Empty } else { Shade::Dark }
}
```

```expect
fail: `if` has incompatible branch types
```
