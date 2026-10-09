# Algebraic results in conditionals are rejected before proof lowering

A nested conditional used to evade declaration validation when both branches
were pure calls. An unused declaration must receive the same type error as a
conditional whose branches are explicit constructors or algebraic variables.
The supported algebraic result selector is an exhaustive `match`.

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
```

```expect
fail: algebraic-valued `if` expressions are not supported in function `select`
```
