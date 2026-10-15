# Nested nonrecursive model getters in resource facts

```c filename=nested-resource.c
int marker(void) { return 0; }
```

```click
verifying "nested-resource.c";
spec enum Tree { Empty, Node(Tree, Tree) }
function child(tree: Tree) -> Tree {
    match tree {
        Tree::Empty => Tree::Empty,
        Tree::Node(left, right) => left,
    }
}
function leaf_value(tree: Tree) -> int32 {
    match tree {
        Tree::Empty => 0,
        Tree::Node(left, right) => 1,
    }
}
resource nested(root: int32*) {
    field model: Tree;
    owns *root;
    fact leaf_value(child(child(model))) == 0;
}
int32 marker() { ensures result == 0; } by { execute(); simp(); }
```

```expect
pass
```
