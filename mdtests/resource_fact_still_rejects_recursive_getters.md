# Recursive resource fact inspection remains rejected

```c filename=nested-resource.c
int marker(void) { return 0; }
```

```click
verifying "nested-resource.c";
spec enum Tree { Empty, Node(Tree, Tree) }
function depth(tree: Tree) -> int32 decreases tree {
    match tree {
        Tree::Empty => 0,
        Tree::Node(left, right) => 1 + depth(left),
    }
}
resource nested(root: int32*) {
    field model: Tree;
    owns *root;
    fact depth(model) == 0;
}
int32 marker() { ensures result == 0; } by { execute(); simp(); }
```

```expect
fail: resource `nested` fact cannot use recursive function `depth`
```
