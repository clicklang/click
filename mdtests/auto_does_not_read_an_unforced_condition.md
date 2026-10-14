# `auto` does not read an unforced condition out of a definition

`auto` reads a condition out of a fact `f(args) == k` only when every way
through `f`'s definition that fails the condition ends in a constant other
than `k`
([`auto_reads_a_condition_out_of_a_definition.md`](auto_reads_a_condition_out_of_a_definition.md)).
Here `balanced(...) == 0` holds on every way that fails a condition, so the
fact forces none of them, and `auto` fails promptly.

```click
spec enum Tree {
    Leaf,
    Node(int, Tree, Tree),
}

function balanced(tree: Tree) -> int
    decreases tree
{
    match tree {
        Tree::Leaf => 1,
        Tree::Node(value, left, right) =>
            if balanced(left) == 1 {
                if balanced(right) == 1 { 1 } else { 0 }
            } else {
                0
            },
    }
}

theorem not_forced(value: int, left: Tree, right: Tree) {
    requires balanced(Tree::Node(value, left, right)) == 0;
    ensures balanced(left) == 1 by auto;
}
```

```expect
fail: could not establish `balanced(left) == 1`
```
