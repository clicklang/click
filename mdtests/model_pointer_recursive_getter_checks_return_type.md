# Recursive pointer getters publish their checked return type

The result can be passed to a typed helper before unfolding the getter. Null
and model-field leaves satisfy the declaration; recursive calls use the same
interface and remain subject to the ordinary termination check.

```click
spec enum Tree { Empty, Node(struct node*, Tree), }
spec enum Ref { At(struct node*), }
function typed(p: struct node*) -> Ref { Ref::At(p) }
function parent(t: Tree) -> struct node* decreases t {
    match t {
        Tree::Empty => 0,
        Tree::Node(p, left) => match left {
            Tree::Empty => p,
            Tree::Node(q, rest) => parent(left),
        },
    }
}
theorem getter(t: Tree) {
    ensures typed(parent(t)) == typed(parent(t)) by normalize();
}
```

```expect
pass
```
