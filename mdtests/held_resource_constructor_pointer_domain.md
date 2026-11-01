# Held resource facts retain constructor pointer domains

A selected resource body supplies the nominal type of its constructor fields,
just as it supplies the domains of typed function calls. Unfolding retains that
evidence so the same model can be folded again.

```c filename=constructor.c
struct node { int value; };
int marker(struct node *p) { return 0; }
```

```click
verifying "constructor.c";
spec enum Tree { Empty, Node(struct node*) }
resource tree(p: struct node*) {
    field model: Tree;
    fact model == Tree::Node(p);
}
int32 marker(struct node* p) {
    owns t: tree(p);
    ensures result == 0;
} by {
    unfold(t);
    step_until(function.exit);
    let t = fold(tree(p), { model: Tree::Node(p) });
}
```

```expect
pass
```
