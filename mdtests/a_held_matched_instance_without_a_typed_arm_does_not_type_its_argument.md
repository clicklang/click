# A held matched instance without a typed arm does not type its argument

Here the `Node` arm states only `p != 0`, so nothing ties `p` to the typed
`identity` field: a held `tree(q->left)` says nothing about the original object
class of `q->left`, and `Ref::At(q->left)` has no reading. The positive is
[`a_held_matched_instance_types_its_pointer_argument.md`](a_held_matched_instance_types_its_pointer_argument.md).

```c filename=a_held_matched_instance_without_a_typed_arm_does_not_type_its_argument.c
struct node { struct node *left; };

int peek(struct node *q) {
    return 0;
}
```

```click
verifying "a_held_matched_instance_without_a_typed_arm_does_not_type_its_argument.c";

spec enum Tree { Empty, Node(struct node*) }
spec enum Ref { At(struct node*) }

resource tree(p: struct node*) {
    field model: Tree;
    match model {
        Tree::Empty => { fact p == 0; },
        Tree::Node(identity) => { fact p != 0; },
    }
}

function keep(r: Ref) -> int32 { 1 }

int32 peek(struct node* q) {
    owns q->left;
    owns t: tree(q->left);
    ensures result == 0;
} by {
    have keep(Ref::At(q->left)) == 1 by { unfold(keep(Ref::At(q->left))); normalize(); }
    execute();
}
```

```expect
fail: could not lower `have` proposition
```
