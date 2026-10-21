# A held matched instance types its pointer argument

`tree(p)` states `p == 0` in its `Empty` arm and `p == identity` in its `Node`
arm, where `identity` is a `struct node*` model field. Whichever arm a held
`tree(q->left)` is in, `q->left` is null or has original object class
`struct node`, so the typed constructor `Ref::At(q->left)` has a reading
without unfolding the instance. The refusals when an arm does not tie the
argument to a typed binding or to null are
[`a_held_matched_instance_without_a_typed_arm_does_not_type_its_argument.md`](a_held_matched_instance_without_a_typed_arm_does_not_type_its_argument.md).
The original is the saved-link fold of a folded child in
`examples/rbtree/rbtree-erase/rbtree_erase_color_flips_red_all.click`.

```c filename=a_held_matched_instance_types_its_pointer_argument.c
struct node { struct node *left; };

int peek(struct node *q) {
    return 0;
}
```

```click
verifying "a_held_matched_instance_types_its_pointer_argument.c";

spec enum Tree { Empty, Node(struct node*) }
spec enum Ref { At(struct node*) }

resource tree(p: struct node*) {
    field model: Tree;
    match model {
        Tree::Empty => { fact p == 0; },
        Tree::Node(identity) => { fact p != 0; fact p == identity; },
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
pass
```
