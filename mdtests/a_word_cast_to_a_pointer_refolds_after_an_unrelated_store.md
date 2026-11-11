# A word cast to a pointer refolds after an unrelated store

The rbtree parent word: a resource states that the node's tagged word, with
its tag bits cleared and cast to a pointer, is the parent. The proof unfolds
the node, the C reads the word into a local, and the proof folds the node
back. Nothing wrote the word, so the cast names one pointer before and after
the store to the local, and the fold finds the fact the unfold gave it.

The cast's provenance is the read of the word. That read was once named from
whichever memory the load ran in, so any store between the unfold and the
fold gave the same read a second name and the fold was refused.

```c filename=word_cast_refold.c
struct rb_node {
    unsigned long __rb_parent_color;
    struct rb_node *rb_right;
    struct rb_node *rb_left;
};

void probe(struct rb_node *node) {
    struct rb_node *parent = (struct rb_node *)(node->__rb_parent_color & ~3);
}
```

```click
verifying "word_cast_refold.c";

spec enum Shape {
    Node(struct rb_node*)
}

resource tagged_at(p: struct rb_node*) {
    field model: Shape;
    match model {
        Shape::Node(parent) => {
            owns p->__rb_parent_color;
            fact ((p->__rb_parent_color & ~3) as (struct rb_node *)) == parent;
        },
    }
}

void probe(struct rb_node* node) {
    owns state: tagged_at(node);
    ensures state.model == old(state.model);
} by {
    match state.model {
        Shape::Node(ancestor) => {
            unfold(state);
            step(); step();
            let state = fold(tagged_at(node), { model: old(state.model) });
            step_until(function.exit);
        },
    }
}
```

```expect
pass
```
