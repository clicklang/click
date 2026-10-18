# Resource-argument equality compares pointer views

Soundness: incomplete. A caller holding the right resource is refused at a
call; nothing false is accepted.

Since #1245 (`2cee79c02`, pointer designation), matching a held named
resource against a callee's required one compares the pointer argument's
view as well as its address and designation. A caller that owns
`size_metadata(rb_old)` (the parameter's own opaque view) is refused when the
callee requires `size_metadata((struct rb_node*)(void*)node)` with
`node = container_of(rb_old, ...)` (the enclosing object's view), although
both name the same address and designation. This passed before #1245.

```c filename=sized.c
struct rb_node { struct rb_node *rb_right; struct rb_node *rb_left; };
struct sized_node { struct rb_node rb; int size; };
#define offsetof(TYPE, MEMBER) __builtin_offsetof(TYPE, MEMBER)
#define container_of(ptr, type, member) ({				\
	void *__mptr = (void *)(ptr);					\
	((type *)(__mptr - offsetof(type, member))); })

int set_size(struct sized_node *node) {
    node->size = 1;
    return 0;
}

void caller(struct rb_node *rb_old) {
    struct sized_node *old = container_of(rb_old, struct sized_node, rb);
    set_size(old);
}
```

```click
verifying "sized.c";

resource size_metadata(node: struct rb_node*) {
    field value: int32;
    owns ((struct sized_node*)(void*)node)->size;
    fact ((struct sized_node*)(void*)node)->size == value;
}

int32 set_size(struct sized_node* node) {
    owns parent: size_metadata((struct rb_node*)(void*)node);
    ensures parent.value == 1;
} by {
    unfold(parent);
    execute();
    let parent = fold(size_metadata((struct rb_node*)(void*)node), { value: 1 });
    simp();
}

void caller(struct rb_node* rb_old) {
    owns source: size_metadata(rb_old);
    ensures source.value == 1;
} by {
    step();
    step();
    step();
    step();
    step();
    step();
    step(set_size(c(old)), { parent: source });
    execute();
}
```

```expect
pass
```

On master the call is refused with `equality of resource argument 1 was not
established`. Spelling the caller's resource as
`size_metadata((struct rb_node*)(void*)rb_old)` makes it verify. The same
refusal stops `examples/rbtree/rbtree-augmented/rbtree_size_rotate.click`,
`rbtree_size_propagate.click` and `rbtree_size_propagate_tree.click`
(`compute_size(old, 0)` against a held `size_metadata(ptr<int32*>(rb_old))`).

Open design question, for the maintainer: either resource-index pointer
equality ignores the view (address and designation only), or the view is
part of a resource's identity and those three sidecars' contracts should be
respelled. Acceptance: whichever rule is chosen is documented, the
reproduction above passes or is respelled accordingly with a negative check
for a different node, and the three sidecars verify.
