# A resource argument reads the containing struct as a value

Linux augmented rbtrees embed a `struct rb_node` in a larger node and
recover the container from the `struct rb_node *` the core code passes.
A contract states the cached `size` of that container as a resource
argument, `((struct sized_node*)(void*)old)->size`, as
`examples/rbtree/rbtree-augmented/rbtree_size_change_child.click` does. A
resource argument is a specification: it reads memory as a value, so the
strict-aliasing check, which applies to C accesses, does not apply to it
(`design/effective-types.md`). The argument is evaluated at the callee's
entry and again where the caller applies the callee's contract.

Before, the argument's read took the class `int` from its kernel type and
was refused against the parameter's `struct rb_node`. The C program's own
reads are still checked
(`a_resource_argument_does_not_exempt_the_c_read_beside_it.md`).

```c filename=sized.c
struct rb_node { struct rb_node *rb_right; struct rb_node *rb_left; };
struct sized_node { struct rb_node rb; int size; };

void clear_left(struct rb_node *old) {
    old->rb_left = 0;
}

int clear_and_size(struct rb_node *node) {
    clear_left(node);
    return ((struct sized_node *)(void *)node)->size;
}
```

```click
verifying "sized.c";

resource sized_link(node: struct rb_node*, previous: int32) {
    field model: int32;
    owns node->rb_right;
    fact model == previous;
}

void clear_left(struct rb_node* old) {
    consumes before: sized_link(old, ((struct sized_node*)(void*)old)->size);
    owns ((struct sized_node*)(void*)old)->size;
    owns old->rb_left;
    produces after: sized_link(old, ((struct sized_node*)(void*)old)->size);
    ensures after.model == old(before.model);
    ensures old->rb_left == 0;
    ensures ((struct sized_node*)(void*)old)->size == old(((struct sized_node*)(void*)old)->size);
} by {
    unfold(before);
    execute();
    let after = fold(sized_link(old, ((struct sized_node*)(void*)old)->size), { model: old(before.model) });
    simp();
}

int32 clear_and_size(struct rb_node* node) {
    owns link: sized_link(node, ((struct sized_node*)(void*)node)->size);
    owns ((struct sized_node*)(void*)node)->size;
    owns node->rb_left;
    ensures node->rb_left == 0;
    ensures result == ((struct sized_node*)(void*)node)->size;
} by {
    let { after: link } = step(clear_left(node), { before: link });
    execute();
}
```

```expect
pass
```
