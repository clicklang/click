# A resource argument does not exempt the C read beside it

A contract's resource argument reads the containing `struct sized_node` as a
value, which the strict-aliasing check does not apply to
(`a_resource_argument_reads_the_containing_struct_as_a_value.md`). The C
function's own read goes through `struct other`, which does not embed a
`struct rb_node`, so that C access is still refused (C11 6.5p7).

```c filename=sized.c
struct rb_node { struct rb_node *rb_right; struct rb_node *rb_left; };
struct sized_node { struct rb_node rb; int size; };
struct other { int a; int b; int c; int d; int e; };

int wrong_container(struct rb_node *node) {
    return ((struct other *)(void *)node)->e;
}
```

```click
verifying "sized.c";

resource sized_link(node: struct rb_node*, previous: int32) {
    field model: int32;
    owns node->rb_right;
    fact model == previous;
}

int32 wrong_container(struct rb_node* node) {
    owns link: sized_link(node, ((struct sized_node*)(void*)node)->size);
    owns ((struct sized_node*)(void*)node)->size;
    ensures true;
} by {
    execute();
}
```

```expect
fail: an object of type `struct rb_node` accessed through an lvalue of type `struct other`
```
