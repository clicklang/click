# `container_of` reads the enclosing struct

A pointer parameter's struct type says what is at its address, not what
surrounds it. A member access through a struct that embeds the parameter's
struct is consistent with that knowledge, so `container_of` from a
`struct rb_node *` to its enclosing `struct sized_node` verifies.

```c filename=container.c
struct rb_node { int value; };
struct sized_node { struct rb_node rb; int size; };
#define offsetof(TYPE, MEMBER) __builtin_offsetof(TYPE, MEMBER)
#define container_of(ptr, type, member) ({ void *__mptr = (void *)(ptr); ((type *)(__mptr - offsetof(type, member))); })

int size_of(struct rb_node *rb) {
    struct sized_node *s = container_of(rb, struct sized_node, rb);
    return s->size;
}
```

```click
verifying "container.c";

int32 size_of(struct rb_node *rb) {
    views rb[0..2];
    ensures true;
} by {
    execute();
}
```

```expect
pass
```
