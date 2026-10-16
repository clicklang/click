# `container_of` into an unrelated struct is refused

`container_of` is consistent with a parameter's struct type only when the
claimed container embeds it. `struct other` does not embed a
`struct rb_node`, so a member access through it is refused.

```c filename=container.c
struct rb_node { int value; };
struct other { int a; int b; };
#define offsetof(TYPE, MEMBER) __builtin_offsetof(TYPE, MEMBER)
#define container_of(ptr, type, member) ({ void *__mptr = (void *)(ptr); ((type *)(__mptr - offsetof(type, member))); })

int wrong_container(struct rb_node *rb) {
    struct other *o = container_of(rb, struct other, a);
    return o->b;
}
```

```click
verifying "container.c";

int32 wrong_container(struct rb_node *rb) {
    views rb[0..2];
    ensures true;
} by {
    execute();
}
```

```expect
fail: an object of type `struct rb_node` accessed through an lvalue of type `struct other`
```
