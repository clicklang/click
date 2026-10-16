# A loop may return a struct pointer unclassed from its tag bits

A struct-pointer parameter designates its struct, and a loop keeps that
class across the abstract iteration. Linux's red-black tree walks up with
`parent = rb_parent(node)`, which converts the parent-and-color word back to
a pointer; the converted pointer carries no class. The back edge keeps the
head's class rather than refusing: the class only adds refusals, so the
iteration checked against it covers the unclassed pointer.

```c filename=climb.c
struct node { unsigned long parent_color; struct node *left; };

#define node_parent(pc) ((struct node *)((pc) & ~3UL))

int climb(struct node *parent, void *up, int a) {
    struct node *node = 0;
    unsigned long pc = (unsigned long)up;
    while (a != 0) {
        node = parent;
        parent = node_parent(pc);
        a = a - 1;
    }
    return a;
}
```

```click
verifying "climb.c";

int32 climb(struct node *parent, void *up, int32 a) {
    requires a >= 0;
    requires a <= 10;
    requires ((uint64)up & 3u64) == 0u64;
    ensures result == 0;
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases a;
        invariant a >= 0;
        invariant a <= 10;
        preserve by {
            step();
            step();
            step();
            close_invariants();
        }
    }
    step();
    simp();
}
```

```expect
pass
```
