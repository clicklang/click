# A parent cast restated after a store lets the parent be dereferenced

The program of
[`a_parent_cast_fact_is_not_carried_across_a_store_through_another_node.md`](a_parent_cast_fact_is_not_carried_across_a_store_through_another_node.md),
with the cast fact restated after the store through `o`:
`have ((struct rb_node*)(g->__rb_parent_color & ~3)) == xid by solve();`.
`solve` carries the unfolded fact across the store, which `o`'s separately
held cell does not overlap, and the restated fact names the read the C cast
makes next. The cast result then designates `xid`, whose cells are held, and
`p->rb_left` is formed and read. Where a branch join lies between the unfold
and the cast, carry the fact through the join's `ensuring` clause, as
`examples/rbtree/rbtree-insert/rbtree_insert.click` does before each rotation.

```c filename=rbtree.h
#ifndef RBTREE_H
#define RBTREE_H
struct rb_node {
    unsigned long __rb_parent_color;
    struct rb_node *rb_right;
    struct rb_node *rb_left;
} __attribute__((aligned(sizeof(long))));
static inline struct rb_node *rb_parent(struct rb_node *r) {
    return (struct rb_node *)(r->__rb_parent_color & ~3);
}
#endif
```

```c filename=a_parent_cast_restated_after_a_store_lets_the_parent_be_dereferenced.c
#include "rbtree.h"

struct rb_node *peek(struct rb_node *g, struct rb_node *o) {
    o->__rb_parent_color = 0;
    struct rb_node *p = rb_parent(g);
    return p->rb_left;
}
```

```click
verifying "a_parent_cast_restated_after_a_store_lets_the_parent_be_dereferenced.c";

spec enum Up {
    Frame(struct rb_node*, struct rb_node*),
}

spec enum Node {
    Inner(struct rb_node*, struct rb_node*),
}

function up_identity(u: Up) -> struct rb_node* {
    match u {
        Up::Frame(identity, child) => identity,
    }
}

function node_parent(n: Node) -> struct rb_node* {
    match n {
        Node::Inner(identity, parent) => parent,
    }
}

resource node_at(p: struct rb_node*) {
    field model: Node;
    match model {
        Node::Inner(identity, parent) => {
            owns p->__rb_parent_color;
            fact p != 0;
            fact p == identity;
            fact aligned(parent, 8);
            fact p->__rb_parent_color == address(parent) + (p->__rb_parent_color & 1);
            fact ((struct rb_node*)(p->__rb_parent_color & ~3)) == parent;
        },
    }
}

resource up_at(child: struct rb_node*) {
    field model: Up;
    match model {
        Up::Frame(identity, c) => {
            owns identity->__rb_parent_color;
            owns identity->rb_left;
            owns identity->rb_right;
            fact identity != 0;
            fact aligned(identity, 8);
            fact identity->rb_left == child;
        },
    }
}

struct rb_node* peek(struct rb_node* g, struct rb_node* o) {
    consumes n: node_at(g);
    consumes o->__rb_parent_color;
    consumes u: up_at(g);
    requires node_parent(n.model) == up_identity(u.model);
    ensures 1 == 1;
} by {
    match n.model {
        Node::Inner(gid, gp) => {
            match u.model {
                Up::Frame(xid, xc) => {
                    have node_parent(Node::Inner(gid, gp)) == gp by {
                        unfold(node_parent(Node::Inner(gid, gp)));
                        normalize();
                    }
                    have up_identity(Up::Frame(xid, xc)) == xid by {
                        unfold(up_identity(Up::Frame(xid, xc)));
                        normalize();
                    }
                    have gp == xid by {
                        rewrite(gp == node_parent(Node::Inner(gid, gp)));
                        rewrite(Node::Inner(gid, gp) == n.model);
                        rewrite(xid == up_identity(Up::Frame(xid, xc)));
                        rewrite(Up::Frame(xid, xc) == u.model);
                        assumption();
                    }
                    unfold(n);
                    unfold(u);
                    step();
                    have ((struct rb_node*)(g->__rb_parent_color & ~3)) == xid by solve();
                    step();
                    step();
                    step();
                    solve();
                },
            }
        },
    }
}
```

```expect
pass
```
