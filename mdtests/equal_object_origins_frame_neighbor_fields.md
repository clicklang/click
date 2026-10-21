# Equal object origins frame neighboring fields

A child resource names its node through a stored pointer. After opening it,
updating the node's parent word must preserve the neighboring child link,
using checked pointer equalities and the complete access widths.

```c filename=equal_object_origins_frame_neighbor_fields.c
#ifndef RBTREE_H
#define RBTREE_H
#define NULL 0
#define RB_RED 0
#define RB_BLACK 1

#define __WRITE_ONCE(x, value) ({ typeof(x) __value = (value); (*(volatile typeof(x) *)&(x)) = __value; __value; })
#define WRITE_ONCE(x, value) __WRITE_ONCE(x, value)
#define likely(x) (x)
#define unlikely(x) (x)
#define __always_inline inline
#define true 1

struct rb_node {
    unsigned long __rb_parent_color;
    struct rb_node *rb_right;
    struct rb_node *rb_left;
} __attribute__((aligned(sizeof(long))));

struct rb_root {
    struct rb_node *rb_node;
};

#define __rb_color(pc)     ((pc) & 1)
#define __rb_is_black(pc)  __rb_color(pc)
#define __rb_is_red(pc)    (!__rb_color(pc))
#define rb_color(rb)       __rb_color((rb)->__rb_parent_color)
#define rb_is_red(rb)      __rb_is_red((rb)->__rb_parent_color)
#define rb_is_black(rb)    __rb_is_black((rb)->__rb_parent_color)

static inline void rb_set_parent_color(struct rb_node *rb, struct rb_node *p, int32 color) {
    rb->__rb_parent_color = (unsigned long)p | color;
}

static inline struct rb_node *rb_red_parent(struct rb_node *red) {
    return (struct rb_node *)red->__rb_parent_color;
}

struct sized_node { struct rb_node rb; int32 size; };
void inner(struct rb_node *node) {
    struct rb_node *parent = rb_red_parent(node), *gparent, *tmp;
    while (1) {
        gparent = rb_red_parent(parent);
        tmp = gparent->rb_right;
        tmp = node->rb_left;
        WRITE_ONCE(parent->rb_right, tmp);
        WRITE_ONCE(node->rb_left, parent);
        rb_set_parent_color(parent, node, RB_RED);
        break;
    }
}

#endif
```

```click
target "x86_64-unknown-linux-gnu";
mode "kernel";
verifying "equal_object_origins_frame_neighbor_fields.c";
resource size_metadata(node: struct rb_node*) {
    field value: int32;
    owns ((struct sized_node*)(void*)node)->size;
    fact ((struct sized_node*)(void*)node)->size == value;
}
spec enum InnerPhase {
    Before(struct rb_node*, struct rb_node*),
    After(struct rb_node*, struct rb_node*),
}
function inner_pending(phase: InnerPhase) -> int32 {
    match phase { InnerPhase::Before(g, p) => 1, InnerPhase::After(g, p) => 0, }
}
function inner_finish(phase: InnerPhase) -> InnerPhase {
    match phase { InnerPhase::Before(g, p) => InnerPhase::After(g, p), InnerPhase::After(g, p) => InnerPhase::After(g, p), }
}
spec enum InnerNode { At(struct rb_node*, struct rb_node*, int32), }
resource inner_node(node: struct rb_node*) {
    field model: InnerNode;
    match model {
        InnerNode::At(identity, above, value) => {
            owns node->rb_left; owns node->rb_right; owns node->__rb_parent_color;
            owns ps: size_metadata(node);
            fact node == identity;
            fact node->__rb_parent_color == address(above);
            fact ((struct rb_node*)(node->__rb_parent_color & ~3)) == above;
            fact aligned(node, 8);
            fact ps.value == value;
        },
    }
}
resource inner_state(node: struct rb_node*) {
    field phase: InnerPhase;
    field parent_model: InnerNode;
    field gvalue: int32; field pvalue: int32; field nvalue: int32;
    match phase {
        InnerPhase::Before(g, p) => {
            owns g->rb_left; owns g->rb_right;
            owns parent_tree: inner_node(g->rb_left);
            owns node->rb_left; owns node->__rb_parent_color;
            owns gs: size_metadata(g);
            owns ns: size_metadata(node);
            fact gs.value == gvalue; fact ns.value == nvalue;
            fact parent_tree.model == parent_model;
            fact parent_model == InnerNode::At(p, g, pvalue);
            fact g->rb_right == 0;
            fact node->rb_left == 0;
            fact node->__rb_parent_color == address(p);
            fact ((struct rb_node*)(node->__rb_parent_color & ~3)) == p;
            fact aligned(node, 8); fact aligned(p, 8);
        },
        InnerPhase::After(g, p) => {
            owns g->rb_left; owns g->rb_right;
            owns p->rb_right; owns p->rb_left; owns p->__rb_parent_color;
            owns node->rb_left; owns node->__rb_parent_color;
            owns gs: size_metadata(g);
            owns ps: size_metadata(p);
            owns ns: size_metadata(node);
            fact gs.value == gvalue; fact ps.value == pvalue; fact ns.value == nvalue;
            fact p->rb_right == 0;
        },
    }
}
void inner(struct rb_node* node) {
    owns state: inner_state(node);
    requires inner_pending(state.phase) == 1;
    ensures state.phase == inner_finish(old(state.phase));
} by {
    match state.phase {
        InnerPhase::After(g, p) => {
            have inner_pending(state.phase) != 1 by {
                rewrite(state.phase == InnerPhase::After(g, p));
                unfold(inner_pending(InnerPhase::After(g, p))); normalize();
            }
            contradiction(inner_pending(state.phase) == 1);
        },
        InnerPhase::Before(g, p) => {
            let { gs: gs, parent_tree: parent_tree, ns: ns } = unfold(state);
                    let { ps: ps } = unfold(parent_tree);
            step(); step(); step(); step();
            have parent == p by { simp(); }
            let parent_tree = fold(inner_node(g->rb_left), { model: InnerNode::At(p, g, old(state.pvalue)) }, { ps: ps });
            let state = fold(inner_state(node), { phase: InnerPhase::Before(g, p), gvalue: old(state.gvalue), pvalue: old(state.pvalue), nvalue: old(state.nvalue), parent_model: old(state.parent_model) }, { gs: gs, parent_tree: parent_tree, ns: ns });
            loop {
                owns state: inner_state(node);
                invariant node == old(node);
                invariant state.parent_model == old(state.parent_model);
                invariant state.gvalue == old(state.gvalue);
                invariant state.pvalue == old(state.pvalue);
                invariant state.nvalue == old(state.nvalue);
                invariant parent == p;
                invariant p == old(g->rb_left);
                invariant state.phase == InnerPhase::Before(g, p);
                invariant old(state.phase) == InnerPhase::Before(g, p);
                decreases 0;
                initialize by simp();
                preserve by {
                    let { gs: gs, parent_tree: parent_tree, ns: ns } = unfold(state);
                    let { ps: ps } = unfold(parent_tree);
                    have g->rb_left == p by { assumption(); }
                    step();
                    have gparent == g by { assumption(); }
                    step(); step(); step();
                    mark after_store;
                    have at(after_store, parent->rb_right == 0) by { assumption(); }
                    step(); step();
                    have separate(memory(parent->rb_right), memory(node->rb_left)) by { assumption(); }
                    have separate(memory(parent->rb_right), memory(p->__rb_parent_color)) by { assumption(); }
                    transport(at(after_store, parent->rb_right == 0), parent->rb_right == 0) using {
                        at(after_store, parent->rb_right == 0);
                        parent == p;
                        separate(memory(parent->rb_right), memory(node->rb_left));
                        separate(memory(parent->rb_right), memory(p->__rb_parent_color));
                    };
                    have p->rb_right == 0 by { assumption(); }
                    let state = fold(inner_state(node), { phase: InnerPhase::After(g, p), gvalue: old(state.gvalue), pvalue: old(state.pvalue), nvalue: old(state.nvalue), parent_model: old(state.parent_model) }, { gs: gs, ps: ps, ns: ns });
                    have state.phase == inner_finish(old(state.phase)) by {
                        rewrite(old(state.phase) == InnerPhase::Before(g, p));
                        unfold(inner_finish(InnerPhase::Before(g, p))); assumption();
                    }
                    step();
                }
            }
            execute(); simp();
        },
    }
}
```

```expect
pass
```
