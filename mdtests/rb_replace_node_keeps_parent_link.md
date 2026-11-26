# the frame cannot still focus the victim after the splice

`rb_replace_node` points the root cell at `new`, so the frame that was
`ctx_at(victim, root)` is now `ctx_at(new, root)` and nothing folds at the old
child. Claiming `produces d: ctx_at(victim, root)` states that the splice left
the root cell alone, and `Context::Top`'s own fact `root->rb_node == child`
refuses it.

The helper contract records the copied fields before updating the root slot.
Its caller checks the attempted fold against the resulting root link.

```c filename=rbtree.h
#ifndef RBTREE_H
#define RBTREE_H
#define NULL 0
#define RB_RED 0
#define RB_BLACK 1

#define __WRITE_ONCE(x, value) ({ typeof(x) __value = (value); (*(volatile typeof(x) *)&(x)) = __value; __value; })
#define WRITE_ONCE(x, value) __WRITE_ONCE(x, value)

struct rb_node {
    unsigned long __rb_parent_color;
    struct rb_node *rb_right;
    struct rb_node *rb_left;
} __attribute__((aligned(sizeof(long))));

struct rb_root {
    struct rb_node *rb_node;
};

static inline struct rb_node *rb_parent(struct rb_node *r) {
    return (struct rb_node *)(r->__rb_parent_color & ~3);
}

static inline unsigned long rb_color(struct rb_node *rb) {
    return rb->__rb_parent_color & 1;
}

static inline void rb_set_parent(struct rb_node *rb, struct rb_node *p) {
    rb->__rb_parent_color = rb_color(rb) | (unsigned long)p;
}

static inline void
__rb_change_child(struct rb_node *old, struct rb_node *new,
                  struct rb_node *parent, struct rb_root *root)
{
    if (parent) {
        if (parent->rb_left == old)
            WRITE_ONCE(parent->rb_left, new);
        else
            WRITE_ONCE(parent->rb_right, new);
    } else
        WRITE_ONCE(root->rb_node, new);
}

static inline void rb_replace_node(struct rb_node *victim, struct rb_node *new,
                                   struct rb_root *root)
{
    struct rb_node *parent = rb_parent(victim);

    /* Copy the pointers/colour from the victim to the replacement */
    *new = *victim;

    /* Set the surrounding nodes to point to the replacement */
    if (victim->rb_left)
        rb_set_parent(victim->rb_left, new);
    if (victim->rb_right)
        rb_set_parent(victim->rb_right, new);
    __rb_change_child(victim, new, parent, root);
}
#endif
```

```c filename=rb_replace_keeps_parent.c
#include "rbtree.h"

void replace_root_node(struct rb_node *victim, struct rb_node *new_node,
                       struct rb_node *parent, struct rb_root *root) {
    rb_replace_node(victim, new_node, root);
}
```

```click
verifying "rb_replace_keeps_parent.c";

spec enum Color { Red, Black }

spec enum RbTree {
    Empty,
    Node(struct rb_node*, struct rb_node*, Color, RbTree, RbTree),
}

spec enum Context {
    Top,
    Left(struct rb_node*, struct rb_node*, Color, RbTree, Context),
}

function color_bit(color: Color) -> int {
    match color {
        Color::Red => 0,
        Color::Black => 1,
    }
}

function rb_substitute(tree: RbTree, replacement: struct rb_node*) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(identity, parent, color, left, right) =>
            RbTree::Node(replacement, parent, color, left, right),
    }
}

resource rb_at(p: struct rb_node*) {
    field model: RbTree;
    match model {
        RbTree::Empty => { fact p == 0; },
        RbTree::Node(identity, parent, color, left_model, right_model) => {
            owns p->__rb_parent_color;
            owns p->rb_left;
            owns p->rb_right;
            owns left: rb_at(p->rb_left);
            owns right: rb_at(p->rb_right);
            fact p != 0;
            fact p == identity;
            fact aligned(p, 8);
            fact aligned(parent, 8);
            fact p->__rb_parent_color == address(parent) + (p->__rb_parent_color & 1);
            fact (p->__rb_parent_color & 1) == color_bit(color);
            fact left.model == left_model;
            fact right.model == right_model;
        },
    }
}

resource ctx_at(child: struct rb_node*, root: struct rb_root*) {
    field model: Context;
    match model {
        Context::Top => {
            owns root->rb_node;
            fact root != 0;
            fact root->rb_node == child;
        },
        Context::Left(identity, grandparent, color, sibling_model, up_model) => {
            owns identity->__rb_parent_color;
            owns identity->rb_left;
            owns identity->rb_right;
            owns sibling: rb_at(identity->rb_right);
            owns up: ctx_at(identity, root);
            fact identity != 0;
            fact aligned(identity, 8);
            fact aligned(grandparent, 8);
            fact identity->rb_left == child;
            fact identity->__rb_parent_color
                == address(grandparent) + (identity->__rb_parent_color & 1);
            fact (identity->__rb_parent_color & 1) == color_bit(color);
            fact sibling.model == sibling_model;
            fact up.model == up_model;
        },
    }
}

void rb_replace_node(struct rb_node* victim, struct rb_node* new,
                     struct rb_root* root) {
    requires victim->__rb_parent_color == 1u64;
    requires victim->rb_left == 0;
    requires victim->rb_right == 0;
    requires root->rb_node == victim;
    requires aligned(new, 8);
    views victim->__rb_parent_color;
    views victim->rb_left;
    views victim->rb_right;
    owns new->__rb_parent_color;
    owns new->rb_left;
    owns new->rb_right;
    owns root->rb_node;
    ensures root->rb_node == new;
    ensures new->rb_left == 0;
    ensures new->rb_right == 0;
    ensures new->__rb_parent_color == 1u64;
} by {
    step_until(statement(2).entry);
    have at(statement(1).region(1).exit, new->rb_left) == 0 by close();
    have new->rb_right == 0 by close();
    have new->rb_left == 0 by close();
    have new->__rb_parent_color == 1u64 by close();
    have separate(memory(root->rb_node), memory(new->__rb_parent_color)) by close();
    have separate(memory(root->rb_node), memory(new->rb_left)) by close();
    have separate(memory(root->rb_node), memory(new->rb_right)) by close();
    mark copied;
    step_until(function.exit);
    have new->rb_left == at(copied, new->rb_left) by close();
    have new->rb_right == at(copied, new->rb_right) by close();
    have new->__rb_parent_color == at(copied, new->__rb_parent_color) by close();
    close();
}

void replace_root_node(struct rb_node* victim, struct rb_node* new_node,
                       struct rb_node* parent, struct rb_root* root) {
    consumes c: ctx_at(victim, root);
    consumes t: rb_at(victim);
    consumes new_node->__rb_parent_color;
    consumes new_node->rb_left;
    consumes new_node->rb_right;
    requires parent == 0;
    requires c.model == Context::Top;
    requires t.model
        == RbTree::Node(victim, parent, Color::Black, RbTree::Empty, RbTree::Empty);
    requires victim->rb_left == 0;
    requires victim->rb_right == 0;
    requires new_node != 0;
    requires aligned(new_node, 8);
    produces d: ctx_at(victim, root);
    produces u: rb_at(new_node);
    ensures d.model == old(c.model);
    ensures u.model == rb_substitute(old(t.model), new_node);
} by {
    let { left: l, right: r } = unfold(t);
    unfold(c);
    unfold(l);
    unfold(r);
    have color_bit(Color::Black) == 1 by {
        unfold(color_bit(Color::Black));
        close();
    }
    have (victim->__rb_parent_color & 1u64) == (color_bit(Color::Black) as uint64) by close();
    have (color_bit(Color::Black) as uint64) == 1u64 by {
        rewrite(color_bit(Color::Black), 1);
        close();
    }
    have (victim->__rb_parent_color & 1u64) == 1u64 by {
        rewrite((victim->__rb_parent_color & 1u64), (color_bit(Color::Black) as uint64));
        close();
    }
    have victim->__rb_parent_color == 1u64 by close();
    step_until(function.exit);
    let l2 = fold(rb_at(new_node->rb_left), { model: RbTree::Empty });
    let r2 = fold(rb_at(new_node->rb_right), { model: RbTree::Empty });
    let u = fold(rb_at(new_node), {
        model: RbTree::Node(new_node, parent, Color::Black, RbTree::Empty, RbTree::Empty),
        left: l2, right: r2
    });
    let d = fold(ctx_at(victim, root), { model: old(c.model) });
    have u.model == rb_substitute(old(t.model), new_node) by {
        rewrite(old(t.model), RbTree::Node(victim, parent, Color::Black, RbTree::Empty, RbTree::Empty));
        unfold(rb_substitute(
            RbTree::Node(victim, parent, Color::Black, RbTree::Empty, RbTree::Empty),
            new_node));
        close();
    }
    close();
}

```

```expect
fail: fact 2 of 2 of arm `Top` is not established
```
