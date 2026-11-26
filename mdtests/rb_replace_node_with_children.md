# `rb_replace_node` with both children present

The general case of `mdtests/rb_replace_node.md`, on the same node-keyed model:
the victim has a left and a right child, so both `if (victim->rb_left)` guards
take their other branch and `rb_set_parent` rewrites each child's packed parent
word. Each child is then refolded at the same address with `new` in its parent
payload, which is what makes this the interesting case — a fold discharges its
body facts exactly, and the rewritten word's arm fact

```text
(((old & 1) | address(new)) & 1) == color_bit(color)
```

is only exact when `old`, the child's word as the C read it *after*
`*new = *victim`, is the same load variable the child's own arm spoke about
before that write. It is, because an `unfold` names the cells it exposes the
way contract lowering does; see
[the canonicalization internals](../docs/internals/canonicalization.md).

The frame is `Context::Top`, and the victim's model is pinned by a requirement
with the wrapper's `parent` in its payload slot, exactly as the root case does:
with the parent inside the model rather than a resource argument, that
requirement is the only thing relating the pointer `rb_parent(victim)`
recomputes to the frame. Since a requirement states one whole model and
`exists` cannot bind an ADT, the children are pinned too, and the wrapper's
extra `left_child` and `right_child` parameters name their identities the way
`mdtests/rb_set_parent_red_ors_a_zero_color.md`'s `old_parent` names a resource argument. The
grandchildren are `RbTree::Empty` and are handed straight back to each child's
refold: the C writes no cell of theirs.

The proof records separation of the victim's two link cells from the three
replacement fields, and of the right link cell from the left child's parent
word. These are the helper's relevant stores: the complete source pointers
retain their values and domains across the copy and first parent update.

No `have color_bit(Color::Red) == 0` is needed here, and adding one breaks the
proof: the fold's body-fact check is exact, and with that equality in scope the
goal reduces through it while the child's arm premise keeps the opaque
`color_bit(Color::Red)`, so the two no longer meet. The colors are concrete, so
the check matches the premise directly instead.

The helper contract records the copied links and the represented parent of
each child. Its caller folds each child through the pointer named by the
helper, then uses the copied links to fold the replacement tree.

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

```c filename=rb_replace_node_with_children.c
#include "rbtree.h"

void replace_node_with_children(struct rb_node *victim, struct rb_node *new_node,
                                struct rb_node *parent, struct rb_node *left_child,
                                struct rb_node *right_child, struct rb_root *root) {
    rb_replace_node(victim, new_node, root);
}
```

```click
verifying "rb_replace_node_with_children.c";

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

function rb_reparent(tree: RbTree, parent: struct rb_node*) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(identity, old_parent, color, left, right) =>
            RbTree::Node(identity, parent, color, left, right),
    }
}

function rb_substitute(tree: RbTree, replacement: struct rb_node*) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(identity, parent, color, left, right) =>
            RbTree::Node(replacement, parent, color,
                rb_reparent(left, replacement), rb_reparent(right, replacement)),
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
            fact ((p->__rb_parent_color & ~3) as (struct rb_node *)) == parent;
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
            fact ((identity->__rb_parent_color & ~3) as (struct rb_node *)) == grandparent;
            fact (identity->__rb_parent_color & 1) == color_bit(color);
            fact sibling.model == sibling_model;
            fact up.model == up_model;
        },
    }
}

void rb_replace_node(struct rb_node* victim, struct rb_node* new,
                     struct rb_root* root) {
    requires victim->__rb_parent_color == 1u64;
    requires victim->rb_left != 0;
    requires victim->rb_right != 0;
    requires (victim->rb_left->__rb_parent_color & 1u64) == 0u64;
    requires (victim->rb_right->__rb_parent_color & 1u64) == 0u64;
    requires root->rb_node == victim;
    requires aligned(new, 8);
    views victim->__rb_parent_color;
    views victim->rb_left;
    views victim->rb_right;
    owns victim->rb_left->__rb_parent_color;
    owns victim->rb_right->__rb_parent_color;
    owns new->__rb_parent_color;
    owns new->rb_left;
    owns new->rb_right;
    owns root->rb_node;
    ensures root->rb_node == new;
    ensures new->rb_left == old(victim->rb_left);
    ensures new->rb_right == old(victim->rb_right);
    ensures new->__rb_parent_color == 1u64;
    ensures new->rb_left->__rb_parent_color == address(new);
    ensures new->rb_right->__rb_parent_color == address(new);
    ensures victim->rb_left->__rb_parent_color == address(new);
    ensures ((victim->rb_left->__rb_parent_color & ~3u64) as (struct rb_node *)) == new;
    ensures victim->rb_right->__rb_parent_color == address(new);
    ensures ((victim->rb_right->__rb_parent_color & ~3u64) as (struct rb_node *)) == new;
} by {
    have (address(new) & 3u64) == 0u64 by close() using { aligned(new, 8); };
    apply(click::integer::uint64_mask_keep(address(new), ~3u64));
    step_until(statement(1).entry);
    have (victim->rb_left->__rb_parent_color & 1u64) == 0u64 by close();
    have (victim->rb_right->__rb_parent_color & 1u64) == 0u64 by close();
    step_until(statement(2).entry);
    // The left link is written in the middle of the aggregate copy.
    have at(statement(1).region(1).exit, new->rb_left) == old(victim->rb_left) by close();
    have new->rb_left == old(victim->rb_left) by close();
    have new->rb_right == old(victim->rb_right) by close();
    have new->__rb_parent_color == 1u64 by close();
    have separate(memory(root->rb_node), memory(new->rb_left)) by close();
    have separate(memory(victim->rb_left->__rb_parent_color), memory(new->rb_left)) by close();
    have separate(memory(victim->rb_right->__rb_parent_color), memory(new->rb_left)) by close();
    have separate(memory(root->rb_node), memory(new->rb_right)) by close();
    have separate(memory(victim->rb_left->__rb_parent_color), memory(new->rb_right)) by close();
    have separate(memory(victim->rb_right->__rb_parent_color), memory(new->rb_right)) by close();
    have separate(memory(root->rb_node), memory(new->__rb_parent_color)) by close();
    have separate(memory(victim->rb_left->__rb_parent_color), memory(new->__rb_parent_color)) by close();
    have separate(memory(victim->rb_right->__rb_parent_color), memory(new->__rb_parent_color)) by close();
    // Frame the child tags across the three stores in the copy.
    have separate(statement(1).region(0).footprint, memory(victim->rb_left->__rb_parent_color)) by close() using {
        separate(memory(victim->rb_left->__rb_parent_color), memory(new->__rb_parent_color));
    };
    have at(statement(1).region(0).exit, victim->rb_left->__rb_parent_color) == at(statement(1).region(0).entry, victim->rb_left->__rb_parent_color) by {
        preserve(memory(victim->rb_left->__rb_parent_color), statement(1).region(0));
    }
    have separate(statement(1).region(1).footprint, memory(victim->rb_left->__rb_parent_color)) by close() using {
        separate(memory(victim->rb_left->__rb_parent_color), memory(new->rb_left));
    };
    have at(statement(1).region(1).exit, victim->rb_left->__rb_parent_color) == at(statement(1).region(1).entry, victim->rb_left->__rb_parent_color) by {
        preserve(memory(victim->rb_left->__rb_parent_color), statement(1).region(1));
    }
    have separate(statement(1).region(2).footprint, memory(victim->rb_left->__rb_parent_color)) by close() using {
        separate(memory(victim->rb_left->__rb_parent_color), memory(new->rb_right));
    };
    have at(statement(1).region(2).exit, victim->rb_left->__rb_parent_color) == at(statement(1).region(2).entry, victim->rb_left->__rb_parent_color) by {
        preserve(memory(victim->rb_left->__rb_parent_color), statement(1).region(2));
    }
    have (victim->rb_left->__rb_parent_color & 1u64) == 0u64 by close();
    have separate(statement(1).region(0).footprint, memory(victim->rb_right->__rb_parent_color)) by close() using {
        separate(memory(victim->rb_right->__rb_parent_color), memory(new->__rb_parent_color));
    };
    have at(statement(1).region(0).exit, victim->rb_right->__rb_parent_color) == at(statement(1).region(0).entry, victim->rb_right->__rb_parent_color) by {
        preserve(memory(victim->rb_right->__rb_parent_color), statement(1).region(0));
    }
    have separate(statement(1).region(1).footprint, memory(victim->rb_right->__rb_parent_color)) by close() using {
        separate(memory(victim->rb_right->__rb_parent_color), memory(new->rb_left));
    };
    have at(statement(1).region(1).exit, victim->rb_right->__rb_parent_color) == at(statement(1).region(1).entry, victim->rb_right->__rb_parent_color) by {
        preserve(memory(victim->rb_right->__rb_parent_color), statement(1).region(1));
    }
    have separate(statement(1).region(2).footprint, memory(victim->rb_right->__rb_parent_color)) by close() using {
        separate(memory(victim->rb_right->__rb_parent_color), memory(new->rb_right));
    };
    have at(statement(1).region(2).exit, victim->rb_right->__rb_parent_color) == at(statement(1).region(2).entry, victim->rb_right->__rb_parent_color) by {
        preserve(memory(victim->rb_right->__rb_parent_color), statement(1).region(2));
    }
    have (victim->rb_right->__rb_parent_color & 1u64) == 0u64 by close();
    have separate(memory(victim->rb_left->__rb_parent_color), memory(victim->rb_right->__rb_parent_color)) by close();
    have separate(memory(victim->rb_left->__rb_parent_color), memory(victim->rb_right)) by close();
    mark copied;
    step_until(statement(3).entry);
    // Read the left child's parent at the update that wrote it.
    have new->rb_left == at(copied, new->rb_left) by close();
    have new->rb_right == at(copied, new->rb_right) by close();
    have victim->rb_left->__rb_parent_color == address(new) by {
        rewrite(at(copied, victim->rb_left->__rb_parent_color & 1u64), 0u64);
        close();
    }
    have victim->rb_left->__rb_parent_color == address(new) by close();
    have (victim->rb_left->__rb_parent_color & ~3u64) == address(new) by {
        rewrite(victim->rb_left->__rb_parent_color, address(new));
        close() using { (address(new) & ~3u64) == address(new); };
    }
    have ((victim->rb_left->__rb_parent_color & ~3u64) as (struct rb_node *)) == new by close();
    have separate(statement(2).statement(0).footprint, memory(victim->rb_right)) by close();
    have at(statement(2).statement(0).exit, victim->rb_right) == at(statement(2).statement(0).entry, victim->rb_right) by {
        preserve(memory(victim->rb_right), statement(2).statement(0));
    }
    have victim->rb_right == at(copied, victim->rb_right) by close();
    have separate(statement(2).statement(0).footprint, memory(victim->rb_right->__rb_parent_color)) by close();
    have at(statement(2).statement(0).exit, victim->rb_right->__rb_parent_color) == at(statement(2).statement(0).entry, victim->rb_right->__rb_parent_color) by {
        preserve(memory(victim->rb_right->__rb_parent_color), statement(2).statement(0));
    }
    have victim->rb_right->__rb_parent_color == at(copied, victim->rb_right->__rb_parent_color) by close();
    have (victim->rb_right->__rb_parent_color & 1u64) == 0u64 by {
        rewrite(victim->rb_right->__rb_parent_color, at(copied, victim->rb_right->__rb_parent_color));
        close() using { at(copied, (victim->rb_right->__rb_parent_color & 1u64) == 0u64); };
    }
    mark after_left;
    step_until(statement(4).entry);
    have at(statement(3).statement(0).exit, victim->rb_right->__rb_parent_color) == address(new) by {
        rewrite(at(after_left, victim->rb_right->__rb_parent_color & 1u64), 0u64);
        close();
    }
    have victim->rb_right->__rb_parent_color == address(new) by close();
    have (victim->rb_right->__rb_parent_color & ~3u64) == address(new) by {
        rewrite(victim->rb_right->__rb_parent_color, address(new));
        close() using { (address(new) & ~3u64) == address(new); };
    }
    have ((victim->rb_right->__rb_parent_color & ~3u64) as (struct rb_node *)) == new by close();
    have separate(statement(3).statement(0).footprint, memory(victim->rb_left)) by close();
    have at(statement(3).statement(0).exit, victim->rb_left) == at(statement(3).statement(0).entry, victim->rb_left) by {
        preserve(memory(victim->rb_left), statement(3).statement(0));
    }
    have victim->rb_left == at(after_left, victim->rb_left) by close();
    have separate(statement(3).statement(0).footprint, memory(victim->rb_left->__rb_parent_color)) by close();
    have at(statement(3).statement(0).exit, victim->rb_left->__rb_parent_color) == at(statement(3).statement(0).entry, victim->rb_left->__rb_parent_color) by {
        preserve(memory(victim->rb_left->__rb_parent_color), statement(3).statement(0));
    }
    have victim->rb_left->__rb_parent_color == at(after_left, victim->rb_left->__rb_parent_color) by close();
    have victim->rb_left->__rb_parent_color == address(new) by close();
    have new->rb_right == at(copied, new->rb_right) by close();
    have new->rb_right == victim->rb_right by close();
    have new->rb_right->__rb_parent_color == address(new) by {
        close() using { victim->rb_right->__rb_parent_color == address(new); };
    }
    have new->rb_left == at(copied, new->rb_left) by close();
    have separate(statement(2).statement(0).footprint, memory(new->__rb_parent_color)) by close();
    have at(statement(2).statement(0).exit, new->__rb_parent_color) == at(statement(2).statement(0).entry, new->__rb_parent_color) by {
        preserve(memory(new->__rb_parent_color), statement(2).statement(0));
    }
    have separate(statement(3).statement(0).footprint, memory(new->__rb_parent_color)) by close();
    have at(statement(3).statement(0).exit, new->__rb_parent_color) == at(statement(3).statement(0).entry, new->__rb_parent_color) by {
        preserve(memory(new->__rb_parent_color), statement(3).statement(0));
    }
    have new->__rb_parent_color == at(copied, new->__rb_parent_color) by close();
    have separate(memory(root->rb_node), memory(new->rb_left->__rb_parent_color)) by close();
    have separate(memory(root->rb_node), memory(new->rb_right->__rb_parent_color)) by close();
    mark reparented;
    step_until(function.exit);
    // The root write preserves the copied links and both child tags.
    have separate(statement(4).footprint, memory(new->rb_left)) by close();
    have at(statement(4).exit, new->rb_left) == at(statement(4).entry, new->rb_left) by {
        preserve(memory(new->rb_left), statement(4));
    }
    have separate(statement(4).footprint, memory(new->rb_right)) by close();
    have at(statement(4).exit, new->rb_right) == at(statement(4).entry, new->rb_right) by {
        preserve(memory(new->rb_right), statement(4));
    }
    have separate(statement(4).footprint, memory(new->__rb_parent_color)) by close();
    have at(statement(4).exit, new->__rb_parent_color) == at(statement(4).entry, new->__rb_parent_color) by {
        preserve(memory(new->__rb_parent_color), statement(4));
    }
    have separate(statement(4).footprint, memory(victim->rb_left)) by close();
    have at(statement(4).exit, victim->rb_left) == at(statement(4).entry, victim->rb_left) by {
        preserve(memory(victim->rb_left), statement(4));
    }
    have separate(statement(4).footprint, memory(victim->rb_right)) by close();
    have at(statement(4).exit, victim->rb_right) == at(statement(4).entry, victim->rb_right) by {
        preserve(memory(victim->rb_right), statement(4));
    }
    have separate(statement(4).footprint, memory(victim->rb_left->__rb_parent_color)) by close();
    have at(statement(4).exit, victim->rb_left->__rb_parent_color) == at(statement(4).entry, victim->rb_left->__rb_parent_color) by {
        preserve(memory(victim->rb_left->__rb_parent_color), statement(4));
    }
    have separate(statement(4).footprint, memory(victim->rb_right->__rb_parent_color)) by close();
    have at(statement(4).exit, victim->rb_right->__rb_parent_color) == at(statement(4).entry, victim->rb_right->__rb_parent_color) by {
        preserve(memory(victim->rb_right->__rb_parent_color), statement(4));
    }
    have new->rb_left == at(reparented, new->rb_left) by close();
    have new->rb_right == at(reparented, new->rb_right) by close();
    have new->__rb_parent_color == at(reparented, new->__rb_parent_color) by close();
    have new->rb_left->__rb_parent_color == at(reparented, new->rb_left->__rb_parent_color) by close();
    have new->rb_right->__rb_parent_color == at(reparented, new->rb_right->__rb_parent_color) by close();
    have victim->rb_left->__rb_parent_color == at(statement(2).statement(0).exit, victim->rb_left->__rb_parent_color) by close();
    have ((victim->rb_left->__rb_parent_color & ~3u64) as (struct rb_node *)) == new by {
        rewrite(victim->rb_left->__rb_parent_color, at(statement(2).statement(0).exit, victim->rb_left->__rb_parent_color));
        close();
    }
    have victim->rb_right->__rb_parent_color == at(statement(3).statement(0).exit, victim->rb_right->__rb_parent_color) by close();
    have ((victim->rb_right->__rb_parent_color & ~3u64) as (struct rb_node *)) == new by {
        rewrite(victim->rb_right->__rb_parent_color, at(statement(3).statement(0).exit, victim->rb_right->__rb_parent_color));
        close();
    }
    close();
}

void replace_node_with_children(struct rb_node* victim, struct rb_node* new_node,
                                struct rb_node* parent, struct rb_node* left_child,
                                struct rb_node* right_child, struct rb_root* root) {
    consumes c: ctx_at(victim, root);
    consumes t: rb_at(victim);
    consumes new_node->__rb_parent_color;
    consumes new_node->rb_left;
    consumes new_node->rb_right;
    requires parent == 0;
    requires c.model == Context::Top;
    requires t.model == RbTree::Node(victim, parent, Color::Black,
        RbTree::Node(left_child, victim, Color::Red, RbTree::Empty, RbTree::Empty),
        RbTree::Node(right_child, victim, Color::Red, RbTree::Empty, RbTree::Empty));
    requires new_node != 0;
    requires aligned(new_node, 8);
    produces d: ctx_at(new_node, root);
    produces u: rb_at(new_node);
    ensures d.model == old(c.model);
    ensures u.model == rb_substitute(old(t.model), new_node);
} by {
    let { left: l, right: r } = unfold(t);
    unfold(c);
    let { left: ll, right: lr } = unfold(l);
    let { left: rl, right: rr } = unfold(r);
    have separate(memory(victim->rb_left), memory(new_node->__rb_parent_color));
    have separate(memory(victim->rb_left), memory(new_node->rb_left));
    have separate(memory(victim->rb_left), memory(new_node->rb_right));
    have separate(memory(victim->rb_right), memory(new_node->__rb_parent_color));
    have separate(memory(victim->rb_right), memory(new_node->rb_left));
    have separate(memory(victim->rb_right), memory(new_node->rb_right));
    have separate(memory(victim->rb_right), memory(left_child->__rb_parent_color));
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
    have victim->__rb_parent_color == address(parent) + (victim->__rb_parent_color & 1u64) by close();
    have address(parent) == 0u64 by {
        rewrite(parent, 0);
        close();
    }
    have victim->__rb_parent_color == 1u64 by {
        rewrite(victim->__rb_parent_color, address(parent) + (victim->__rb_parent_color & 1u64));
        rewrite(address(parent), 0u64);
        rewrite((victim->__rb_parent_color & 1u64), 1u64);
        close();
    }
    have color_bit(Color::Red) == 0 by {
        unfold(color_bit(Color::Red));
        close();
    }
    have (color_bit(Color::Red) as uint64) == 0u64 by {
        rewrite(color_bit(Color::Red), 0);
        close();
    }
    have (victim->rb_left->__rb_parent_color & 1u64) == (color_bit(Color::Red) as uint64) by close();
    have (victim->rb_left->__rb_parent_color & 1u64) == 0u64 by {
        rewrite((victim->rb_left->__rb_parent_color & 1u64), (color_bit(Color::Red) as uint64));
        close();
    }
    have (victim->rb_right->__rb_parent_color & 1u64) == (color_bit(Color::Red) as uint64) by close();
    have (victim->rb_right->__rb_parent_color & 1u64) == 0u64 by {
        rewrite((victim->rb_right->__rb_parent_color & 1u64), (color_bit(Color::Red) as uint64));
        close();
    }
    step_until(function.exit);
    have (address(new_node) & 1u64) == 0u64 by close();
    have victim->rb_left->__rb_parent_color == address(new_node) by close();
    have (victim->rb_left->__rb_parent_color & 1u64) == 0u64 by {
        rewrite(victim->rb_left->__rb_parent_color, address(new_node));
        close();
    }
    have victim->rb_left->__rb_parent_color == address(new_node) + (victim->rb_left->__rb_parent_color & 1u64) by {
        rewrite((victim->rb_left->__rb_parent_color & 1u64), 0u64);
        close();
    }
    have victim->rb_right->__rb_parent_color == address(new_node) by close();
    have (victim->rb_right->__rb_parent_color & 1u64) == 0u64 by {
        rewrite(victim->rb_right->__rb_parent_color, address(new_node));
        close();
    }
    have victim->rb_right->__rb_parent_color == address(new_node) + (victim->rb_right->__rb_parent_color & 1u64) by {
        rewrite((victim->rb_right->__rb_parent_color & 1u64), 0u64);
        close();
    }
    let l2 = fold(rb_at(victim->rb_left), {
        model: RbTree::Node(left_child, new_node, Color::Red, RbTree::Empty, RbTree::Empty),
        left: ll, right: lr
    });
    let r2 = fold(rb_at(victim->rb_right), {
        model: RbTree::Node(right_child, new_node, Color::Red, RbTree::Empty, RbTree::Empty),
        left: rl, right: rr
    });
    let u = fold(rb_at(new_node), {
        model: RbTree::Node(new_node, parent, Color::Black,
            RbTree::Node(left_child, new_node, Color::Red, RbTree::Empty, RbTree::Empty),
            RbTree::Node(right_child, new_node, Color::Red, RbTree::Empty, RbTree::Empty)),
        left: l2, right: r2
    });
    let d = fold(ctx_at(new_node, root), { model: old(c.model) });
    have u.model == rb_substitute(old(t.model), new_node) by {
        rewrite(old(t.model), RbTree::Node(victim, parent, Color::Black,
            RbTree::Node(left_child, victim, Color::Red, RbTree::Empty, RbTree::Empty),
            RbTree::Node(right_child, victim, Color::Red, RbTree::Empty, RbTree::Empty)));
        unfold(rb_substitute(RbTree::Node(victim, parent, Color::Black,
            RbTree::Node(left_child, victim, Color::Red, RbTree::Empty, RbTree::Empty),
            RbTree::Node(right_child, victim, Color::Red, RbTree::Empty, RbTree::Empty)),
            new_node));
        unfold(rb_reparent(
            RbTree::Node(left_child, victim, Color::Red, RbTree::Empty, RbTree::Empty),
            new_node));
        unfold(rb_reparent(
            RbTree::Node(right_child, victim, Color::Red, RbTree::Empty, RbTree::Empty),
            new_node));
        close();
    }
    close();
}
```

```expect
pass
```
