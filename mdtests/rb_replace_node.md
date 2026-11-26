# `rb_replace_node` substitutes one identity in the model

The unchanged Linux `rb_replace_node` splices `new` into `victim`'s place: it
copies the packed parent word and both links with a whole-struct assignment,
retargets each existing child's parent word at `new`, and points the parent —
or the root cell — at `new`. Its model effect is exactly the identity
substitution at the focused node: `RbTree::Node(victim, parent, color, l, r)`
becomes `RbTree::Node(new, parent, color, l, r)`, with the parent payload, both
subtrees and the frame unchanged. That is `rb_substitute`.

The model is keyed by node with the parent in the payload (gap 35 in
[`roadmap/rbtree-example.md`](../roadmap/rbtree-example.md)):
`rb_at(p)` and `ctx_at(child, root)`. The wrapper pins the victim's model with
the C parameter `parent` in the payload slot, which is how `rb_parent(victim)`
and the frame are related here: with the parent inside the model rather than a
resource argument, nothing else ties the pointer the helper recomputes to the
node the frame owns.

The victim here has no children. That is what lets both `if (victim->rb_left)`
guards be decided from the requirements, and what lets the two child instances
be refolded at the new parent for free: an `RbTree::Empty` arm owns nothing and
states only `p == 0`.

All three frames are contracted. `Context::Top` sends the helper down its root
branch; `Context::Left` and `Context::Right` send it into `parent->rb_left ==
old`, whose cell the frame owns through its own `identity` payload rather than
through any C name — see the note at the end of this file.

The three wrappers use one checked contract for the existing splice helper.
The helper proves the copy once and opens the context for the root, left,
or right link update.

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

```c filename=rb_replace_node.c
#include "rbtree.h"

void replace_root_node(struct rb_node *victim, struct rb_node *new_node,
                       struct rb_node *parent, struct rb_root *root) {
    rb_replace_node(victim, new_node, root);
}

void replace_left_child(struct rb_node *victim, struct rb_node *new_node,
                        struct rb_node *parent, struct rb_node *grandparent,
                        struct rb_root *root) {
    rb_replace_node(victim, new_node, root);
}

void replace_right_child(struct rb_node *victim, struct rb_node *new_node,
                         struct rb_node *parent, struct rb_node *grandparent,
                         struct rb_root *root) {
    rb_replace_node(victim, new_node, root);
}
```

```click
verifying "rb_replace_node.c";

spec enum Color { Red, Black }

spec enum RbTree {
    Empty,
    Node(struct rb_node*, struct rb_node*, Color, RbTree, RbTree),
}

spec enum Context {
    Top,
    Left(struct rb_node*, struct rb_node*, Color, RbTree, Context),
    Right(struct rb_node*, struct rb_node*, Color, RbTree, Context),
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
        Context::Right(identity, grandparent, color, sibling_model, up_model) => {
            owns identity->__rb_parent_color;
            owns identity->rb_left;
            owns identity->rb_right;
            owns sibling: rb_at(identity->rb_left);
            owns up: ctx_at(identity, root);
            fact identity != 0;
            fact aligned(identity, 8);
            fact aligned(grandparent, 8);
            fact identity->rb_right == child;
            fact identity->__rb_parent_color
                == address(grandparent) + (identity->__rb_parent_color & 1);
            fact ((identity->__rb_parent_color & ~3) as (struct rb_node *)) == grandparent;
            fact (identity->__rb_parent_color & 1) == color_bit(color);
            fact sibling.model == sibling_model;
            fact up.model == up_model;
        },
    }
}

resource parent_tag_frame(identity: struct rb_node*, grandparent: struct rb_node*) {
    field color: Color;
    owns identity->__rb_parent_color;
    fact identity->__rb_parent_color == address(grandparent) + (identity->__rb_parent_color & 1);
    fact ((identity->__rb_parent_color & ~3) as (struct rb_node *)) == grandparent;
    fact (identity->__rb_parent_color & 1) == color_bit(color);
}

function context_parent(context: Context) -> struct rb_node* {
    match context {
        Context::Top => 0,
        Context::Left(identity, grandparent, color, sibling, up) => identity,
        Context::Right(identity, grandparent, color, sibling, up) => identity,
    }
}

function no_splice_sibling(context: Context) -> Bool {
    match context {
        Context::Top => true,
        Context::Left(identity, grandparent, color, sibling, up) => sibling == RbTree::Empty,
        Context::Right(identity, grandparent, color, sibling, up) => sibling == RbTree::Empty,
    }
}

void rb_replace_node(struct rb_node* victim, struct rb_node* new, struct rb_root* root) {
    consumes c: ctx_at(victim, root);
    consumes t: rb_at(victim);
    consumes new->__rb_parent_color;
    consumes new->rb_left;
    consumes new->rb_right;
    requires t.model ==
        RbTree::Node(victim, context_parent(c.model), Color::Black, RbTree::Empty, RbTree::Empty);
    requires no_splice_sibling(c.model);
    requires victim->rb_left == 0;
    requires victim->rb_right == 0;
    requires new != 0;
    requires aligned(new, 8);
    produces d: ctx_at(new, root);
    produces u: rb_at(new);
    ensures d.model == old(c.model);
    ensures u.model == rb_substitute(old(t.model), new);
} by {
    let { left: l, right: r } = unfold(t);
    unfold(l);
    unfold(r);
    step_until(statement(1).entry);
    have parent == context_parent(c.model) by close();
    have ((victim->__rb_parent_color & ~3u64) as (struct rb_node *)) == parent by close();
    mark before_copy;
    have victim->rb_left == 0 by close();
    have victim->rb_right == 0 by close();
    have separate(memory(new->__rb_parent_color), memory(victim->rb_left)) by close();
    have separate(memory(new->rb_left), memory(victim->rb_left)) by close();
    have separate(memory(new->rb_right), memory(victim->rb_left)) by close();
    have separate(memory(new->__rb_parent_color), memory(victim->rb_right)) by close();
    have separate(memory(new->rb_left), memory(victim->rb_right)) by close();
    have separate(memory(new->rb_right), memory(victim->rb_right)) by close();
    step_until(statement(2).entry);
    have separate(statement(1).region(0).footprint, memory(victim->rb_left)) by close() using {
        separate(memory(new->__rb_parent_color), memory(victim->rb_left));
    };
    have at(statement(1).region(0).exit, victim->rb_left) == at(statement(1).region(0).entry, victim->rb_left) by {
        preserve(memory(victim->rb_left), statement(1).region(0));
    }
    have separate(statement(1).region(1).footprint, memory(victim->rb_left)) by close() using {
        separate(memory(new->rb_left), memory(victim->rb_left));
    };
    have at(statement(1).region(1).exit, victim->rb_left) == at(statement(1).region(1).entry, victim->rb_left) by {
        preserve(memory(victim->rb_left), statement(1).region(1));
    }
    have separate(statement(1).region(2).footprint, memory(victim->rb_left)) by close() using {
        separate(memory(new->rb_right), memory(victim->rb_left));
    };
    have at(statement(1).region(2).exit, victim->rb_left) == at(statement(1).region(2).entry, victim->rb_left) by {
        preserve(memory(victim->rb_left), statement(1).region(2));
    }
    have victim->rb_left == 0 by close();
    have separate(statement(1).region(0).footprint, memory(victim->rb_right)) by close() using {
        separate(memory(new->__rb_parent_color), memory(victim->rb_right));
    };
    have at(statement(1).region(0).exit, victim->rb_right) == at(statement(1).region(0).entry, victim->rb_right) by {
        preserve(memory(victim->rb_right), statement(1).region(0));
    }
    have separate(statement(1).region(1).footprint, memory(victim->rb_right)) by close() using {
        separate(memory(new->rb_left), memory(victim->rb_right));
    };
    have at(statement(1).region(1).exit, victim->rb_right) == at(statement(1).region(1).entry, victim->rb_right) by {
        preserve(memory(victim->rb_right), statement(1).region(1));
    }
    have separate(statement(1).region(2).footprint, memory(victim->rb_right)) by close() using {
        separate(memory(new->rb_right), memory(victim->rb_right));
    };
    have at(statement(1).region(2).exit, victim->rb_right) == at(statement(1).region(2).entry, victim->rb_right) by {
        preserve(memory(victim->rb_right), statement(1).region(2));
    }
    have victim->rb_right == 0 by close();
    have at(statement(1).region(1).exit, new->rb_left) == 0 by close();
    have new->rb_left == 0 by close();
    have new->rb_right == 0 by close();
    have new->__rb_parent_color == old(victim->__rb_parent_color) by close();
    have new->__rb_parent_color == at(before_copy, victim->__rb_parent_color) by close();
    have ((new->__rb_parent_color & ~3u64) as (struct rb_node *)) == parent by {
        rewrite(new->__rb_parent_color, at(before_copy, victim->__rb_parent_color));
        close();
    }
    let l2 = fold(rb_at(0), { model: RbTree::Empty });
    let r2 = fold(rb_at(0), { model: RbTree::Empty });
    let u = fold(rb_at(new), {
        model: RbTree::Node(new, parent, Color::Black, RbTree::Empty, RbTree::Empty),
        left: l2, right: r2
    });
    have old(t.model) == RbTree::Node(victim, parent, Color::Black, RbTree::Empty, RbTree::Empty) by close();
    have u.model == rb_substitute(old(t.model), new) by {
        rewrite(old(t.model), RbTree::Node(victim, parent, Color::Black, RbTree::Empty, RbTree::Empty));
        unfold(rb_substitute(RbTree::Node(victim, parent, Color::Black, RbTree::Empty, RbTree::Empty), new));
        close();
    }
    match c.model {
        Context::Top => {
            have context_parent(Context::Top) == 0 by {
                unfold(context_parent(Context::Top));
                close();
            }
            have context_parent(c.model) == 0 by {
                rewrite(c.model, Context::Top);
                close();
            }
            have parent == 0 by close();
            unfold(c);
            step_until(function.exit);
            have root->rb_node == new by close();
            let d = fold(ctx_at(new, root), { model: Context::Top });
            close();
        },
        Context::Left(identity, grandparent, color, sibling, up) => {
            have context_parent(Context::Left(identity, grandparent, color, sibling, up)) == identity by {
                unfold(context_parent(Context::Left(identity, grandparent, color, sibling, up)));
                close();
            }
            have context_parent(c.model) == identity by {
                rewrite(c.model, Context::Left(identity, grandparent, color, sibling, up));
                close();
            }
            have parent == identity by close();
            have no_splice_sibling(Context::Left(identity, grandparent, color, sibling, up)) by {
                have no_splice_sibling(c.model) by close();
                rewrite(Context::Left(identity, grandparent, color, sibling, up), c.model);
                close();
            }
            unfold(no_splice_sibling(Context::Left(identity, grandparent, color, sibling, up)));
            have sibling == RbTree::Empty by close();
            let { sibling: s, up: outer } = unfold(c);
            let saved_tag = fold(parent_tag_frame(identity, grandparent), { color: color });
            unfold(s);
            have identity->rb_left == victim by close();
            have identity->rb_right == 0 by close();
            have separate(memory(identity->rb_left), memory(identity->rb_right)) by close();
            step_until(function.exit);
            have identity->rb_left == new by close();
            have identity->rb_right == 0 by close();
            unfold(saved_tag);
            let s2 = fold(rb_at(0), { model: RbTree::Empty });
            let d = fold(ctx_at(new, root), { model: Context::Left(identity, grandparent, color, sibling, up), sibling: s2, up: outer });
            close();
        },
        Context::Right(identity, grandparent, color, sibling, up) => {
            have context_parent(Context::Right(identity, grandparent, color, sibling, up)) == identity by {
                unfold(context_parent(Context::Right(identity, grandparent, color, sibling, up)));
                close();
            }
            have context_parent(c.model) == identity by {
                rewrite(c.model, Context::Right(identity, grandparent, color, sibling, up));
                close();
            }
            have parent == identity by close();
            have no_splice_sibling(Context::Right(identity, grandparent, color, sibling, up)) by {
                have no_splice_sibling(c.model) by close();
                rewrite(Context::Right(identity, grandparent, color, sibling, up), c.model);
                close();
            }
            unfold(no_splice_sibling(Context::Right(identity, grandparent, color, sibling, up)));
            have sibling == RbTree::Empty by close();
            let { sibling: s, up: outer } = unfold(c);
            let saved_tag = fold(parent_tag_frame(identity, grandparent), { color: color });
            unfold(s);
            have identity->rb_right == victim by close();
            have identity->rb_left == 0 by close();
            have separate(memory(identity->rb_right), memory(identity->rb_left)) by close();
            step_until(function.exit);
            have identity->rb_right == new by close();
            have identity->rb_left == 0 by close();
            unfold(saved_tag);
            let s2 = fold(rb_at(0), { model: RbTree::Empty });
            let d = fold(ctx_at(new, root), { model: Context::Right(identity, grandparent, color, sibling, up), sibling: s2, up: outer });
            close();
        },
    }
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
    produces d: ctx_at(new_node, root);
    produces u: rb_at(new_node);
    ensures d.model == old(c.model);
    ensures u.model == rb_substitute(old(t.model), new_node);
} by {
    have context_parent(c.model) == parent by {
        rewrite(c.model, Context::Top);
        unfold(context_parent(Context::Top));
        close();
    }
    have no_splice_sibling(c.model) by {
        rewrite(c.model, Context::Top);
        unfold(no_splice_sibling(Context::Top));
        close();
    }
    have t.model == RbTree::Node(victim, context_parent(c.model), Color::Black, RbTree::Empty, RbTree::Empty) by {
        rewrite(context_parent(c.model), parent);
        close();
    }
    let { d: d, u: u } = step(rb_replace_node, { c: c, t: t });
    step_until(function.exit);
    close();
}


void replace_left_child(struct rb_node* victim, struct rb_node* new_node,
                        struct rb_node* parent, struct rb_node* grandparent,
                        struct rb_root* root) {
    consumes c: ctx_at(victim, root);
    consumes t: rb_at(victim);
    consumes new_node->__rb_parent_color;
    consumes new_node->rb_left;
    consumes new_node->rb_right;
    requires parent != 0;
    requires aligned(grandparent, 8);
    requires c.model
        == Context::Left(parent, grandparent, Color::Black, RbTree::Empty, Context::Top);
    requires t.model
        == RbTree::Node(victim, parent, Color::Black, RbTree::Empty, RbTree::Empty);
    requires victim->rb_left == 0;
    requires victim->rb_right == 0;
    requires new_node != 0;
    requires aligned(new_node, 8);
    produces d: ctx_at(new_node, root);
    produces u: rb_at(new_node);
    ensures d.model == old(c.model);
    ensures u.model == rb_substitute(old(t.model), new_node);
} by {
    have context_parent(c.model) == parent by {
        rewrite(c.model, Context::Left(parent, grandparent, Color::Black, RbTree::Empty, Context::Top));
        unfold(context_parent(Context::Left(parent, grandparent, Color::Black, RbTree::Empty, Context::Top)));
        close();
    }
    have no_splice_sibling(c.model) by {
        rewrite(c.model, Context::Left(parent, grandparent, Color::Black, RbTree::Empty, Context::Top));
        unfold(no_splice_sibling(Context::Left(parent, grandparent, Color::Black, RbTree::Empty, Context::Top)));
        close();
    }
    have t.model == RbTree::Node(victim, context_parent(c.model), Color::Black, RbTree::Empty, RbTree::Empty) by {
        rewrite(context_parent(c.model), parent);
        close();
    }
    let { d: d, u: u } = step(rb_replace_node, { c: c, t: t });
    step_until(function.exit);
    close();
}
void replace_right_child(struct rb_node* victim, struct rb_node* new_node,
                        struct rb_node* parent, struct rb_node* grandparent,
                        struct rb_root* root) {
    consumes c: ctx_at(victim, root);
    consumes t: rb_at(victim);
    consumes new_node->__rb_parent_color;
    consumes new_node->rb_left;
    consumes new_node->rb_right;
    requires parent != 0;
    requires aligned(grandparent, 8);
    requires c.model
        == Context::Right(parent, grandparent, Color::Black, RbTree::Empty, Context::Top);
    requires t.model
        == RbTree::Node(victim, parent, Color::Black, RbTree::Empty, RbTree::Empty);
    requires victim->rb_left == 0;
    requires victim->rb_right == 0;
    requires new_node != 0;
    requires aligned(new_node, 8);
    produces d: ctx_at(new_node, root);
    produces u: rb_at(new_node);
    ensures d.model == old(c.model);
    ensures u.model == rb_substitute(old(t.model), new_node);
} by {
    have context_parent(c.model) == parent by {
        rewrite(c.model, Context::Right(parent, grandparent, Color::Black, RbTree::Empty, Context::Top));
        unfold(context_parent(Context::Right(parent, grandparent, Color::Black, RbTree::Empty, Context::Top)));
        close();
    }
    have no_splice_sibling(c.model) by {
        rewrite(c.model, Context::Right(parent, grandparent, Color::Black, RbTree::Empty, Context::Top));
        unfold(no_splice_sibling(Context::Right(parent, grandparent, Color::Black, RbTree::Empty, Context::Top)));
        close();
    }
    have t.model == RbTree::Node(victim, context_parent(c.model), Color::Black, RbTree::Empty, RbTree::Empty) by {
        rewrite(context_parent(c.model), parent);
        close();
    }
    let { d: d, u: u } = step(rb_replace_node, { c: c, t: t });
    step_until(function.exit);
    close();
}
```

```expect
pass
```

## Why the victim has no children here

Keeping both children `RbTree::Empty` is what lets the two `if (victim->rb_left)`
guards be decided from the requirements alone and the two child instances be
refolded at the new parent for free: an `RbTree::Empty` arm owns nothing and
states only `p == 0`. The general case, where `rb_set_parent` rewrites each
child's packed word and each child is refolded with `new` in its parent payload,
is [`rb_replace_node_with_children.md`](rb_replace_node_with_children.md).

## Reading a frame's cells through its payload

`ctx_at(child, root)`'s `Left` and `Right` arms own `identity`'s cells through
the frame's own pointer payload. A requirement pins that payload to the
wrapper's `parent`, so after `unfold(c)` the frame owns exactly `parent`'s three
cells and states `parent->rb_left == victim`. The inlined `__rb_change_child`
then reads `parent->rb_left`, and that read has to see the same cell the arm
spoke about — across `*new = *victim`, a write to a separate object whose
separation from `parent`'s cells is a resource fact and not a memory-DAG edge.

It does, because an `unfold` names the cells it exposes the way contract
lowering does, and that projection now substitutes the arm's *constructor
bindings* as well as the resource's own parameters, so a clause written over
`identity` denotes a cell it can name. Until it did, the clause did not
evaluate, the cell stayed unnamed, the copy re-minted its load identity, and
`execute()` refused with `step() requires exactly one statement successor …,
got 2`. That was gap 43 in
[`roadmap/rbtree-example.md`](../roadmap/rbtree-example.md);
its reduction is `mdtests/guard_after_sibling_write_through_unfold.md`.

The `Right` frame additionally needs `parent->rb_left == old` to be *false*. It
is: the frame's sibling is `rb_at(identity->rb_left)` at `RbTree::Empty`, so
unfolding it gives `parent->rb_left == 0` while the victim is non-null, and one
null and one non-null pointer send the helper down its `else` path with no
requirement about the left link at all (package A11).
