# An unfolded frame's own arm is refuted from the path

The rbtree context `ctx_at(child, root)` keyed by node (package C1b). A frame's
arm owns the cells of the node its `identity` payload carries and holds the
frame above it as the child `up`, so `let { up: u } = unfold(c)` is how every
fixup step reaches its grandparent frame — and the question it asks next is
whether that frame is `Context::Top`.

Nothing at contract lowering can answer it: `u` does not exist there. What
answers it is a fact of the path — here the requirement `ctx_up_is_framed`
read through the arm this proof is in, in the fixup loops the C local
`rb_parent` has just filled in. A predicate value refutes no arm by itself,
so each `Context::Top` arm states the exclusion: it unfolds the predicate at
`Context::Top` to `0`, rewrites the model to `Top`, and closes by
`contradiction` against the known `1`. Evaluating a predicate at each arm to
find such a contradiction would be a search inside `unfold` and `match`,
which are checking steps.

The memory-free reduction, where the deciding fact is a C local the body
assigned, is
[`loop_body_refutes_an_unfolded_child.md`](loop_body_refutes_an_unfolded_child.md);
the single-frame walk this pair is cut from is
[`rb_ascending_walk_to_root.md`](rb_ascending_walk_to_root.md).

```c filename=rbtree.h
#ifndef RBTREE_H
#define RBTREE_H
#define NULL 0
#define RB_RED 0
#define RB_BLACK 1

struct rb_node {
    unsigned long __rb_parent_color;
    struct rb_node *rb_right;
    struct rb_node *rb_left;
} __attribute__((aligned(sizeof(long))));

struct rb_root {
    struct rb_node *rb_node;
};
#endif
```

```c filename=rb_refutes_the_unfolded_frame.c
#include "rbtree.h"

struct rb_node *rb_focus(struct rb_node *node, struct rb_root *root) {
    return node;
}
```

```click
verifying "rb_refutes_the_unfolded_frame.c";

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

function rb_parent_is(tree: RbTree, p: struct rb_node*) -> int32 {
    match tree {
        RbTree::Empty => 1,
        RbTree::Node(identity, parent, color, left, right) =>
            if parent == p { 1 } else { 0 },
    }
}

function ctx_node_is(ctx: Context, p: struct rb_node*) -> int32 {
    match ctx {
        Context::Top => if p == 0 { 1 } else { 0 },
        Context::Left(identity, grandparent, color, sibling_model, up_model) =>
            if identity == p { 1 } else { 0 },
        Context::Right(identity, grandparent, color, sibling_model, up_model) =>
            if identity == p { 1 } else { 0 },
    }
}

function ctx_reroot(ctx: Context, p: struct rb_node*) -> Context {
    match ctx {
        Context::Top => Context::Top,
        Context::Left(identity, grandparent, color, sibling_model, up_model) =>
            Context::Left(p, grandparent, color, sibling_model, up_model),
        Context::Right(identity, grandparent, color, sibling_model, up_model) =>
            Context::Right(p, grandparent, color, sibling_model, up_model),
    }
}

function ctx_is_framed(ctx: Context) -> int32 {
    match ctx {
        Context::Top => 0,
        Context::Left(identity, grandparent, color, sibling_model, up_model) => 1,
        Context::Right(identity, grandparent, color, sibling_model, up_model) => 1,
    }
}

function ctx_up_is_framed(ctx: Context) -> int32 {
    match ctx {
        Context::Top => 0,
        Context::Left(identity, grandparent, color, sibling_model, up_model) =>
            ctx_is_framed(up_model),
        Context::Right(identity, grandparent, color, sibling_model, up_model) =>
            ctx_is_framed(up_model),
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
            fact rb_parent_is(left_model, p) == 1;
            fact rb_parent_is(right_model, p) == 1;
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
            fact rb_parent_is(sibling_model, identity) == 1;
            fact ctx_node_is(up_model, grandparent) == 1;
            fact up_model == ctx_reroot(up_model, grandparent);
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
            fact (identity->__rb_parent_color & 1) == color_bit(color);
            fact sibling.model == sibling_model;
            fact up.model == up_model;
            fact rb_parent_is(sibling_model, identity) == 1;
            fact ctx_node_is(up_model, grandparent) == 1;
            fact up_model == ctx_reroot(up_model, grandparent);
        },
    }
}

struct rb_node* rb_focus(struct rb_node* node, struct rb_root* root) {
    consumes c: ctx_at(node, root);
    requires ctx_up_is_framed(c.model) == 1;
    ensures 1 == 1;
} by {
    match c.model {
        Context::Top => {
            have ctx_up_is_framed(Context::Top) == 0 by {
                unfold(ctx_up_is_framed(Context::Top));
                normalize();
            }
            have ctx_up_is_framed(c.model) == 0 by {
                rewrite(c.model == Context::Top);
                assumption();
            }
            have ctx_up_is_framed(c.model) != 0 by {
                rewrite(ctx_up_is_framed(c.model) == 1);
                normalize();
            }
            contradiction(ctx_up_is_framed(c.model) == 0);
        },
        Context::Left(identity, grandparent, color, sibling_model, up_model) => {
            have ctx_up_is_framed(Context::Left(identity, grandparent, color,
                                                sibling_model, up_model))
                == ctx_is_framed(up_model) by {
                unfold(ctx_up_is_framed(Context::Left(identity, grandparent, color,
                                                      sibling_model, up_model)));
                normalize();
            }
            have ctx_is_framed(up_model) == 1 by {
                rewrite(ctx_is_framed(up_model)
                    == ctx_up_is_framed(Context::Left(identity, grandparent, color,
                                                      sibling_model, up_model)));
                rewrite(Context::Left(identity, grandparent, color,
                                      sibling_model, up_model) == c.model);
                assumption();
            }
            let { sibling: s, up: u } = unfold(c);
            have ctx_is_framed(u.model) == 1 by {
                rewrite(u.model == up_model);
                assumption();
            }
            match u.model {
                Context::Top => {
                    have ctx_is_framed(Context::Top) == 0 by {
                        unfold(ctx_is_framed(Context::Top));
                        normalize();
                    }
                    have ctx_is_framed(u.model) == 0 by {
                        rewrite(u.model == Context::Top);
                        assumption();
                    }
                    have ctx_is_framed(u.model) != 0 by {
                        rewrite(ctx_is_framed(u.model) == 1);
                        normalize();
                    }
                    contradiction(ctx_is_framed(u.model) == 0);
                },
                Context::Left(i2, g2, c2, s2, u2) => {
                    step();
                    solve();
                },
                Context::Right(i2, g2, c2, s2, u2) => {
                    step();
                    solve();
                },
            }
        },
        Context::Right(identity, grandparent, color, sibling_model, up_model) => {
            have ctx_up_is_framed(Context::Right(identity, grandparent, color,
                                                 sibling_model, up_model))
                == ctx_is_framed(up_model) by {
                unfold(ctx_up_is_framed(Context::Right(identity, grandparent, color,
                                                       sibling_model, up_model)));
                normalize();
            }
            have ctx_is_framed(up_model) == 1 by {
                rewrite(ctx_is_framed(up_model)
                    == ctx_up_is_framed(Context::Right(identity, grandparent, color,
                                                       sibling_model, up_model)));
                rewrite(Context::Right(identity, grandparent, color,
                                       sibling_model, up_model) == c.model);
                assumption();
            }
            let { sibling: s, up: u } = unfold(c);
            have ctx_is_framed(u.model) == 1 by {
                rewrite(u.model == up_model);
                assumption();
            }
            match u.model {
                Context::Top => {
                    have ctx_is_framed(Context::Top) == 0 by {
                        unfold(ctx_is_framed(Context::Top));
                        normalize();
                    }
                    have ctx_is_framed(u.model) == 0 by {
                        rewrite(u.model == Context::Top);
                        assumption();
                    }
                    have ctx_is_framed(u.model) != 0 by {
                        rewrite(ctx_is_framed(u.model) == 1);
                        normalize();
                    }
                    contradiction(ctx_is_framed(u.model) == 0);
                },
                Context::Left(i2, g2, c2, s2, u2) => {
                    step();
                    solve();
                },
                Context::Right(i2, g2, c2, s2, u2) => {
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
