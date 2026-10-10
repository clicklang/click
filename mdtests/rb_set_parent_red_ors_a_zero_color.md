# rb_set_parent_red ors a zero color into an aligned parent word

The Linux `rb_set_parent_color(node, parent, RB_RED)` stores
`(unsigned long)parent | 0`. The node arm of a one-node `rb_at` states that
word as the parent's address plus its color bit, with the parent aligned to 8,
and the refold after the store must re-establish both facts at the new parent.
An `|` with a zero constant is its other operand, and the alignment the body
states must be decided at the refold from the facts the store left. This is
the red reparenting helper on a node without subtrees, and it catches a
bitwise-or simplification that keeps the `| 0` and a refold that cannot
justify the parent alignment the body states.

```c filename=rb_set_parent_red_ors_a_zero_color.c
#define RB_RED 0

struct rb_node {
    unsigned long __rb_parent_color;
    struct rb_node *rb_right;
    struct rb_node *rb_left;
} __attribute__((aligned(sizeof(long))));

static inline void rb_set_parent_color(struct rb_node *rb, struct rb_node *p, int32 color) {
    rb->__rb_parent_color = (unsigned long)p | color;
}

void set_parent_red(struct rb_node *node, struct rb_node *parent) {
    rb_set_parent_color(node, parent, RB_RED);
}
```

```click
verifying "rb_set_parent_red_ors_a_zero_color.c";

spec enum Color { Red, Black }

spec enum RbTree {
    Empty,
    Node(struct rb_node*, struct rb_node*, Color, RbTree, RbTree),
}

function color_bit(color: Color) -> int {
    match color {
        Color::Red => 0,
        Color::Black => 1,
    }
}

function rb_reparent_color(tree: RbTree, new_parent: struct rb_node*, color: Color) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(identity, parent, old_color, left, right) =>
            RbTree::Node(identity, new_parent, color, left, right),
    }
}

resource rb_at(p: struct rb_node*) {
    field model: RbTree;
    match model {
        RbTree::Empty => { fact p == 0; },
        RbTree::Node(identity, parent, color, left_model, right_model) => {
            owns p->__rb_parent_color;
            fact p != 0;
            fact p == identity;
            fact aligned(p, 8);
            fact aligned(parent, 8);
            fact p->__rb_parent_color == address(parent) + (p->__rb_parent_color & 1);
            fact (p->__rb_parent_color & 1) == color_bit(color);
        },
    }
}

void set_parent_red(struct rb_node* node, struct rb_node* parent) {
    consumes t: rb_at(node);
    requires t.model != RbTree::Empty;
    requires aligned(parent, 8);
    produces u: rb_at(node);
    ensures u.model == rb_reparent_color(old(t.model), parent, Color::Red);
} by {
    match t.model {
        RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
        RbTree::Node(identity, old_parent, color, left_model, right_model) => {
            unfold(t);
            have color_bit(Color::Red) == 0 by {
                unfold(color_bit(Color::Red));
                normalize();
            }
            execute();
            let u = fold(rb_at(node), {
                model: RbTree::Node(identity, parent, Color::Red, left_model, right_model)
            });
            have u.model == rb_reparent_color(old(t.model), parent, Color::Red) by {
                rewrite(u.model
                    == RbTree::Node(identity, parent, Color::Red, left_model, right_model));
                rewrite(old(t.model)
                    == RbTree::Node(identity, old_parent, color, left_model, right_model));
                unfold(rb_reparent_color(
                    RbTree::Node(identity, old_parent, color, left_model, right_model),
                    parent, Color::Red));
                simp();
            }
            simp();
        },
    }
}
```

```expect
pass
```
