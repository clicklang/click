verifying "rb_erase_augmented.c";

import "../rbtree-model/rbtree_resources.click";
import "../rbtree-model/rbtree_erase_child.click";

spec enum EraseSpine {
    Top,
    Left(struct rb_node*, struct rb_node*, Color, RbTree, EraseSpine),
}

function erase_context(spine: EraseSpine) -> Context decreases spine {
    match spine {
        EraseSpine::Top => Context::Top,
        EraseSpine::Left(identity, grandparent, color, sibling, up) =>
            Context::Left(identity, grandparent, color, sibling, erase_context(up)),
    }
}

# The path ends at anchor->rb_left, leaving anchor's other fields available.
resource erase_spine_at(focus: struct rb_node*, anchor: struct rb_node*) {
    field model: EraseSpine;
    match model {
        EraseSpine::Top => {
            owns anchor->rb_left;
            fact anchor != 0;
            fact anchor->rb_left == focus;
        },
        EraseSpine::Left(identity, grandparent, color, sibling_model, up_model) => {
            owns identity->__rb_parent_color;
            owns identity->rb_left;
            owns identity->rb_right;
            owns sibling: rb_at(identity->rb_right);
            owns up: erase_spine_at(identity, anchor);
            fact identity != 0;
            fact aligned(identity, 8);
            fact aligned(grandparent, 8);
            fact identity->rb_left == focus;
            fact identity->__rb_parent_color
                == address(grandparent) + (identity->__rb_parent_color & 1);
            fact (identity->__rb_parent_color & 1) == color_bit(color);
            fact sibling.model == sibling_model;
            fact up.model == up_model;
            fact rb_parent_is(sibling_model, identity) == 1;
        },
    }
}

resource erase_left_at(anchor: struct rb_node*) {
    field model: RbTree;
    owns anchor->rb_left;
    owns tree: rb_at(anchor->rb_left);
    fact anchor != 0;
    fact tree.model == model;
}

function erase_spine_depth(ctx: EraseSpine) -> Integer
    decreases ctx
{
    match ctx {
        EraseSpine::Top => 0,
        EraseSpine::Left(identity, grandparent, color, sibling_model, up_model) =>
            erase_spine_depth(up_model) + 1,
    }
}

theorem erase_spine_depth_is_nonnegative(ctx: EraseSpine) {
    ensures 0 <= erase_spine_depth(ctx) by {
        induct(ctx) as ih {
            EraseSpine::Top => {
                unfold(erase_spine_depth(EraseSpine::Top));
                normalize();
            }
            EraseSpine::Left(identity, grandparent, color, sibling_model, up_model) => {
                apply(ih(up_model));
                unfold(erase_spine_depth(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model)));
                arithmetic() using { 0 <= erase_spine_depth(up_model); }
            }
        }
    }
}

theorem erase_parent_consistent_parent_is(t: RbTree, p: struct rb_node*) {
    requires rb_parent_consistent(t, p) == 1;
    ensures rb_parent_is(t, p) == 1 by {
        induct(t) as ih {
            RbTree::Empty => {
                unfold(rb_parent_is(RbTree::Empty, p));
                normalize();
            }
            RbTree::Node(node, parent, color, left, right) => {
                apply(rb_parent_consistent_node_parent(node, parent, color, left, right, p));
                apply(rb_parent_is_node_is(node, parent, color, left, right, p));
                rewrite(rb_parent_is(RbTree::Node(node, parent, color, left, right), p)
                    == rb_node_is(parent, p));
                assumption();
            }
        }
    }
}

tactic refold_erase_spine(focus: struct rb_node*, anchor: struct rb_node*) {
    consumes c: erase_spine_at(focus, anchor);
    decreases erase_spine_depth(c.model);
    consumes t: rb_at(focus);
    requires rb_parent_consistent(plug(erase_context(c.model), t.model), anchor) == 1;
    produces whole: erase_left_at(anchor);
    ensures whole.model == plug(erase_context(old(c.model)), old(t.model));
} by {
    match c.model {
        EraseSpine::Top => {
            unfold(c);
            let whole = fold(erase_left_at(anchor), { model: t.model }, { tree: t });
            have plug(Context::Top, old(t.model)) == old(t.model) by {
                unfold(plug(Context::Top, old(t.model))); normalize();
            }
            have whole.model == plug(erase_context(old(c.model)), old(t.model)) by {
                rewrite(old(c.model) == EraseSpine::Top);
                unfold(erase_context(EraseSpine::Top));
                rewrite(plug(Context::Top, old(t.model)) == old(t.model)); simp();
            }
        },
        EraseSpine::Left(identity, grandparent, color, sibling_model, up_model) => {
            have erase_context(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model))
                == Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)) by {
                unfold(erase_context(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model))); normalize();
            }
            have rb_parent_consistent(plug(Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)), t.model), anchor) == 1 by {
                rewrite(Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)) == erase_context(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model)));
                rewrite(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model) == c.model);
                assumption();
            }
            apply(plug_parent_consistent_ctx(Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)), t.model, anchor)) using {
                rb_parent_consistent(plug(Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)), t.model), anchor) == 1;
            }
            apply(ctx_consistent_left_focus(identity, grandparent, color, sibling_model, erase_context(up_model), t.model, anchor)) using {
                ctx_consistent(Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)), t.model, anchor) == 1;
            }
            apply(erase_parent_consistent_parent_is(t.model, identity)) using {
                rb_parent_consistent(t.model, identity) == 1;
            }
            let { sibling: s, up: u } = unfold(c);
            let sub = fold(rb_at(identity), { model: RbTree::Node(identity, grandparent, color, old(t.model), sibling_model) }, { left: t, right: s });
            apply(erase_spine_depth_is_nonnegative(up_model));
            have 0 <= erase_spine_depth(u.model) by {
                rewrite(u.model == up_model);
                assumption();
            }
            have erase_spine_depth(old(c.model)) == erase_spine_depth(up_model) + 1 by {
                rewrite(old(c.model) == EraseSpine::Left(identity, grandparent, color, sibling_model, up_model));
                unfold(erase_spine_depth(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model)));
                normalize();
            }
            have erase_spine_depth(u.model) < erase_spine_depth(old(c.model)) by {
                rewrite(u.model == up_model);
                arithmetic() using { erase_spine_depth(old(c.model)) == erase_spine_depth(up_model) + 1; }
            }
            have plug(Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)), old(t.model)) == plug(erase_context(up_model), RbTree::Node(identity, grandparent, color, old(t.model), sibling_model)) by {
                unfold(plug(Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)), old(t.model)));
                normalize();
            }
            have rb_parent_consistent(plug(erase_context(u.model), sub.model), anchor) == 1 by {
                rewrite(u.model == up_model);
                rewrite(sub.model == RbTree::Node(identity, grandparent, color, old(t.model), sibling_model));
                rewrite(plug(erase_context(up_model), RbTree::Node(identity, grandparent, color, old(t.model), sibling_model)) == plug(Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)), old(t.model)));
                rewrite(Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)) == erase_context(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model)));
                rewrite(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model) == old(c.model));
                assumption();
            }
            let { whole: whole } = refold_erase_spine(identity, anchor, { c: u, t: sub });
            have whole.model == plug(erase_context(old(c.model)), old(t.model)) by {
                rewrite(old(c.model) == EraseSpine::Left(identity, grandparent, color, sibling_model, up_model));
                rewrite(erase_context(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model)) == Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)));
                rewrite(plug(Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)), old(t.model)) == plug(erase_context(up_model), RbTree::Node(identity, grandparent, color, old(t.model), sibling_model)));
                simp();
            }
        },
    }
}

# A nonempty focus is still the leftmost candidate through every spine frame.
theorem erase_spine_minimum(spine: EraseSpine, tree: RbTree) {
    requires tree != RbTree::Empty;
    ensures rb_minimum(plug(erase_context(spine), tree)) == rb_minimum(tree) by {
        induct(spine) as ih {
            EraseSpine::Top => {
                unfold(erase_context(EraseSpine::Top));
                unfold(plug(Context::Top, tree)); normalize();
            }
            EraseSpine::Left(identity, parent, color, sibling, up) => {
                have RbTree::Node(identity, parent, color, tree, sibling) != RbTree::Empty by { normalize(); }
                apply(ih(up, RbTree::Node(identity, parent, color, tree, sibling)));
                apply(rb_minimum_nonempty_left(identity, parent, color, tree, sibling));
                unfold(erase_context(EraseSpine::Left(identity, parent, color, sibling, up)));
                unfold(plug(Context::Left(identity, parent, color, sibling, erase_context(up)), tree));
                rewrite(rb_minimum(plug(erase_context(up), RbTree::Node(identity, parent, color, tree, sibling)))
                    == rb_minimum(RbTree::Node(identity, parent, color, tree, sibling)));
                assumption();
            }
        }
    }
}

# Cutting the minimum below a left-only spine leaves its ancestor frames intact.
theorem erase_spine_remove_min_blackened(spine: EraseSpine, tree: RbTree) {
    requires tree != RbTree::Empty;
    ensures rb_remove_min_blackened(plug(erase_context(spine), tree))
        == plug(erase_context(spine), rb_remove_min_blackened(tree)) by {
        induct(spine) as ih {
            EraseSpine::Top => {
                unfold(erase_context(EraseSpine::Top));
                unfold(plug(Context::Top, tree));
                unfold(plug(Context::Top, rb_remove_min_blackened(tree))); normalize();
            }
            EraseSpine::Left(identity, parent, color, sibling, up) => {
                have RbTree::Node(identity, parent, color, tree, sibling) != RbTree::Empty by { normalize(); }
                apply(ih(up, RbTree::Node(identity, parent, color, tree, sibling)));
                apply(rb_remove_min_blackened_nonempty_left(identity, parent, color, tree, sibling));
                unfold(erase_context(EraseSpine::Left(identity, parent, color, sibling, up)));
                unfold(plug(Context::Left(identity, parent, color, sibling, erase_context(up)), tree));
                unfold(plug(Context::Left(identity, parent, color, sibling, erase_context(up)), rb_remove_min_blackened(tree)));
                rewrite(rb_remove_min_blackened(plug(erase_context(up), RbTree::Node(identity, parent, color, tree, sibling)))
                    == plug(erase_context(up), rb_remove_min_blackened(RbTree::Node(identity, parent, color, tree, sibling))));
                rewrite(rb_remove_min_blackened(RbTree::Node(identity, parent, color, tree, sibling))
                    == RbTree::Node(identity, parent, color, rb_remove_min_blackened(tree), sibling));
                normalize();
            }
        }
    }
}

function erase_spine_parent(spine: EraseSpine, anchor: struct rb_node*) -> struct rb_node* {
    match spine {
        EraseSpine::Top => anchor,
        EraseSpine::Left(identity, grandparent, color, sibling, up) => identity,
    }
}

theorem erase_spine_focus_parent_consistent(spine: EraseSpine, tree: RbTree, anchor: struct rb_node*) {
    requires rb_parent_consistent(plug(erase_context(spine), tree), anchor) == 1;
    ensures rb_parent_consistent(tree, erase_spine_parent(spine, anchor)) == 1 by {
        induct(spine) as ih {
            EraseSpine::Top => {
                unfold(erase_spine_parent(EraseSpine::Top, anchor));
                have plug(erase_context(EraseSpine::Top), tree) == tree by {
                    unfold(erase_context(EraseSpine::Top)); unfold(plug(Context::Top, tree)); normalize();
                }
                rewrite(tree == plug(erase_context(EraseSpine::Top), tree)); assumption();
            },
            EraseSpine::Left(identity, parent, color, sibling, up) => {
                have erase_context(EraseSpine::Left(identity, parent, color, sibling, up)) == Context::Left(identity, parent, color, sibling, erase_context(up)) by {
                    unfold(erase_context(EraseSpine::Left(identity, parent, color, sibling, up))); normalize();
                }
                have rb_parent_consistent(plug(Context::Left(identity, parent, color, sibling, erase_context(up)), tree), anchor) == 1 by {
                    rewrite(Context::Left(identity, parent, color, sibling, erase_context(up)) == erase_context(EraseSpine::Left(identity, parent, color, sibling, up))); assumption();
                }
                apply(plug_parent_consistent_ctx(Context::Left(identity, parent, color, sibling, erase_context(up)), tree, anchor));
                apply(ctx_consistent_left_focus(identity, parent, color, sibling, erase_context(up), tree, anchor));
                unfold(erase_spine_parent(EraseSpine::Left(identity, parent, color, sibling, up), anchor)); assumption();
            },
        }
    }
}
