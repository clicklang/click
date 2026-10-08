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

# The path with its innermost left link exposed for the C successor splice.
resource erase_spine_frame(parent: struct rb_node*, anchor: struct rb_node*) {
    field model: EraseSpine;
    match model {
        EraseSpine::Top => {
            fact parent == anchor;
            fact anchor != 0;
        },
        EraseSpine::Left(identity, grandparent, color, sibling_model, up_model) => {
            owns identity->__rb_parent_color;
            owns identity->rb_right;
            owns sibling: rb_at(identity->rb_right);
            owns up: erase_spine_at(identity, anchor);
            fact parent == identity;
            fact identity != 0;
            fact aligned(identity, 8);
            fact aligned(grandparent, 8);
            fact identity->__rb_parent_color
            == address(grandparent) + (identity->__rb_parent_color & 1);
            fact (identity->__rb_parent_color & 1) == color_bit(color);
            fact sibling.model == sibling_model;
            fact up.model == up_model;
            fact rb_parent_is(sibling_model, identity) == 1;
        },
    }
}

tactic open_erase_spine_link(focus: struct rb_node*, parent: struct rb_node*, anchor: struct rb_node*) {
    consumes c: erase_spine_at(focus, anchor);
    requires parent == erase_spine_parent(c.model, anchor);
    produces parent->rb_left;
    produces frame: erase_spine_frame(parent, anchor);
    ensures parent->rb_left == focus;
    ensures frame.model == old(c.model);
} by {
    match c.model {
        EraseSpine::Top => {
            have erase_spine_parent(c.model, anchor) == anchor by {
                rewrite(c.model == EraseSpine::Top);
                unfold(erase_spine_parent(EraseSpine::Top, anchor)); normalize();
            }
            have parent == anchor by { normalize() using { } }
            unfold(c);
            let frame = fold(erase_spine_frame(parent, anchor), { model: EraseSpine::Top });
            have parent->rb_left == focus by { simp(); }
            have frame.model == old(c.model) by { simp(); }
        },
        EraseSpine::Left(identity, grandparent, color, sibling_model, up_model) => {
            have erase_spine_parent(c.model, anchor) == identity by {
                rewrite(c.model == EraseSpine::Left(identity, grandparent, color, sibling_model, up_model));
                unfold(erase_spine_parent(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model), anchor)); normalize();
            }
            have parent == identity by { normalize() using { } }
            let { sibling: sibling, up: up } = unfold(c);
            let frame = fold(erase_spine_frame(parent, anchor), {
                model: EraseSpine::Left(identity, grandparent, color, sibling_model, up_model)
            }, { sibling: sibling, up: up });
            have parent->rb_left == focus by { simp(); }
            have frame.model == old(c.model) by { simp(); }
        },
    }
}

tactic close_erase_spine_link(focus: struct rb_node*, parent: struct rb_node*, anchor: struct rb_node*) {
    consumes parent->rb_left;
    consumes frame: erase_spine_frame(parent, anchor);
    requires parent->rb_left == focus;
    produces c: erase_spine_at(focus, anchor);
    ensures c.model == old(frame.model);
} by {
    match frame.model {
        EraseSpine::Top => {
            unfold(frame);
            have anchor->rb_left == focus by { simp(); }
            let c = fold(erase_spine_at(focus, anchor), { model: EraseSpine::Top });
            have c.model == old(frame.model) by { simp(); }
        },
        EraseSpine::Left(identity, grandparent, color, sibling_model, up_model) => {
            let { sibling: sibling, up: up } = unfold(frame);
            have parent != 0 by { rewrite(parent == identity); assumption(); }
            have aligned(parent, 8) by { rewrite(parent == identity); assumption(); }
            have rb_parent_is(sibling_model, parent) == 1 by { rewrite(parent == identity); assumption(); }
            let c = fold(erase_spine_at(focus, anchor), {
                model: EraseSpine::Left(identity, grandparent, color, sibling_model, up_model)
            }, { sibling: sibling, up: up });
            have c.model == old(frame.model) by { simp(); }
        },
    }
}

function erase_minimum_identity(minimum: RbMinimum) -> struct rb_node* {
    match minimum {
        RbMinimum::Absent => 0,
        RbMinimum::Found(identity, color, child) => identity,
    }
}

function erase_minimum_child(minimum: RbMinimum) -> RbTree {
    match minimum {
        RbMinimum::Absent => RbTree::Empty,
        RbMinimum::Found(identity, color, child) => child,
    }
}

contract void AugmentRotate(struct rb_node* old, struct rb_node* new) {
    requires new != 0;
    ensures 1 == 1;
}

contract void ErasePropagate(struct rb_node* node, struct rb_node* stop) {
    ensures 1 == 1;
}

contract void EraseCopy(struct rb_node* node, struct rb_node* successor) {
    requires node != 0;
    requires successor != 0;
    ensures 1 == 1;
}

resource erase_callbacks(augment: const struct rb_augment_callbacks*) {
    owns augment->propagate;
    owns augment->copy;
    owns augment->rotate;
    fact ErasePropagate(augment->propagate);
    fact EraseCopy(augment->copy);
    fact AugmentRotate(augment->rotate);
}

struct rb_node* __rb_erase_augmented(struct rb_node* node, struct rb_root* root,
    const struct rb_augment_callbacks* augment) {
    consumes tree: rb_at(node);
    consumes up: ctx_at(node, root);
    requires up.model == Context::Top;
    requires tree.model != RbTree::Empty;
    requires rb_parent_is(tree.model, 0) == 1;
    requires rb_color(tree.model) == Color::Black;
    requires rb_left(tree.model) != RbTree::Empty;
    requires rb_right(tree.model) != RbTree::Empty;
    requires rb_left(rb_right(tree.model)) != RbTree::Empty;
    requires erase_minimum_child(rb_minimum(rb_right(tree.model))) != RbTree::Empty;
    requires rb_parent_consistent(tree.model, 0) == 1;
    requires is_rb(tree.model) == 1;
    owns erase_callbacks(augment);
    produces node->__rb_parent_color;
    produces node->rb_left;
    produces node->rb_right;
    produces remaining: rb_root_at(root);
    ensures remaining.model == rb_successor_child_splice(
        erase_minimum_identity(rb_minimum(rb_right(old(tree.model)))), 0, Color::Black,
        rb_left(old(tree.model)), rb_right(old(tree.model)));
    ensures is_rb_root(remaining.model) == 1;
    ensures rb_parent_consistent(remaining.model, 0) == 1;
    ensures rb_inorder(remaining.model) == list_append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model))));
    ensures result == 0;
} by {
    match tree.model {
        RbTree::Empty => { contradiction(tree.model == RbTree::Empty); },
        RbTree::Node(identity, parent_model, color, left_model, right_model) => {
            have rb_left(tree.model) == left_model by {
                rewrite(tree.model == RbTree::Node(identity, parent_model, color, left_model, right_model));
                unfold(rb_left(RbTree::Node(identity, parent_model, color, left_model, right_model))); normalize();
            }
            have rb_right(tree.model) == right_model by {
                rewrite(tree.model == RbTree::Node(identity, parent_model, color, left_model, right_model));
                unfold(rb_right(RbTree::Node(identity, parent_model, color, left_model, right_model))); normalize();
            }
            have left_model != RbTree::Empty by { rewrite(left_model == rb_left(tree.model)); assumption(); }
            have right_model != RbTree::Empty by { rewrite(right_model == rb_right(tree.model)); assumption(); }
            have erase_minimum_child(rb_minimum(right_model)) != RbTree::Empty by {
                rewrite(right_model == rb_right(tree.model)); assumption();
            }
            have rb_left(right_model) != RbTree::Empty by { rewrite(right_model == rb_right(tree.model)); assumption(); }
            have rb_parent_is(RbTree::Node(identity, parent_model, color, left_model, right_model), 0) == 1 by {
                rewrite(RbTree::Node(identity, parent_model, color, left_model, right_model) == tree.model); assumption();
            }
            apply(rb_parent_is_node_parent(identity, parent_model, color, left_model, right_model, 0));
            have color == Color::Black by {
                unfold(rb_color(RbTree::Node(identity, parent_model, color, left_model, right_model)));
                rewrite(color == rb_color(RbTree::Node(identity, parent_model, color, left_model, right_model)));
                rewrite(RbTree::Node(identity, parent_model, color, left_model, right_model) == tree.model); assumption();
            }
            have rb_parent_consistent(RbTree::Node(identity, parent_model, color, left_model, right_model), 0) == 1 by {
                rewrite(RbTree::Node(identity, parent_model, color, left_model, right_model) == tree.model); assumption();
            }
            apply(rb_parent_consistent_node_right(identity, parent_model, color, left_model, right_model, 0));
            have is_rb(RbTree::Node(identity, parent_model, color, left_model, right_model)) == 1 by {
                rewrite(RbTree::Node(identity, parent_model, color, left_model, right_model) == tree.model); assumption();
            }
            have ctx_rb(Context::Top, black_height(RbTree::Node(identity, parent_model, color, left_model, right_model)),
                rb_color(RbTree::Node(identity, parent_model, color, left_model, right_model))) == 1 by {
                unfold(rb_color(RbTree::Node(identity, parent_model, color, left_model, right_model)));
                rewrite(color == Color::Black);
                unfold(ctx_rb(Context::Top, black_height(RbTree::Node(identity, parent_model, Color::Black, left_model, right_model)), Color::Black));
                unfold(color_black(Color::Black)); normalize();
            }
            have ctx_consistent(Context::Top, RbTree::Node(identity, parent_model, color, left_model, right_model), 0) == 1 by {
                unfold(ctx_consistent(Context::Top, RbTree::Node(identity, parent_model, color, left_model, right_model), 0));
                rewrite(rb_parent_consistent(RbTree::Node(identity, parent_model, color, left_model, right_model), 0) == 1); normalize();
            }
            have rb_left(old(tree.model)) == left_model by { simp(); }
            have rb_right(old(tree.model)) == right_model by { simp(); }
            unfold(up);
            let { left: l, right: r } = unfold(tree);
            have color_bit(Color::Black) == 1 by { unfold(color_bit(Color::Black)); normalize(); }
            have (node->__rb_parent_color & 1) == 1 by {
                rewrite((node->__rb_parent_color & 1) == color_bit(color));
                rewrite(color == Color::Black); unfold(color_bit(Color::Black)); normalize();
            }
            have node->__rb_parent_color == 1 by { simp(); }
            match left_model {
                RbTree::Empty => { contradiction(left_model == RbTree::Empty); },
                RbTree::Node(lid, lp, lc, ll, lr) => {
                    let { left: ll_tree, right: lr_tree } = unfold(l);
                    match right_model {
                        RbTree::Empty => { contradiction(right_model == RbTree::Empty); },
                        RbTree::Node(rid, rp, rc, rl, rr) => {
                            have rl != RbTree::Empty by {
                                unfold(rb_left(RbTree::Node(rid, rp, rc, rl, rr)));
                                rewrite(rl == rb_left(RbTree::Node(rid, rp, rc, rl, rr)));
                                rewrite(RbTree::Node(rid, rp, rc, rl, rr) == right_model); assumption();
                            }
                            have rb_parent_consistent(RbTree::Node(rid, rp, rc, rl, rr), identity) == 1 by {
                                rewrite(RbTree::Node(rid, rp, rc, rl, rr) == right_model); assumption();
                            }
                            apply(rb_parent_consistent_node_left(rid, rp, rc, rl, rr, identity));
                            apply(rb_remove_min_blackened_parent_consistent(rl, rid));
                            let { left: t, right: right_sibling } = unfold(r);
                            match rl {
                                RbTree::Empty => { contradiction(rl == RbTree::Empty); },
                                RbTree::Node(iid, ip, ic, il, ir) => {
                                    let { left: init_l, right: init_r } = unfold(t);
                                    let t = fold(rb_at(iid), { model: RbTree::Node(iid, ip, ic, il, ir) }, { left: init_l, right: init_r });
                                    step(); step(); step(); step(); step(); step(); step(); step(); step(); step(); step(); step(); step(); step();
                                    let c = fold(erase_spine_at(tmp, child), { model: EraseSpine::Top });
                                    have plug(erase_context(c.model), t.model) == rl by {
                                        rewrite(c.model == EraseSpine::Top);
                                        unfold(erase_context(EraseSpine::Top));
                                        unfold(plug(Context::Top, t.model)); simp();
                                    }
                                    have successor == erase_spine_parent(c.model, child) by {
                                        rewrite(c.model == EraseSpine::Top);
                                        unfold(erase_spine_parent(EraseSpine::Top, child)); simp();
                                    }
                                    loop {
                                        owns c: erase_spine_at(tmp, child);
                                        owns t: rb_at(tmp);
                                        decreases t;
                                        invariant tmp != 0;
                                        invariant successor == erase_spine_parent(c.model, child);
                                        invariant plug(erase_context(c.model), t.model) == rl;
                                        initialize by simp;
                                        preserve by {
                                            match t.model {
                                                RbTree::Empty => { unfold(t); have tmp != 0 by { simp(); } contradiction(tmp == 0); },
                                                RbTree::Node(tid, tp, tc, tl, tr) => {
                                                    have plug(erase_context(EraseSpine::Left(tid, tp, tc, tr, c.model)), tl) == rl by {
                                                        unfold(erase_context(EraseSpine::Left(tid, tp, tc, tr, c.model)));
                                                        unfold(plug(Context::Left(tid, tp, tc, tr, erase_context(c.model)), tl));
                                                        rewrite(RbTree::Node(tid, tp, tc, tl, tr) == t.model); assumption();
                                                    }
                                                    let { left: next, right: sibling } = unfold(t);
                                                    have tmp == tid by { assumption(); }
                                                    have tid != 0 by { rewrite(tid == tmp); assumption(); }
                                                    have erase_spine_parent(EraseSpine::Left(tid, tp, tc, tr, c.model), child) == tid by {
                                                        unfold(erase_spine_parent(EraseSpine::Left(tid, tp, tc, tr, c.model), child)); normalize();
                                                    }
                                                    let frame = fold(erase_spine_at(tmp->rb_left, child),
                                                        { model: EraseSpine::Left(tid, tp, tc, tr, c.model) }, { sibling: sibling, up: c });
                                                    step(); step(); step();
                                                    have successor == erase_spine_parent(frame.model, child) by { simp(); }
                                                    if tmp == 0 {
                                                    } else {
                                                        close_invariants();
                                                    }
                                                },
                                            }
                                        }
                                    }
                                    have node->rb_left == lid by { simp(); }
                                    have tmp == 0 by { simp(); }
                                    match t.model {
                                        RbTree::Node(a, b, col, lt, rt) => {
                                            have t.model == RbTree::Empty by { assumption(); }
                                            have t.model != RbTree::Empty by { rewrite(t.model == RbTree::Node(a, b, col, lt, rt)); normalize(); }
                                            contradiction(t.model == RbTree::Empty);
                                        },
                                        RbTree::Empty => {
                                            have c.model != EraseSpine::Top by { normalize(); }
                                            match c.model {
                                                EraseSpine::Top => { contradiction(c.model == EraseSpine::Top); },
                                                EraseSpine::Left(mid, mp, mc, mr, mu) => {
                                                    have plug(erase_context(c.model), t.model) == plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)) by {
                                                        rewrite(c.model == EraseSpine::Left(mid, mp, mc, mr, mu));
                                                        unfold(erase_context(EraseSpine::Left(mid, mp, mc, mr, mu)));
                                                        unfold(plug(Context::Left(mid, mp, mc, mr, erase_context(mu)), t.model));
                                                        rewrite(t.model == RbTree::Empty); normalize();
                                                    }
                                                    have plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)) == rl by {
                                                        rewrite(plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)) == plug(erase_context(c.model), t.model)); assumption();
                                                    }
                                                    have RbTree::Node(mid, mp, mc, RbTree::Empty, mr) != RbTree::Empty by { normalize(); }
                                                    apply(erase_spine_minimum(mu, RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                    have rb_minimum(rl) == RbMinimum::Found(mid, mc, mr) by {
                                                        rewrite(rl == plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                        rewrite(rb_minimum(plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)))
                                                            == rb_minimum(RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                        unfold(rb_minimum(RbTree::Node(mid, mp, mc, RbTree::Empty, mr))); normalize();
                                                    }
                                                    apply(rb_minimum_nonempty_left(rid, rp, rc, rl, rr));
                                                    have rb_minimum(right_model) == RbMinimum::Found(mid, mc, mr) by {
                                                        rewrite(right_model == RbTree::Node(rid, rp, rc, rl, rr));
                                                        rewrite(rb_minimum(RbTree::Node(rid, rp, rc, rl, rr)) == rb_minimum(rl)); assumption();
                                                    }
                                                    have mr != RbTree::Empty by {
                                                        have erase_minimum_child(rb_minimum(right_model)) == mr by {
                                                            rewrite(rb_minimum(right_model) == RbMinimum::Found(mid, mc, mr));
                                                            unfold(erase_minimum_child(RbMinimum::Found(mid, mc, mr))); normalize();
                                                        }
                                                        rewrite(mr == erase_minimum_child(rb_minimum(right_model)));
                                                        assumption();
                                                    }
                                                    apply(rb_erase_nonempty_successor_splice(identity, mid, parent_model, color,
                                                        left_model, right_model, Context::Top, 0, mc, mr));
                                                    apply(rb_remove_min_blackened_nonempty_left(rid, rp, rc, rl, rr));
                                                    have erase_minimum_identity(rb_minimum(right_model)) == mid by {
                                                        rewrite(rb_minimum(right_model) == RbMinimum::Found(mid, mc, mr));
                                                        unfold(erase_minimum_identity(RbMinimum::Found(mid, mc, mr))); normalize();
                                                    }
                                                    have rb_parent_consistent(plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)), rid) == 1 by {
                                                        rewrite(plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)) == rl); assumption();
                                                    }
                                                    apply(erase_spine_focus_parent_consistent(mu, RbTree::Node(mid, mp, mc, RbTree::Empty, mr), rid));
                                                    apply(erase_parent_consistent_parent_is(RbTree::Node(mid, mp, mc, RbTree::Empty, mr), erase_spine_parent(mu, rid)));
                                                    apply(rb_parent_is_node_parent(mid, mp, mc, RbTree::Empty, mr, erase_spine_parent(mu, rid)));
                                                    apply(erase_spine_remove_min_blackened(mu, RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                    have rb_remove_min_blackened(rl) == plug(erase_context(mu), rb_reparent(rb_recolor(mr, Color::Black), mp)) by {
                                                        rewrite(rl == plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                        rewrite(rb_remove_min_blackened(plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)))
                                                                == plug(erase_context(mu), rb_remove_min_blackened(RbTree::Node(mid, mp, mc, RbTree::Empty, mr))));
                                                        unfold(rb_remove_min_blackened(RbTree::Node(mid, mp, mc, RbTree::Empty, mr))); normalize();
                                                    }
                                                    let { sibling: min_right, up: path } = unfold(c);
                                                    unfold(t);
                                                    have min_right.model != RbTree::Empty by { rewrite(min_right.model == mr); assumption(); }
                                                    have parent == erase_spine_parent(path.model, child) by { simp(); }
                                                    have parent == mp by {
                                                        rewrite(parent == erase_spine_parent(path.model, child));
                                                        rewrite(path.model == mu); rewrite(child == rid);
                                                        rewrite(erase_spine_parent(mu, rid) == mp); normalize();
                                                    }
                                                    have path.model == mu by { simp(); }
                                                    mark opened_spine;
                                                    let { frame: link_frame } = open_erase_spine_link(successor, parent, child, { c: path });
                                                    have link_frame.model == at(opened_spine, path.model) by { assumption(); }
                                                    have link_frame.model == mu by { simp(); }
                                                    step(); step(); step(); step();
                                                    have node->rb_left == lid by { simp(); }
                                                    unfold(erase_callbacks(augment));
                                                    match min_right.model {
                                                        RbTree::Empty => { contradiction(min_right.model == RbTree::Empty); },
                                                        RbTree::Node(cid, cp, cc, cl, cr) => {
                                                            have mr == RbTree::Node(cid, cp, cc, cl, cr) by { rewrite(mr == min_right.model); assumption(); }
                                                            have rb_reparent(rb_recolor(mr, Color::Black), mp) == RbTree::Node(cid, mp, Color::Black, cl, cr) by {
                                                                rewrite(mr == RbTree::Node(cid, cp, cc, cl, cr));
                                                                unfold(rb_recolor(RbTree::Node(cid, cp, cc, cl, cr), Color::Black));
                                                                unfold(rb_reparent(RbTree::Node(cid, cp, Color::Black, cl, cr), mp)); normalize();
                                                            }
                                                            let { left: child_left, right: child_right } = unfold(min_right);
                                                            execute_until(statement(62));
                                                            let moved_child = fold(rb_at(cid), { model: RbTree::Node(cid, mp, Color::Black, cl, cr) }, { left: child_left, right: child_right });
                                                            mark closing_spine;
                                                            let { c: path2 } = close_erase_spine_link(cid, parent, child, { frame: link_frame });
                                                            have path2.model == at(closing_spine, link_frame.model) by { assumption(); }
                                                            have path2.model == mu by { simp(); }
                                                            have moved_child.model == rb_reparent(rb_recolor(mr, Color::Black), mp) by {
                                                                rewrite(rb_reparent(rb_recolor(mr, Color::Black), mp) == RbTree::Node(cid, mp, Color::Black, cl, cr)); normalize();
                                                            }
                                                            have rb_parent_consistent(plug(erase_context(path2.model), moved_child.model), child) == 1 by {
                                                                rewrite(path2.model == mu);
                                                                rewrite(moved_child.model == rb_reparent(rb_recolor(mr, Color::Black), mp));
                                                                rewrite(plug(erase_context(mu), rb_reparent(rb_recolor(mr, Color::Black), mp)) == rb_remove_min_blackened(rl));
                                                                rewrite(child == rid); assumption();
                                                            }
                                                            mark rebuilding_spine;
                                                            let { whole: whole } = refold_erase_spine(cid, child, { c: path2, t: moved_child });
                                                            have at(rebuilding_spine, path2.model) == mu by { assumption(); }
                                                            have whole.model == plug(erase_context(at(rebuilding_spine, path2.model)), RbTree::Node(cid, mp, Color::Black, cl, cr)) by { assumption(); }
                                                            have whole.model == rb_remove_min_blackened(rl) by {
                                                                rewrite(rb_remove_min_blackened(rl) == plug(erase_context(mu), rb_reparent(rb_recolor(mr, Color::Black), mp)));
                                                                rewrite(rb_reparent(rb_recolor(mr, Color::Black), mp) == RbTree::Node(cid, mp, Color::Black, cl, cr));
                                                                rewrite(mu == at(rebuilding_spine, path2.model));
                                                                assumption();
                                                            }
                                                            let { tree: rebuilt_left } = unfold(whole);
                                                            have rebuilt_left.model == rb_remove_min_blackened(rl) by { simp(); }
                                                            have right_sibling.model == rr by { simp(); }
                                                            apply(erase_parent_consistent_parent_is(rb_remove_min_blackened(rl), rid));
                                                            have child == rid by { simp(); }
                                                            have child->rb_left == rid->rb_left by { simp(); }
                                                            have child->rb_right == rid->rb_right by { simp(); }
                                                            let moved_right = fold(rb_at(rid), {
                                                                model: RbTree::Node(rid, mid, rc, rb_remove_min_blackened(rl), rr)
                                                            }, { left: rebuilt_left, right: right_sibling });
                                                            let moved_left = fold(rb_at(lid), {
                                                                model: RbTree::Node(lid, mid, lc, ll, lr)
                                                            }, { left: ll_tree, right: lr_tree });
                                                            have rb_parent_is(RbTree::Node(lid, mid, lc, ll, lr), mid) == 1 by { unfold(rb_parent_is(RbTree::Node(lid, mid, lc, ll, lr), mid)); normalize(); }
                                                            have rb_parent_is(RbTree::Node(rid, mid, rc, rb_remove_min_blackened(rl), rr), mid) == 1 by { unfold(rb_parent_is(RbTree::Node(rid, mid, rc, rb_remove_min_blackened(rl), rr), mid)); normalize(); }
                                                            let result_tree = fold(rb_at(mid), {
                                                                model: RbTree::Node(mid, 0, Color::Black, RbTree::Node(lid, mid, lc, ll, lr),
                                                                    RbTree::Node(rid, mid, rc, rb_remove_min_blackened(rl), rr))
                                                            }, { left: moved_left, right: moved_right });
                                                            let remaining = fold(rb_root_at(root), {
                                                                model: RbTree::Node(mid, 0, Color::Black, RbTree::Node(lid, mid, lc, ll, lr),
                                                                    RbTree::Node(rid, mid, rc, rb_remove_min_blackened(rl), rr))
                                                            }, { tree: result_tree });
                                                            have remaining.model == rb_successor_child_splice(mid, parent_model, color, left_model, right_model) by {
                                                                unfold(rb_successor_child_splice(mid, parent_model, color, left_model, right_model));
                                                                rewrite(left_model == RbTree::Node(lid, lp, lc, ll, lr));
                                                                rewrite(right_model == RbTree::Node(rid, rp, rc, rl, rr));
                                                                rewrite(rb_remove_min_blackened(RbTree::Node(rid, rp, rc, rl, rr)) == RbTree::Node(rid, rp, rc, rb_remove_min_blackened(rl), rr));
                                                                unfold(rb_reparent(RbTree::Node(lid, lp, lc, ll, lr), mid));
                                                                unfold(rb_reparent(RbTree::Node(rid, rp, rc, rb_remove_min_blackened(rl), rr), mid));
                                                                rewrite(parent_model == 0); rewrite(color == Color::Black); normalize();
                                                            }
                                                            have remaining.model == rb_successor_child_splice(
                                                                erase_minimum_identity(rb_minimum(rb_right(old(tree.model)))), 0, Color::Black,
                                                                rb_left(old(tree.model)), rb_right(old(tree.model))) by {
                                                                rewrite(remaining.model == rb_successor_child_splice(mid, parent_model, color, left_model, right_model));
                                                                rewrite(rb_left(old(tree.model)) == left_model); rewrite(rb_right(old(tree.model)) == right_model);
                                                                rewrite(erase_minimum_identity(rb_minimum(right_model)) == mid);
                                                                rewrite(parent_model == 0); rewrite(color == Color::Black); normalize();
                                                            }
                                                            have is_rb_root(remaining.model) == 1 by {
                                                                rewrite(remaining.model == rb_successor_child_splice(mid, parent_model, color, left_model, right_model));
                                                                have rb_successor_child_splice(mid, parent_model, color, left_model, right_model)
                                                                    == plug(Context::Top, rb_successor_child_splice(mid, parent_model, color, left_model, right_model)) by {
                                                                    unfold(plug(Context::Top, rb_successor_child_splice(mid, parent_model, color, left_model, right_model))); normalize();
                                                                }
                                                                rewrite(rb_successor_child_splice(mid, parent_model, color, left_model, right_model)
                                                                        == plug(Context::Top, rb_successor_child_splice(mid, parent_model, color, left_model, right_model))); assumption();
                                                            }
                                                            have rb_parent_consistent(remaining.model, 0) == 1 by {
                                                                have rb_parent_consistent(rb_successor_child_splice(mid, parent_model, color, left_model, right_model), 0) == 1 by {
                                                                    apply(ctx_consistent_top(rb_successor_child_splice(mid, parent_model, color, left_model, right_model), 0)); assumption();
                                                                }
                                                                rewrite(remaining.model == rb_successor_child_splice(mid, parent_model, color, left_model, right_model)); assumption();
                                                            }
                                                            have rb_inorder(remaining.model) == list_append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model)))) by {
                                                                rewrite(remaining.model == rb_successor_child_splice(mid, parent_model, color, left_model, right_model));
                                                                rewrite(rb_left(old(tree.model)) == left_model); rewrite(rb_right(old(tree.model)) == right_model); assumption();
                                                            }
                                                            execute(); fold(erase_callbacks(augment)); simp();
                                                        },
                                                    }

                                                },
                                            }
                                        },
                                    }
                                },
                            }
                        },
                    }
                },
            }
        },
    }
}
