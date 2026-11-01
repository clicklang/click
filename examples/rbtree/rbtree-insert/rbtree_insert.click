verifying "rb_insert_color.c";

import "../rbtree-model/rbtree_model.click";
import "../rbtree-model/rbtree_resources.click";

theorem ctx_rb_red_focus_not_top(ctx: Context, bh: Nat) {
    requires ctx_rb(ctx, bh, Color::Red) == 1;

    ensures ctx != Context::Top by {
        induct(ctx) as ih {
            Context::Top => {
                have ctx_rb(Context::Top, bh, Color::Red) != 1 by {
                    unfold(ctx_rb(Context::Top, bh, Color::Red));
                    unfold(color_black(Color::Red));
                    normalize();
                }
                contradiction(ctx_rb(Context::Top, bh, Color::Red) == 1);
            }
            Context::Left(identity, grandparent, color, sibling_model, up_model) => {
                normalize();
            }
            Context::Right(identity, grandparent, color, sibling_model, up_model) => {
                normalize();
            }
        }
    }
}

theorem color_bit_zero_is_red(color: Color) {
    requires color_bit(color) == 0;

    ensures color == Color::Red by {
        induct(color) as ih {
            Color::Red => {
                normalize();
            }
            Color::Black => {
                have color_bit(Color::Black) != 0;
                contradiction(color_bit(Color::Black) == 0);
            }
        }
    }
}

theorem color_bit_one_is_black(color: Color) {
    requires color_bit(color) == 1;

    ensures color == Color::Black by {
        induct(color) as ih {
            Color::Red => {
                have color_bit(Color::Red) != 1;
                contradiction(color_bit(Color::Red) == 1);
            }
            Color::Black => {
                normalize();
            }
        }
    }
}

theorem rb_root_black_node_color_bit(node: struct rb_node*, parent: struct rb_node*,
                                     color: Color, left: RbTree, right: RbTree) {
    requires rb_root_black(RbTree::Node(node, parent, color, left, right)) == 1;

    ensures color_bit(color) == 1 by {
        induct(color) as ih {
            Color::Red => {
                have rb_root_black(RbTree::Node(node, parent, Color::Red, left, right)) != 1 by {
                    unfold(rb_root_black(RbTree::Node(node, parent, Color::Red, left, right)));
                    normalize();
                }
                contradiction(rb_root_black(RbTree::Node(node, parent, Color::Red, left, right))
                    == 1);
            }
            Color::Black => {
                unfold(color_bit(Color::Black));
                normalize();
            }
        }
    }
}

theorem ctx_node_is_top_null(p: struct rb_node*) {
    requires ctx_node_is(Context::Top, p) == 1;

    ensures p == 0;
}

theorem rb_ptr_transitive(a: struct rb_node*, b: struct rb_node*, c: struct rb_node*) {
    requires a == b;
    requires a == c;

    ensures c == b by solve();
}

theorem rb_has_parent_node(identity: struct rb_node*, parent: struct rb_node*, color: Color,
                           left: RbTree, right: RbTree, q: struct rb_node*) {
    requires rb_has_parent(RbTree::Node(identity, parent, color, left, right), q) == 1;

    ensures parent == q;
}

theorem rb_has_parent_same(sub: RbTree, q: struct rb_node*, p: struct rb_node*) {
    requires rb_has_parent(sub, q) == 1;
    requires rb_has_parent(sub, p) == 1;

    ensures p == q by {
        induct(sub) as ih {
            RbTree::Empty => {
                have rb_has_parent(RbTree::Empty, q) != 1;
                contradiction(rb_has_parent(RbTree::Empty, q) == 1);
            }
            RbTree::Node(identity, parent, color, left, right) => {
                apply(rb_has_parent_node(identity, parent, color, left, right, q));
                apply(rb_has_parent_node(identity, parent, color, left, right, p));
                apply(rb_ptr_transitive(parent, q, p));
                assumption();
            }
        }
    }
}

theorem ctx_holds_top_parent(sub: RbTree) {
    requires ctx_holds(Context::Top, sub) == 1;

    ensures rb_has_parent(sub, 0) == 1 by {
        unfold(ctx_holds(Context::Top, sub));
        rewrite(rb_has_parent(sub, 0) == ctx_holds(Context::Top, sub));
        assumption();
    }
}

theorem ctx_holds_left_parent(cid: struct rb_node*, grandparent: struct rb_node*,
                              ccolor: Color, sibling_model: RbTree, up_model: Context,
                              sub: RbTree) {
    requires ctx_holds(Context::Left(cid, grandparent, ccolor, sibling_model, up_model),
        sub) == 1;

    ensures rb_has_parent(sub, cid) == 1 by {
        unfold(ctx_holds(
            Context::Left(cid, grandparent, ccolor, sibling_model, up_model), sub));
        rewrite(rb_has_parent(sub, cid)
            == ctx_holds(Context::Left(cid, grandparent, ccolor, sibling_model, up_model),
                sub));
        assumption();
    }
}

theorem ctx_holds_right_parent(cid: struct rb_node*, grandparent: struct rb_node*,
                               ccolor: Color, sibling_model: RbTree, up_model: Context,
                               sub: RbTree) {
    requires ctx_holds(Context::Right(cid, grandparent, ccolor, sibling_model, up_model),
        sub) == 1;

    ensures rb_has_parent(sub, cid) == 1 by {
        unfold(ctx_holds(
            Context::Right(cid, grandparent, ccolor, sibling_model, up_model), sub));
        rewrite(rb_has_parent(sub, cid)
            == ctx_holds(Context::Right(cid, grandparent, ccolor, sibling_model, up_model),
                sub));
        assumption();
    }
}

theorem ctx_node_is_from_parent(ctx: Context, sub: RbTree, p: struct rb_node*) {
    requires ctx_holds(ctx, sub) == 1;
    requires rb_has_parent(sub, p) == 1;

    ensures ctx_node_is(ctx, p) == 1 by {
        induct(ctx) as ih {
            Context::Top => {
                apply(ctx_holds_top_parent(sub));
                apply(rb_has_parent_same(sub, 0, p));
                have ctx_node_is(Context::Top, p) == 1 by {
                    unfold(ctx_node_is(Context::Top, p));
                    normalize() using { p == 0; };
                }
                assumption();
            }
            Context::Left(cid, grandparent, ccolor, sibling_model, up_model) => {
                apply(ctx_holds_left_parent(cid, grandparent, ccolor, sibling_model,
                    up_model, sub));
                apply(rb_has_parent_same(sub, cid, p));
                have ctx_node_is(
                    Context::Left(cid, grandparent, ccolor, sibling_model, up_model),
                    p) == 1 by {
                    unfold(ctx_node_is(
                        Context::Left(cid, grandparent, ccolor, sibling_model, up_model), p));
                    normalize() using { p == cid; };
                }
                assumption();
            }
            Context::Right(cid, grandparent, ccolor, sibling_model, up_model) => {
                apply(ctx_holds_right_parent(cid, grandparent, ccolor, sibling_model,
                    up_model, sub));
                apply(rb_has_parent_same(sub, cid, p));
                have ctx_node_is(
                    Context::Right(cid, grandparent, ccolor, sibling_model, up_model),
                    p) == 1 by {
                    unfold(ctx_node_is(
                        Context::Right(cid, grandparent, ccolor, sibling_model, up_model), p));
                    normalize() using { p == cid; };
                }
                assumption();
            }
        }
    }
}

theorem ctx_node_is_left_identity(cid: struct rb_node*, grandparent: struct rb_node*,
                                  ccolor: Color, sibling_model: RbTree, up_model: Context,
                                  p: struct rb_node*) {
    requires ctx_node_is(Context::Left(cid, grandparent, ccolor, sibling_model, up_model),
        p) == 1;

    ensures p == cid;
}

theorem ctx_node_is_right_identity(cid: struct rb_node*, grandparent: struct rb_node*,
                                   ccolor: Color, sibling_model: RbTree, up_model: Context,
                                   p: struct rb_node*) {
    requires ctx_node_is(Context::Right(cid, grandparent, ccolor, sibling_model, up_model),
        p) == 1;

    ensures p == cid;
}

theorem ctx_reroot_top_fixed(p: struct rb_node*) {
    ensures Context::Top == ctx_reroot(Context::Top, p) by {
        unfold(ctx_reroot(Context::Top, p));
        normalize();
    }
}

theorem ctx_reroot_left_fixed(cid: struct rb_node*, grandparent: struct rb_node*,
                              ccolor: Color, sibling_model: RbTree, up_model: Context,
                              p: struct rb_node*) {
    requires ctx_node_is(Context::Left(cid, grandparent, ccolor, sibling_model, up_model),
        p) == 1;

    ensures Context::Left(cid, grandparent, ccolor, sibling_model, up_model)
        == ctx_reroot(Context::Left(cid, grandparent, ccolor, sibling_model, up_model), p) by {
        if p == cid {
            unfold(ctx_reroot(
                Context::Left(cid, grandparent, ccolor, sibling_model, up_model), p));
            rewrite(p == cid);
            normalize();
        } else {
            have ctx_node_is(
                Context::Left(cid, grandparent, ccolor, sibling_model, up_model), p) != 1 by {
                unfold(ctx_node_is(
                    Context::Left(cid, grandparent, ccolor, sibling_model, up_model), p));
                normalize() using { not(p == cid); };
            }
            contradiction(ctx_node_is(
                Context::Left(cid, grandparent, ccolor, sibling_model, up_model), p) == 1);
        }
    }
}

theorem ctx_reroot_right_fixed(cid: struct rb_node*, grandparent: struct rb_node*,
                               ccolor: Color, sibling_model: RbTree, up_model: Context,
                               p: struct rb_node*) {
    requires ctx_node_is(Context::Right(cid, grandparent, ccolor, sibling_model, up_model),
        p) == 1;

    ensures Context::Right(cid, grandparent, ccolor, sibling_model, up_model)
        == ctx_reroot(Context::Right(cid, grandparent, ccolor, sibling_model, up_model), p) by {
        if p == cid {
            unfold(ctx_reroot(
                Context::Right(cid, grandparent, ccolor, sibling_model, up_model), p));
            rewrite(p == cid);
            normalize();
        } else {
            have ctx_node_is(
                Context::Right(cid, grandparent, ccolor, sibling_model, up_model), p) != 1 by {
                unfold(ctx_node_is(
                    Context::Right(cid, grandparent, ccolor, sibling_model, up_model), p));
                normalize() using { not(p == cid); };
            }
            contradiction(ctx_node_is(
                Context::Right(cid, grandparent, ccolor, sibling_model, up_model), p) == 1);
        }
    }
}

theorem ctx_reroot_fixed(ctx: Context, p: struct rb_node*) {
    requires ctx_node_is(ctx, p) == 1;

    ensures ctx == ctx_reroot(ctx, p) by {
        induct(ctx) as ih {
            Context::Top => {
                apply(ctx_reroot_top_fixed(p));
                assumption();
            }
            Context::Left(cid, grandparent, ccolor, sibling_model, up_model) => {
                apply(ctx_reroot_left_fixed(cid, grandparent, ccolor, sibling_model,
                    up_model, p));
                assumption();
            }
            Context::Right(cid, grandparent, ccolor, sibling_model, up_model) => {
                apply(ctx_reroot_right_fixed(cid, grandparent, ccolor, sibling_model,
                    up_model, p));
                assumption();
            }
        }
    }
}

function ctx_depth(ctx: Context) -> Integer
    decreases ctx
{
    match ctx {
        Context::Top => 0,
        Context::Left(identity, grandparent, color, sibling_model, up_model) =>
            ctx_depth(up_model) + 1,
        Context::Right(identity, grandparent, color, sibling_model, up_model) =>
            ctx_depth(up_model) + 1,
    }
}

theorem ctx_depth_is_nonnegative(ctx: Context) {
    ensures 0 <= ctx_depth(ctx) by {
        induct(ctx) as ih {
            Context::Top => {
                unfold(ctx_depth(Context::Top));
                normalize();
            }
            Context::Left(identity, grandparent, color, sibling_model, up_model) => {
                apply(ih(up_model));
                unfold(ctx_depth(Context::Left(identity, grandparent, color, sibling_model, up_model)));
                solve() using { 0 <= ctx_depth(up_model); };
            }
            Context::Right(identity, grandparent, color, sibling_model, up_model) => {
                apply(ih(up_model));
                unfold(ctx_depth(Context::Right(identity, grandparent, color, sibling_model, up_model)));
                solve() using { 0 <= ctx_depth(up_model); };
            }
        }
    }
}

theorem rb_parent_consistent_parent_is(t: RbTree, p: struct rb_node*) {
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

tactic refold_to_root(focus: struct rb_node*, root: struct rb_root*) {
    consumes c: ctx_at(focus, root);
    decreases ctx_depth(c.model);
    consumes t: rb_at(focus);
    requires rb_tree_parent_consistent(plug(c.model, t.model)) == 1;
    produces whole: rb_root_at(root);
    ensures whole.model == plug(old(c.model), old(t.model));
} by {
    match c.model {
        Context::Top => {
            unfold(c);
            let whole = fold(rb_root_at(root), { model: t.model }, { tree: t });
            have whole.model == plug(old(c.model), old(t.model));
        },
        Context::Left(identity, grandparent, color, sibling_model, up_model) => {
            have rb_parent_consistent(plug(Context::Left(identity, grandparent, color, sibling_model, up_model), t.model), 0) == 1;
            apply(plug_parent_consistent_ctx(Context::Left(identity, grandparent, color, sibling_model, up_model), t.model, 0)) using {
                rb_parent_consistent(plug(Context::Left(identity, grandparent, color, sibling_model, up_model), t.model), 0) == 1;
            };
            apply(ctx_consistent_left_focus(identity, grandparent, color, sibling_model, up_model, t.model, 0)) using {
                ctx_consistent(Context::Left(identity, grandparent, color, sibling_model, up_model), t.model, 0) == 1;
            };
            apply(rb_parent_consistent_parent_is(t.model, identity)) using {
                rb_parent_consistent(t.model, identity) == 1;
            };
            let { sibling: s, up: u } = unfold(c);
            let sub = fold(rb_at(identity), { model: RbTree::Node(identity, grandparent, color, old(t.model), sibling_model) }, { left: t, right: s });
            apply(ctx_depth_is_nonnegative(up_model));
            have ctx_depth(old(c.model)) == ctx_depth(up_model) + 1 by {
                rewrite(old(c.model) == Context::Left(identity, grandparent, color, sibling_model, up_model));
                unfold(ctx_depth(Context::Left(identity, grandparent, color, sibling_model, up_model)));
                normalize();
            }
            have ctx_depth(u.model) < ctx_depth(old(c.model));
            have plug(Context::Left(identity, grandparent, color, sibling_model, up_model), old(t.model)) == plug(up_model, RbTree::Node(identity, grandparent, color, old(t.model), sibling_model));
            have rb_tree_parent_consistent(plug(u.model, sub.model)) == 1;
            let { whole: whole } = refold_to_root(identity, root, { c: u, t: sub });
            have whole.model == plug(old(c.model), old(t.model));
        },
        Context::Right(identity, grandparent, color, sibling_model, up_model) => {
            have rb_parent_consistent(plug(Context::Right(identity, grandparent, color, sibling_model, up_model), t.model), 0) == 1;
            apply(plug_parent_consistent_ctx(Context::Right(identity, grandparent, color, sibling_model, up_model), t.model, 0)) using {
                rb_parent_consistent(plug(Context::Right(identity, grandparent, color, sibling_model, up_model), t.model), 0) == 1;
            };
            apply(ctx_consistent_right_focus(identity, grandparent, color, sibling_model, up_model, t.model, 0)) using {
                ctx_consistent(Context::Right(identity, grandparent, color, sibling_model, up_model), t.model, 0) == 1;
            };
            apply(rb_parent_consistent_parent_is(t.model, identity)) using {
                rb_parent_consistent(t.model, identity) == 1;
            };
            let { sibling: s, up: u } = unfold(c);
            let sub = fold(rb_at(identity), { model: RbTree::Node(identity, grandparent, color, sibling_model, old(t.model)) }, { left: s, right: t });
            apply(ctx_depth_is_nonnegative(up_model));
            have ctx_depth(old(c.model)) == ctx_depth(up_model) + 1 by {
                rewrite(old(c.model) == Context::Right(identity, grandparent, color, sibling_model, up_model));
                unfold(ctx_depth(Context::Right(identity, grandparent, color, sibling_model, up_model)));
                normalize();
            }
            have ctx_depth(u.model) < ctx_depth(old(c.model));
            have plug(Context::Right(identity, grandparent, color, sibling_model, up_model), old(t.model)) == plug(up_model, RbTree::Node(identity, grandparent, color, sibling_model, old(t.model)));
            have rb_tree_parent_consistent(plug(u.model, sub.model)) == 1;
            let { whole: whole } = refold_to_root(identity, root, { c: u, t: sub });
            have whole.model == plug(old(c.model), old(t.model));
        },
    }
}

contract void AugmentRotate(struct rb_node* old, struct rb_node* new) {
    requires new != 0;
    ensures 1 == 1;
}

void dummy_rotate(struct rb_node* old, struct rb_node* new) {
    requires new != 0;
    ensures 1 == 1;
}

void __rb_insert(struct rb_node* node, struct rb_root* root,
                 void (*augment_rotate)(struct rb_node*, struct rb_node*)) {
    requires AugmentRotate(augment_rotate);
    consumes c: ctx_at(node, root);
    consumes t: rb_at(node);
    requires t.model != RbTree::Empty;
    requires rb_color_bit(t.model) == 0;
    requires ctx_holds(c.model, t.model) == 1;
    requires is_rb(t.model) == 1;
    requires ctx_almost_rb_insert(c.model, black_height(t.model)) == 1;
    requires rb_tree_parent_consistent(plug(c.model, t.model)) == 1;
    produces tree: rb_root_at(root);
    ensures rb_inorder(tree.model) == rb_inorder(plug(old(c.model), old(t.model)));
    ensures is_rb_root(tree.model) == 1;
    ensures rb_tree_parent_consistent(tree.model) == 1;
} by {
    match t.model {
        RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
        RbTree::Node(identity, node_parent, color, left_model, right_model) => {
            let { left: l, right: r } = unfold(t);
            have (node->__rb_parent_color & 1) == rb_color_bit(old(t.model)) by {
                rewrite(old(t.model)
                    == RbTree::Node(identity, node_parent, color, left_model, right_model));
                unfold(rb_color_bit(
                    RbTree::Node(identity, node_parent, color, left_model, right_model)));
                assumption();
            }
            step();
            step();
            step();
            step();
            let t = fold(rb_at(node), { model: old(t.model) }, { left: l, right: r });
            have rb_has_parent(t.model, node_parent) == 1 by {
                rewrite(t.model
                    == RbTree::Node(identity, node_parent, color, left_model, right_model));
                unfold(rb_has_parent(
                    RbTree::Node(identity, node_parent, color, left_model, right_model),
                    node_parent));
                normalize();
            }
            have ctx_node_is(c.model, node_parent) == 1 by {
                apply(ctx_node_is_from_parent(c.model, t.model, node_parent)) using {
                    ctx_holds(c.model, t.model) == 1;
                    rb_has_parent(t.model, node_parent) == 1;
                };
                assumption();
            }
            have c.model == ctx_reroot(c.model, node_parent) by {
                apply(ctx_reroot_fixed(c.model, node_parent)) using {
                    ctx_node_is(c.model, node_parent) == 1;
                };
                assumption();
            }
            have parent == node_parent;
            loop {
                owns c: ctx_at(node, root);
                owns t: rb_at(node);
                decreases c;
                invariant t.model != RbTree::Empty;
                invariant rb_color_bit(t.model) == 0;
                invariant rb_parent_is(t.model, parent) == 1;
                invariant ctx_node_is(c.model, parent) == 1;
                invariant c.model == ctx_reroot(c.model, parent);
                invariant is_rb(t.model) == 1;
                invariant ctx_almost_rb_insert(c.model, black_height(t.model)) == 1;
                invariant rb_inorder(plug(c.model, t.model))
                    == rb_inorder(plug(old(c.model),
                        RbTree::Node(identity, node_parent, color,
                            left_model, right_model)));
                invariant rb_tree_parent_consistent(plug(c.model, t.model)) == 1;

                initialize by solve();
                preserve by {
                    match t.model {
                        RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
                        RbTree::Node(nid, nparent, ncolor, nleft, nright) => {
                            if parent == 0 {
                                match c.model {
                                    Context::Left(cid, cgp, ccolor, csib, cup) => {
                                        have ctx_node_is(Context::Left(cid, cgp, ccolor, csib, cup), parent) == 1 by {
                                            rewrite(Context::Left(cid, cgp, ccolor, csib, cup) == c.model);
                                            assumption();
                                        }
                                        have parent == cid by {
                                            apply(ctx_node_is_left_identity(cid, cgp, ccolor, csib, cup, parent)) using {
                                                ctx_node_is(Context::Left(cid, cgp, ccolor, csib, cup), parent) == 1;
                                            };
                                            assumption();
                                        }
                                        let { sibling: cs, up: cu } = unfold(c);
                                        have parent != 0 by {
                                            rewrite(parent == cid);
                                            assumption();
                                        }
                                        contradiction(parent == 0);
                                    },
                                    Context::Right(cid, cgp, ccolor, csib, cup) => {
                                        have ctx_node_is(Context::Right(cid, cgp, ccolor, csib, cup), parent) == 1 by {
                                            rewrite(Context::Right(cid, cgp, ccolor, csib, cup) == c.model);
                                            assumption();
                                        }
                                        have parent == cid by {
                                            apply(ctx_node_is_right_identity(cid, cgp, ccolor, csib, cup, parent)) using {
                                                ctx_node_is(Context::Right(cid, cgp, ccolor, csib, cup), parent) == 1;
                                            };
                                            assumption();
                                        }
                                        let { sibling: cs, up: cu } = unfold(c);
                                        have parent != 0 by {
                                            rewrite(parent == cid);
                                            assumption();
                                        }
                                        contradiction(parent == 0);
                                    },
                                    Context::Top => {
                                        have rb_parent_is(RbTree::Node(nid, nparent, ncolor, nleft, nright), parent) == 1 by {
                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                            assumption();
                                        }
                                        have nparent == parent by {
                                            apply(rb_parent_is_node_parent(nid, nparent, ncolor, nleft, nright, parent)) using {
                                                rb_parent_is(RbTree::Node(nid, nparent, ncolor, nleft, nright), parent) == 1;
                                            };
                                            assumption();
                                        }
                                        have RbTree::Node(nid, 0, Color::Black, nleft, nright) == rb_recolor(RbTree::Node(nid, nparent, ncolor, nleft, nright), Color::Black) by {
                                            unfold(rb_recolor(RbTree::Node(nid, nparent, ncolor, nleft, nright), Color::Black));
                                            solve();
                                        }
                                        have is_rb(RbTree::Node(nid, nparent, ncolor, nleft, nright)) == 1 by {
                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                            assumption();
                                        }
                                        have is_rb_root(plug(Context::Top, rb_recolor(RbTree::Node(nid, nparent, ncolor, nleft, nright), Color::Black))) == 1 by {
                                            apply(ctx_insert_root_exit(RbTree::Node(nid, nparent, ncolor, nleft, nright))) using {
                                                is_rb(RbTree::Node(nid, nparent, ncolor, nleft, nright)) == 1;
                                            };
                                            assumption();
                                        }
                                        have is_rb_root(plug(Context::Top, RbTree::Node(nid, 0, Color::Black, nleft, nright))) == 1 by {
                                            rewrite(RbTree::Node(nid, 0, Color::Black, nleft, nright) == rb_recolor(RbTree::Node(nid, nparent, ncolor, nleft, nright), Color::Black));
                                            assumption();
                                        }
                                        have rb_inorder(plug(Context::Top, rb_recolor(RbTree::Node(nid, nparent, ncolor, nleft, nright), Color::Black))) == rb_inorder(plug(Context::Top, RbTree::Node(nid, nparent, ncolor, nleft, nright))) by {
                                            apply(plug_recolor_inorder(Context::Top, RbTree::Node(nid, nparent, ncolor, nleft, nright), Color::Black));
                                            assumption();
                                        }
                                        have rb_inorder(plug(Context::Top, RbTree::Node(nid, 0, Color::Black, nleft, nright))) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                            rewrite(RbTree::Node(nid, 0, Color::Black, nleft, nright) == rb_recolor(RbTree::Node(nid, nparent, ncolor, nleft, nright), Color::Black));
                                            rewrite(rb_inorder(plug(Context::Top, rb_recolor(RbTree::Node(nid, nparent, ncolor, nleft, nright), Color::Black))) == rb_inorder(plug(Context::Top, RbTree::Node(nid, nparent, ncolor, nleft, nright))));
                                            assumption();
                                        }
                                        have rb_parent_consistent(plug(Context::Top, RbTree::Node(nid, nparent, ncolor, nleft, nright)), 0) == 1 by {
                                            unfold(rb_tree_parent_consistent(plug(Context::Top, RbTree::Node(nid, nparent, ncolor, nleft, nright))));
                                            rewrite(rb_parent_consistent(plug(Context::Top, RbTree::Node(nid, nparent, ncolor, nleft, nright)), 0) == rb_tree_parent_consistent(plug(Context::Top, RbTree::Node(nid, nparent, ncolor, nleft, nright))));
                                            rewrite(Context::Top == c.model);
                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                            assumption();
                                        }
                                        have rb_parent_consistent(RbTree::Node(nid, nparent, ncolor, nleft, nright), 0) == 1 by {
                                            unfold(plug(Context::Top, RbTree::Node(nid, nparent, ncolor, nleft, nright)));
                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == plug(Context::Top, RbTree::Node(nid, nparent, ncolor, nleft, nright)));
                                            assumption();
                                        }
                                        have rb_parent_consistent(rb_recolor(RbTree::Node(nid, nparent, ncolor, nleft, nright), Color::Black), 0) == 1 by {
                                            apply(rb_recolor_parent_consistent(RbTree::Node(nid, nparent, ncolor, nleft, nright), Color::Black, 0)) using {
                                                rb_parent_consistent(RbTree::Node(nid, nparent, ncolor, nleft, nright), 0) == 1;
                                            };
                                            assumption();
                                        }
                                        have rb_parent_consistent(plug(Context::Top, RbTree::Node(nid, 0, Color::Black, nleft, nright)), 0) == 1 by {
                                            unfold(plug(Context::Top, RbTree::Node(nid, 0, Color::Black, nleft, nright)));
                                            rewrite(RbTree::Node(nid, 0, Color::Black, nleft, nright) == rb_recolor(RbTree::Node(nid, nparent, ncolor, nleft, nright), Color::Black));
                                            assumption();
                                        }
                                        let { left: l, right: r } = unfold(t);
                                        step();
                                        step();
                                        have node->__rb_parent_color == 1 by { assumption(); }
                                        have (node->__rb_parent_color & 1)
                                            == color_bit(Color::Black) by {
                                            rewrite(node->__rb_parent_color == 1);
                                            unfold(color_bit(Color::Black));
                                            normalize();
                                        }
                                        have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == 0 by {
                                            rewrite(node->__rb_parent_color == 1);
                                            normalize();
                                        }
                                        let t = fold(rb_at(node),
                                            { model: RbTree::Node(nid, 0, Color::Black, nleft, nright) },
                                            { left: l, right: r });
                                        have is_rb_root(plug(c.model, t.model)) == 1 by {
                                            rewrite(c.model == Context::Top);
                                            rewrite(t.model == RbTree::Node(nid, 0, Color::Black, nleft, nright));
                                            assumption();
                                        }
                                        have rb_inorder(plug(c.model, t.model)) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                            rewrite(c.model == Context::Top);
                                            rewrite(t.model == RbTree::Node(nid, 0, Color::Black, nleft, nright));
                                            assumption();
                                        }
                                        have rb_tree_parent_consistent(plug(c.model, t.model)) == 1 by {
                                            unfold(rb_tree_parent_consistent(plug(c.model, t.model)));
                                            rewrite(c.model == Context::Top);
                                            rewrite(t.model == RbTree::Node(nid, 0, Color::Black, nleft, nright));
                                            assumption();
                                        }
                                        step();
                                    },
                                }
                            } else {
                                match c.model {
                                    Context::Top => {
                                        have ctx_node_is(Context::Top, parent) == 1 by {
                                            rewrite(Context::Top == c.model);
                                            assumption();
                                        }
                                        unfold(ctx_node_is(Context::Top, parent));
                                        have parent == 0;
                                        contradiction(parent == 0);
                                    },
                                    Context::Left(cid, cgp, ccolor, csib, cup) => {
                                        have ctx_node_is(Context::Left(cid, cgp, ccolor,
                                            csib, cup), parent) == 1 by {
                                            rewrite(Context::Left(cid, cgp, ccolor, csib, cup)
                                                == c.model);
                                            assumption();
                                        }
                                        have parent == cid by {
                                            apply(ctx_node_is_left_identity(cid, cgp, ccolor,
                                                csib, cup, parent)) using {
                                                ctx_node_is(Context::Left(cid, cgp, ccolor,
                                                    csib, cup), parent) == 1;
                                            };
                                            assumption();
                                        }
                                        have ctx_rb(Context::Left(cid, cgp, ccolor, csib, cup),
                                            black_height(t.model), Color::Black) == 1 by {
                                            apply(ctx_almost_rb_insert_black_focus(c.model,
                                                black_height(t.model))) using {
                                                ctx_almost_rb_insert(c.model,
                                                    black_height(t.model)) == 1;
                                            };
                                            rewrite(Context::Left(cid, cgp, ccolor, csib, cup)
                                                == c.model);
                                            assumption();
                                        }
                                        have rb_inorder(plug(Context::Left(cid, cgp, ccolor, csib, cup), t.model))
                                            == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                            rewrite(Context::Left(cid, cgp, ccolor, csib, cup) == c.model);
                                            assumption();
                                        }
                                        have rb_parent_consistent(plug(Context::Left(cid, cgp, ccolor, csib, cup), t.model), 0) == 1 by {
                                            unfold(rb_tree_parent_consistent(plug(Context::Left(cid, cgp, ccolor, csib, cup), t.model)));
                                            rewrite(rb_parent_consistent(plug(Context::Left(cid, cgp, ccolor, csib, cup), t.model), 0)
                                                == rb_tree_parent_consistent(plug(Context::Left(cid, cgp, ccolor, csib, cup), t.model)));
                                            rewrite(Context::Left(cid, cgp, ccolor, csib, cup) == c.model);
                                            assumption();
                                        }
                                        have ctx_almost_rb_insert(Context::Left(cid, cgp, ccolor, csib, cup), black_height(t.model)) == 1 by {
                                            rewrite(Context::Left(cid, cgp, ccolor, csib, cup) == c.model);
                                            assumption();
                                        }
                                        let { sibling: cs, up: cu } = unfold(c);
                                        step();
                                        step();
                                        match ccolor {
                                            Color::Black => {
                                                have (parent->__rb_parent_color & 1) == 1 by {
                                                    rewrite((parent->__rb_parent_color & 1)
                                                        == color_bit(ccolor));
                                                    rewrite(ccolor == Color::Black);
                                                    unfold(color_bit(Color::Black));
                                                    solve();
                                                }
                                                have ctx_almost_rb_insert(Context::Left(cid, cgp, Color::Black, csib, cup), black_height(t.model)) == 1 by {
                                                    rewrite(Color::Black == ccolor);
                                                    assumption();
                                                }
                                                have ctx_rb(Context::Left(cid, cgp, Color::Black, csib, cup), black_height(t.model), rb_color(t.model)) == 1 by {
                                                    apply(ctx_black_frame_left_restores(cid, cgp, csib, cup, black_height(t.model), rb_color(t.model))) using {
                                                        ctx_almost_rb_insert(Context::Left(cid, cgp, Color::Black, csib, cup), black_height(t.model)) == 1;
                                                    };
                                                    assumption();
                                                }
                                                have is_rb_root(plug(Context::Left(cid, cgp, Color::Black, csib, cup), t.model)) == 1 by {
                                                    apply(ctx_insert_black_parent_exit(Context::Left(cid, cgp, Color::Black, csib, cup), t.model)) using {
                                                        is_rb(t.model) == 1;
                                                        ctx_rb(Context::Left(cid, cgp, Color::Black, csib, cup), black_height(t.model), rb_color(t.model)) == 1;
                                                    };
                                                    assumption();
                                                }
                                                have (parent->__rb_parent_color & 1) != 0 by {
                                                    rewrite((parent->__rb_parent_color & 1) == 1);
                                                    normalize();
                                                }
                                                step();
                                                let c = fold(ctx_at(node, root),
                                                    { model: Context::Left(cid, cgp, ccolor,
                                                        csib, cup) },
                                                    { sibling: cs, up: cu });
                                                have is_rb_root(plug(c.model, t.model)) == 1 by {
                                                    rewrite(c.model == Context::Left(cid, cgp, ccolor, csib, cup));
                                                    rewrite(ccolor == Color::Black);
                                                    assumption();
                                                }
                                                have rb_tree_parent_consistent(plug(c.model, t.model)) == 1 by {
                                                    unfold(rb_tree_parent_consistent(plug(c.model, t.model)));
                                                }
                                                step();
                                            },
                                            Color::Red => {
                                                have color_bit(ccolor) == 0 by {
                                                    rewrite(ccolor == Color::Red);
                                                    unfold(color_bit(Color::Red));
                                                    solve();
                                                }
                                                have ctx_rb(Context::Left(cid, cgp,
                                                    Color::Red, csib, cup),
                                                    black_height(t.model),
                                                    Color::Black) == 1 by {
                                                    rewrite(Color::Red == ccolor);
                                                    assumption();
                                                }
                                                have ctx_rb(cu.model,
                                                    black_height(t.model), Color::Red) == 1 by {
                                                    apply(ctx_rb_left_red_up(cid, cgp, csib, cup,
                                                        black_height(t.model),
                                                        Color::Black)) using {
                                                        ctx_rb(Context::Left(cid, cgp, Color::Red,
                                                            csib, cup), black_height(t.model),
                                                            Color::Black) == 1;
                                                    };
                                                    rewrite(cu.model == cup);
                                                    assumption();
                                                }
                                                step();
                                                step();
                                                step();
                                                have cu.model != Context::Top by {
                                                    apply(ctx_rb_red_focus_not_top(cu.model,
                                                        black_height(t.model))) using {
                                                        ctx_rb(cu.model,
                                                            black_height(t.model),
                                                            Color::Red) == 1;
                                                    };
                                                    assumption();
                                                }
                                                match cu.model {
                                                Context::Top => {
                                                    contradiction(cu.model == Context::Top);
                                                },
                                                Context::Left(uid, ugp, ucolor, usib, uup) => {
                                                    have ctx_node_is(Context::Left(uid, ugp, ucolor,
                                                        usib, uup), cgp) == 1 by {
                                                        rewrite(Context::Left(uid, ugp, ucolor, usib, uup)
                                                            == cu.model);
                                                        rewrite(cu.model == cup);
                                                        assumption();
                                                    }
                                                    have cgp == uid by {
                                                        apply(ctx_node_is_left_identity(uid, ugp, ucolor,
                                                            usib, uup, cgp)) using {
                                                            ctx_node_is(Context::Left(uid, ugp, ucolor,
                                                                usib, uup), cgp) == 1;
                                                        };
                                                        assumption();
                                                    }
                                                    have ctx_rb(Context::Left(uid, ugp, ucolor, usib, uup), black_height(t.model), Color::Red) == 1 by {
                                                        rewrite(Context::Left(uid, ugp, ucolor, usib, uup) == cu.model);
                                                        assumption();
                                                    }
                                                    let { sibling: us, up: uu } = unfold(cu);
                                                    mark before_grandparent_links;
                                                    have separate(memory(gparent->rb_right), memory(gparent->rb_left)) by { assumption(); }
                                                    have separate(memory(gparent->rb_right), memory(parent->rb_right)) by { assumption(); }
                                                    have separate(memory(gparent->rb_right), memory(gparent->__rb_parent_color)) by { assumption(); }
                                                    have separate(memory(gparent->rb_right), memory(parent->__rb_parent_color)) by { assumption(); }
                                                    have at(before_grandparent_links, ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp) by { assumption(); }
                                                    have separate(memory(gparent->__rb_parent_color), memory(gparent->rb_right)) by { assumption(); }
                                                    have separate(memory(gparent->__rb_parent_color), memory(parent->rb_left)) by { assumption(); }
                                                    step();
                                                    mark before_uncle_pointer_changes;
                                                    have at(before_uncle_pointer_changes, gparent->rb_right == at(before_uncle_pointer_changes, tmp)) by { assumption(); }
                                                    have at(before_uncle_pointer_changes, parent->rb_left == node) by { assumption(); }
                                                    have separate(memory(parent->rb_left), memory(gparent->rb_left)) by { assumption(); }
                                                    have separate(memory(parent->rb_left), memory(parent->rb_right)) by { assumption(); }
                                                    have separate(memory(parent->rb_left), memory(gparent->__rb_parent_color)) by { assumption(); }
                                                    have separate(memory(parent->rb_left), memory(parent->__rb_parent_color)) by { assumption(); }
                                                    if rb_root_black(usib) == 1 {
                                                        match us.model ensuring {
                                                            owns un: rb_at(tmp);
                                                            fact un.model == usib;
                                                        } {
                                                            RbTree::Node(unid, unp, uncolor, unl, unr) => {
                                                                let { left: ul, right: ur } = unfold(us);
                                                                step();
                                                                have rb_root_black(RbTree::Node(unid, unp, uncolor, unl, unr)) == 1 by {
                                                                    rewrite(RbTree::Node(unid, unp, uncolor, unl, unr) == usib);
                                                                    assumption();
                                                                }
                                                                have color_bit(uncolor) == 1 by {
                                                                    apply(rb_root_black_node_color_bit(unid, unp, uncolor, unl, unr)) using {
                                                                        rb_root_black(RbTree::Node(unid, unp, uncolor, unl, unr)) == 1;
                                                                    };
                                                                    assumption();
                                                                }
                                                                have uncolor == Color::Black by {
                                                                    apply(color_bit_one_is_black(uncolor)) using {
                                                                        color_bit(uncolor) == 1;
                                                                    };
                                                                    assumption();
                                                                }
                                                                step();
                                                                have ucolor == Color::Black by {
                                                                    apply(ctx_rb_left_red_focus_black(uid, ugp, ucolor, usib, uup, black_height(t.model))) using {
                                                                        ctx_rb(Context::Left(uid, ugp, ucolor, usib, uup), black_height(t.model), Color::Red) == 1;
                                                                    };
                                                                    assumption();
                                                                }
                                                                have rb_parent_is(RbTree::Node(unid, unp, uncolor, unl, unr), gparent) == 1 by {
                                                                    rewrite(RbTree::Node(unid, unp, uncolor, unl, unr) == usib);
                                                                    assumption();
                                                                }
                                                                have unp == gparent by {
                                                                    apply(rb_parent_is_node_parent(unid, unp, uncolor, unl, unr, gparent)) using {
                                                                        rb_parent_is(RbTree::Node(unid, unp, uncolor, unl, unr), gparent) == 1;
                                                                    };
                                                                    assumption();
                                                                }
                                                                have usib == RbTree::Node(unid, gparent, Color::Black, unl, unr) by {
                                                                    rewrite(usib == RbTree::Node(unid, unp, uncolor, unl, unr));
                                                                    rewrite(unp == gparent);
                                                                    rewrite(uncolor == Color::Black);
                                                                    normalize();
                                                                }
                                                                have (tmp->__rb_parent_color & 1) == color_bit(Color::Black) by {
                                                                    rewrite(Color::Black == uncolor);
                                                                    assumption();
                                                                }
                                                                let un = fold(rb_at(tmp), { model: RbTree::Node(unid, gparent, Color::Black, unl, unr) }, { left: ul, right: ur });
                                                                have un.model == usib by {
                                                                    rewrite(usib == RbTree::Node(unid, gparent, Color::Black, unl, unr));
                                                                    normalize();
                                                                }
                                                            },
                                                            RbTree::Empty => {
                                                                unfold(us);
                                                                step();
                                                                step();
                                                                have ucolor == Color::Black by {
                                                                    apply(ctx_rb_left_red_focus_black(uid, ugp, ucolor, usib, uup, black_height(t.model))) using {
                                                                        ctx_rb(Context::Left(uid, ugp, ucolor, usib, uup), black_height(t.model), Color::Red) == 1;
                                                                    };
                                                                    assumption();
                                                                }
                                                                let un = fold(rb_at(tmp), { model: RbTree::Empty });
                                                                have un.model == usib by {
                                                                    rewrite(usib == RbTree::Empty);
                                                                    normalize();
                                                                }
                                                            },
                                                        }
                                                        have cup == Context::Left(gparent, ugp, Color::Black, usib, uup) by {
                                                            rewrite(cup == Context::Left(uid, ugp, ucolor, usib, uup));
                                                            rewrite(ucolor == Color::Black);
                                                            rewrite(uid == gparent);
                                                            normalize();
                                                        }
                                                        have rb_parent_is(RbTree::Node(nid, nparent, ncolor, nleft, nright), parent) == 1 by {
                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                            assumption();
                                                        }
                                                        have nparent == cid by {
                                                            apply(rb_parent_is_node_parent(nid, nparent, ncolor, nleft, nright, parent)) using {
                                                                rb_parent_is(RbTree::Node(nid, nparent, ncolor, nleft, nright), parent) == 1;
                                                            };
                                                            solve();
                                                        }
                                                        have color_bit(ncolor) == 0 by {
                                                            unfold(rb_color_bit(RbTree::Node(nid, nparent, ncolor, nleft, nright)));
                                                            rewrite(color_bit(ncolor) == rb_color_bit(RbTree::Node(nid, nparent, ncolor, nleft, nright)));
                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                            assumption();
                                                        }
                                                        have ncolor == Color::Red by {
                                                            apply(color_bit_zero_is_red(ncolor)) using {
                                                                color_bit(ncolor) == 0;
                                                            };
                                                            assumption();
                                                        }
                                                        have t.model == RbTree::Node(nid, cid, Color::Red, nleft, nright) by {
                                                            rewrite(t.model == RbTree::Node(nid, nparent, ncolor, nleft, nright));
                                                            rewrite(nparent == cid);
                                                            rewrite(ncolor == Color::Red);
                                                            normalize();
                                                        }
                                                        have is_rb(RbTree::Node(nid, cid, Color::Red, nleft, nright)) == 1 by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright) == t.model);
                                                            assumption();
                                                        }
                                                        have ctx_rb(Context::Left(cid, gparent, Color::Red, csib, Context::Left(gparent, ugp, Color::Black, usib, uup)), black_height(RbTree::Node(nid, cid, Color::Red, nleft, nright)), Color::Black) == 1 by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright) == t.model);
                                                            rewrite(Context::Left(gparent, ugp, Color::Black, usib, uup) == cup);
                                                            rewrite(gparent == cgp);
                                                            rewrite(Color::Red == ccolor);
                                                            assumption();
                                                        }
                                                        have rb_parent_consistent(plug(Context::Left(cid, gparent, Color::Red, csib, Context::Left(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright)), 0) == 1 by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright) == t.model);
                                                            rewrite(Context::Left(gparent, ugp, Color::Black, usib, uup) == cup);
                                                            rewrite(gparent == cgp);
                                                            rewrite(Color::Red == ccolor);
                                                            assumption();
                                                        }
                                                        have rb_inorder(plug(Context::Left(cid, gparent, Color::Red, csib, Context::Left(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright))) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright) == t.model);
                                                            rewrite(Context::Left(gparent, ugp, Color::Black, usib, uup) == cup);
                                                            rewrite(gparent == cgp);
                                                            rewrite(Color::Red == ccolor);
                                                            assumption();
                                                        }
                                                        apply(ctx_insert_case3_left_step(ugp, gparent, cid, nid, nleft, nright, csib, usib, uup)) using {
                                                            is_rb(RbTree::Node(nid, cid, Color::Red, nleft, nright)) == 1;
                                                            rb_root_black(usib) == 1;
                                                            ctx_rb(Context::Left(cid, gparent, Color::Red, csib, Context::Left(gparent, ugp, Color::Black, usib, uup)), black_height(RbTree::Node(nid, cid, Color::Red, nleft, nright)), Color::Black) == 1;
                                                            rb_parent_consistent(plug(Context::Left(cid, gparent, Color::Red, csib, Context::Left(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright)), 0) == 1;
                                                        };
                                                        let { left: nl_at, right: nr_at } = unfold(t);
                                                        have (node->__rb_parent_color & 1) == color_bit(Color::Red) by {
                                                            rewrite(Color::Red == ncolor);
                                                            assumption();
                                                        }
                                                        match cs.model ensuring {
                                                            owns sn: rb_at(tmp);
                                                            fact sn.model == rb_reparent(csib, gparent);
                                                            fact ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp;
                                                            fact gparent->rb_right == at(before_uncle_pointer_changes, tmp);
                                                            fact parent->rb_left == node;
                                                        } {
                                                            RbTree::Empty => {
                                                                unfold(cs);
                                                                step();
                                                                step();
                                                                let t = fold(rb_at(node), { model: RbTree::Node(nid, cid, Color::Red, nleft, nright) }, { left: nl_at, right: nr_at });
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                have rb_reparent(csib, gparent) == RbTree::Empty by {
                                                                    rewrite(csib == RbTree::Empty);
                                                                    unfold(rb_reparent(RbTree::Empty, gparent)); normalize();
                                                                }
                                                                let sn = fold(rb_at(tmp), { model: RbTree::Empty });
                                                                have sn.model == rb_reparent(csib, gparent) by {
                                                                    rewrite(rb_reparent(csib, gparent) == RbTree::Empty);
                                                                    solve();
                                                                }
                                                                transport(at(before_grandparent_links, ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp), ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp);
                                                                transport(at(before_uncle_pointer_changes, gparent->rb_right == at(before_uncle_pointer_changes, tmp)), gparent->rb_right == at(before_uncle_pointer_changes, tmp)) using {
                                                                    at(before_uncle_pointer_changes, gparent->rb_right == at(before_uncle_pointer_changes, tmp));
                                                                    separate(memory(gparent->rb_right), memory(gparent->rb_left));
                                                                    separate(memory(gparent->rb_right), memory(parent->rb_right));
                                                                };
                                                                transport(at(before_uncle_pointer_changes, parent->rb_left == node), parent->rb_left == node) using {
                                                                    at(before_uncle_pointer_changes, parent->rb_left == node);
                                                                    separate(memory(parent->rb_left), memory(gparent->rb_left));
                                                                    separate(memory(parent->rb_left), memory(parent->rb_right));
                                                                };
                                                            },
                                                            RbTree::Node(sx, sp, scol, sl, sr) => {
                                                                let { left: sl_at, right: sr_at } = unfold(cs);
                                                                step();
                                                                step();
                                                                step();
                                                                have gparent == uid by { assumption(); }
                                                                have tmp == sx by { assumption(); }
                                                                have separate(memory(gparent->rb_right), memory(tmp->__rb_parent_color)) by { assumption(); }
                                                                have separate(memory(parent->rb_left), memory(tmp->__rb_parent_color)) by { assumption(); }
                                                                have separate(memory(uid->__rb_parent_color), memory(sx->__rb_parent_color)) by { assumption(); }
                                                                have separate(memory(gparent->__rb_parent_color), memory(tmp->__rb_parent_color)) by {
                                                                    rewrite(gparent == uid);
                                                                    rewrite(tmp == sx);
                                                                    assumption();
                                                                }
                                                                let t = fold(rb_at(node), { model: RbTree::Node(nid, cid, Color::Red, nleft, nright) }, { left: nl_at, right: nr_at });
                                                                have rb_root_black(RbTree::Node(sx, sp, scol, sl, sr)) == 1 by {
                                                                    rewrite(RbTree::Node(sx, sp, scol, sl, sr) == csib);
                                                                    assumption();
                                                                }
                                                                have color_bit(scol) == 1 by {
                                                                    apply(rb_root_black_node_color_bit(sx, sp, scol, sl, sr)) using {
                                                                        rb_root_black(RbTree::Node(sx, sp, scol, sl, sr)) == 1;
                                                                    };
                                                                    assumption();
                                                                }
                                                                have rb_reparent(csib, gparent) == RbTree::Node(sx, gparent, scol, sl, sr) by {
                                                                    rewrite(csib == RbTree::Node(sx, sp, scol, sl, sr));
                                                                    unfold(rb_reparent(RbTree::Node(sx, sp, scol, sl, sr), gparent)); normalize();
                                                                }
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                let sn = fold(rb_at(tmp), { model: RbTree::Node(sx, gparent, scol, sl, sr) }, { left: sl_at, right: sr_at });
                                                                have sn.model == rb_reparent(csib, gparent) by {
                                                                    rewrite(rb_reparent(csib, gparent) == RbTree::Node(sx, gparent, scol, sl, sr));
                                                                    solve();
                                                                }
                                                                transport(at(before_grandparent_links, ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp), ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp);
                                                                transport(at(before_uncle_pointer_changes, gparent->rb_right == at(before_uncle_pointer_changes, tmp)), gparent->rb_right == at(before_uncle_pointer_changes, tmp)) using {
                                                                    at(before_uncle_pointer_changes, gparent->rb_right == at(before_uncle_pointer_changes, tmp));
                                                                    separate(memory(gparent->rb_right), memory(gparent->rb_left));
                                                                    separate(memory(gparent->rb_right), memory(parent->rb_right));
                                                                    separate(memory(gparent->rb_right), memory(tmp->__rb_parent_color));
                                                                };
                                                                transport(at(before_uncle_pointer_changes, parent->rb_left == node), parent->rb_left == node) using {
                                                                    at(before_uncle_pointer_changes, parent->rb_left == node);
                                                                    separate(memory(parent->rb_left), memory(gparent->rb_left));
                                                                    separate(memory(parent->rb_left), memory(parent->rb_right));
                                                                    separate(memory(parent->rb_left), memory(tmp->__rb_parent_color));
                                                                };
                                                            },
                                                        }
                                                        transport(at(before_grandparent_links, ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp), ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp);
                                                        have (gparent->__rb_parent_color & 1) == 1 by {
                                                            rewrite((gparent->__rb_parent_color & 1) == color_bit(ucolor));
                                                            rewrite(ucolor == Color::Black);
                                                            unfold(color_bit(Color::Black));
                                                            solve();
                                                        }
                                                        mark before_rotation_parent_changes;
                                                        have at(before_rotation_parent_changes, gparent->rb_right == at(before_uncle_pointer_changes, tmp)) by { assumption(); }
                                                        have at(before_rotation_parent_changes, parent->rb_left == node) by { assumption(); }
                                                        match uu.model ensuring {
                                                            owns uu: ctx_at(parent, root);
                                                            fact uu.model == uup;
                                                            fact gparent->rb_right == at(before_uncle_pointer_changes, tmp);
                                                            fact parent->rb_left == node;
                                                        } {
                                                            Context::Top => {
                                                                have ctx_node_is(Context::Top, ugp) == 1 by {
                                                                    rewrite(Context::Top == uu.model);
                                                                    rewrite(uu.model == uup);
                                                                    assumption();
                                                                }
                                                                have ugp == 0 by {
                                                                    apply(ctx_node_is_top_null(ugp)) using {
                                                                        ctx_node_is(Context::Top, ugp) == 1;
                                                                    };
                                                                    assumption();
                                                                }
                                                                unfold(uu);
                                                                have separate(memory(gparent->rb_right), memory(root->rb_node)) by { assumption(); }
                                                                have separate(memory(parent->rb_left), memory(root->rb_node)) by { assumption(); }
                                                                step();
                                                                transport(at(before_rotation_parent_changes, gparent->rb_right == at(before_uncle_pointer_changes, tmp)), gparent->rb_right == at(before_uncle_pointer_changes, tmp)) using {
                                                                    at(before_rotation_parent_changes, gparent->rb_right == at(before_uncle_pointer_changes, tmp));
                                                                    separate(memory(gparent->rb_right), memory(gparent->__rb_parent_color));
                                                                    separate(memory(gparent->rb_right), memory(parent->__rb_parent_color));
                                                                    separate(memory(gparent->rb_right), memory(root->rb_node));
                                                                };
                                                                transport(at(before_rotation_parent_changes, parent->rb_left == node), parent->rb_left == node) using {
                                                                    at(before_rotation_parent_changes, parent->rb_left == node);
                                                                    separate(memory(parent->rb_left), memory(gparent->__rb_parent_color));
                                                                    separate(memory(parent->rb_left), memory(parent->__rb_parent_color));
                                                                    separate(memory(parent->rb_left), memory(root->rb_node));
                                                                };
                                                                let uu = fold(ctx_at(parent, root), { model: Context::Top });
                                                                have uu.model == uup by { rewrite(uup == Context::Top); normalize(); }
                                                            },
                                                            Context::Left(xid, xgp, xcol, xsib, xup) => {
                                                                have ctx_node_is(Context::Left(xid, xgp, xcol, xsib, xup), ugp) == 1 by {
                                                                    rewrite(Context::Left(xid, xgp, xcol, xsib, xup) == uu.model);
                                                                    rewrite(uu.model == uup);
                                                                    assumption();
                                                                }
                                                                have ugp == xid by {
                                                                    apply(ctx_node_is_left_identity(xid, xgp, xcol, xsib, xup, ugp)) using {
                                                                        ctx_node_is(Context::Left(xid, xgp, xcol, xsib, xup), ugp) == 1;
                                                                    };
                                                                    assumption();
                                                                }
                                                                let { sibling: xs, up: xu } = unfold(uu);
                                                                have separate(memory(gparent->rb_right), memory(xid->rb_left)) by { assumption(); }
                                                                have separate(memory(parent->rb_left), memory(xid->rb_left)) by { assumption(); }
                                                                have separate(memory(gparent->rb_right), memory(xid->rb_right)) by { assumption(); }
                                                                have separate(memory(parent->rb_left), memory(xid->rb_right)) by { assumption(); }
                                                                step();
                                                                transport(at(before_rotation_parent_changes, gparent->rb_right == at(before_uncle_pointer_changes, tmp)), gparent->rb_right == at(before_uncle_pointer_changes, tmp)) using {
                                                                    at(before_rotation_parent_changes, gparent->rb_right == at(before_uncle_pointer_changes, tmp));
                                                                    separate(memory(gparent->rb_right), memory(gparent->__rb_parent_color));
                                                                    separate(memory(gparent->rb_right), memory(parent->__rb_parent_color));
                                                                    separate(memory(gparent->rb_right), memory(xid->rb_left));
                                                                    separate(memory(gparent->rb_right), memory(xid->rb_right));
                                                                };
                                                                transport(at(before_rotation_parent_changes, parent->rb_left == node), parent->rb_left == node) using {
                                                                    at(before_rotation_parent_changes, parent->rb_left == node);
                                                                    separate(memory(parent->rb_left), memory(gparent->__rb_parent_color));
                                                                    separate(memory(parent->rb_left), memory(parent->__rb_parent_color));
                                                                    separate(memory(parent->rb_left), memory(xid->rb_left));
                                                                    separate(memory(parent->rb_left), memory(xid->rb_right));
                                                                };
                                                                let uu = fold(ctx_at(parent, root), { model: Context::Left(xid, xgp, xcol, xsib, xup) }, { sibling: xs, up: xu });
                                                                have uu.model == uup by { rewrite(uup == Context::Left(xid, xgp, xcol, xsib, xup)); normalize(); }
                                                            },
                                                            Context::Right(xid, xgp, xcol, xsib, xup) => {
                                                                have ctx_node_is(Context::Right(xid, xgp, xcol, xsib, xup), ugp) == 1 by {
                                                                    rewrite(Context::Right(xid, xgp, xcol, xsib, xup) == uu.model);
                                                                    rewrite(uu.model == uup);
                                                                    assumption();
                                                                }
                                                                have ugp == xid by {
                                                                    apply(ctx_node_is_right_identity(xid, xgp, xcol, xsib, xup, ugp)) using {
                                                                        ctx_node_is(Context::Right(xid, xgp, xcol, xsib, xup), ugp) == 1;
                                                                    };
                                                                    assumption();
                                                                }
                                                                let { sibling: xs, up: xu } = unfold(uu);
                                                                have separate(memory(gparent->rb_right), memory(xid->rb_left)) by { assumption(); }
                                                                have separate(memory(parent->rb_left), memory(xid->rb_left)) by { assumption(); }
                                                                have separate(memory(gparent->rb_right), memory(xid->rb_right)) by { assumption(); }
                                                                have separate(memory(parent->rb_left), memory(xid->rb_right)) by { assumption(); }
                                                                mark before_upper_child_change;
                                                                have at(before_upper_child_change, ((xid->__rb_parent_color & ~3) as (struct rb_node *)) == xgp) by { assumption(); }
                                                                have separate(memory(xid->__rb_parent_color), memory(gparent->__rb_parent_color)) by { assumption(); }
                                                                have separate(memory(xid->__rb_parent_color), memory(parent->__rb_parent_color)) by { assumption(); }
                                                                have separate(memory(xid->__rb_parent_color), memory(xid->rb_left)) by { assumption(); }
                                                                have separate(memory(xid->__rb_parent_color), memory(xid->rb_right)) by { assumption(); }
                                                                match xsib ensuring {
                                                                    owns xs: rb_at(xid->rb_left);
                                                                    fact xs.model == xsib;
                                                                    fact gparent->rb_right == at(before_uncle_pointer_changes, tmp);
                                                                    fact parent->rb_left == node;
                                                                    fact ((xid->__rb_parent_color & ~3) as (struct rb_node *)) == xgp;
                                                                } {
                                                                    RbTree::Empty => {
                                                                        unfold(xs);
                                                                        step();
                                                                        transport(at(before_rotation_parent_changes, gparent->rb_right == at(before_uncle_pointer_changes, tmp)), gparent->rb_right == at(before_uncle_pointer_changes, tmp)) using {
                                                                            at(before_rotation_parent_changes, gparent->rb_right == at(before_uncle_pointer_changes, tmp));
                                                                            separate(memory(gparent->rb_right), memory(gparent->__rb_parent_color));
                                                                            separate(memory(gparent->rb_right), memory(parent->__rb_parent_color));
                                                                                    separate(memory(gparent->rb_right), memory(xid->rb_left));
                                                                            separate(memory(gparent->rb_right), memory(xid->rb_right));
                                                                        };
                                                                        transport(at(before_rotation_parent_changes, parent->rb_left == node), parent->rb_left == node) using {
                                                                            at(before_rotation_parent_changes, parent->rb_left == node);
                                                                            separate(memory(parent->rb_left), memory(gparent->__rb_parent_color));
                                                                            separate(memory(parent->rb_left), memory(parent->__rb_parent_color));
                                                                            separate(memory(parent->rb_left), memory(xid->rb_left));
                                                                            separate(memory(parent->rb_left), memory(xid->rb_right));
                                                                        };
                                                                        let xs = fold(rb_at(0), { model: xsib });
                                                                        transport(at(before_upper_child_change, ((xid->__rb_parent_color & ~3) as (struct rb_node *)) == xgp), ((xid->__rb_parent_color & ~3) as (struct rb_node *)) == xgp);
                                                                    },
                                                                    RbTree::Node(yid, yp, ycol, yl, yr) => {
                                                                        let { left: yl_at, right: yr_at } = unfold(xs);
                                                                        step();
                                                                        transport(at(before_rotation_parent_changes, gparent->rb_right == at(before_uncle_pointer_changes, tmp)), gparent->rb_right == at(before_uncle_pointer_changes, tmp)) using {
                                                                            at(before_rotation_parent_changes, gparent->rb_right == at(before_uncle_pointer_changes, tmp));
                                                                            separate(memory(gparent->rb_right), memory(gparent->__rb_parent_color));
                                                                            separate(memory(gparent->rb_right), memory(parent->__rb_parent_color));
                                                                                    separate(memory(gparent->rb_right), memory(xid->rb_left));
                                                                            separate(memory(gparent->rb_right), memory(xid->rb_right));
                                                                        };
                                                                        transport(at(before_rotation_parent_changes, parent->rb_left == node), parent->rb_left == node) using {
                                                                            at(before_rotation_parent_changes, parent->rb_left == node);
                                                                            separate(memory(parent->rb_left), memory(gparent->__rb_parent_color));
                                                                            separate(memory(parent->rb_left), memory(parent->__rb_parent_color));
                                                                            separate(memory(parent->rb_left), memory(xid->rb_left));
                                                                            separate(memory(parent->rb_left), memory(xid->rb_right));
                                                                        };
                                                                        let xs = fold(rb_at(yid), { model: xsib }, { left: yl_at, right: yr_at });
                                                                        transport(at(before_upper_child_change, ((xid->__rb_parent_color & ~3) as (struct rb_node *)) == xgp), ((xid->__rb_parent_color & ~3) as (struct rb_node *)) == xgp);
                                                                    },
                                                                }
                                                                let uu = fold(ctx_at(parent, root), { model: Context::Right(xid, xgp, xcol, xsib, xup) }, { sibling: xs, up: xu });
                                                                have uu.model == uup by { rewrite(uup == Context::Right(xid, xgp, xcol, xsib, xup)); normalize(); }
                                                            },
                                                        }
                                                            have rb_parent_is(rb_reparent(csib, gparent), gparent) == 1 by {
                                                                apply(rb_reparent_parent_is(csib, gparent));
                                                                assumption();
                                                            }
                                                            let gn = fold(rb_at(gparent), { model: RbTree::Node(gparent, cid, Color::Red, rb_reparent(csib, gparent), usib) }, { left: sn, right: un });
                                                            have rb_parent_is(RbTree::Node(gparent, cid, Color::Red, rb_reparent(csib, gparent), usib), cid) == 1 by {
                                                                unfold(rb_parent_is(RbTree::Node(gparent, cid, Color::Red, rb_reparent(csib, gparent), usib), cid));
                                                            }
                                                            have (parent->__rb_parent_color & 1) == color_bit(Color::Black) by {
                                                                unfold(color_bit(Color::Black));
                                                                solve();
                                                            }
                                                        let c = fold(ctx_at(node, root), { model: Context::Left(cid, ugp, Color::Black, RbTree::Node(gparent, cid, Color::Red, rb_reparent(csib, gparent), usib), uup) }, { sibling: gn, up: uu });
                                                        have rb_inorder(plug(c.model, t.model)) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                                            rewrite(c.model == Context::Left(cid, ugp, Color::Black, RbTree::Node(gparent, cid, Color::Red, rb_reparent(csib, gparent), usib), uup));
                                                            rewrite(t.model == RbTree::Node(nid, cid, Color::Red, nleft, nright));
                                                            rewrite(rb_inorder(plug(Context::Left(cid, ugp, Color::Black, RbTree::Node(gparent, cid, Color::Red, rb_reparent(csib, gparent), usib), uup), RbTree::Node(nid, cid, Color::Red, nleft, nright))) == rb_inorder(plug(Context::Left(cid, gparent, Color::Red, csib, Context::Left(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright))));
                                                            assumption();
                                                        }
                                                        have rb_tree_parent_consistent(plug(c.model, t.model)) == 1 by {
                                                            unfold(rb_tree_parent_consistent(plug(c.model, t.model)));
                                                        }
                                                        step();
                                                        step();
                                                    } else {
                                                        match us.model {
                                                            RbTree::Node(unid, unp, uncolor, unl, unr) => {
                                                                let { left: ul, right: ur } = unfold(us);
                                                                step();
                                                                match uncolor {
                                                                    Color::Red => {
                                                                        have (tmp->__rb_parent_color & 1) == 0 by {
                                                                            rewrite((tmp->__rb_parent_color & 1) == color_bit(uncolor));
                                                                            rewrite(uncolor == Color::Red);
                                                                            unfold(color_bit(Color::Red));
                                                                            solve();
                                                                        }
                                                                        have ucolor == Color::Black by {
                                                                            apply(ctx_rb_left_red_focus_black(uid, ugp, ucolor, usib, uup, black_height(t.model))) using {
                                                                                ctx_rb(Context::Left(uid, ugp, ucolor, usib, uup), black_height(t.model), Color::Red) == 1;
                                                                            };
                                                                            assumption();
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(unid, unp, uncolor, unl, unr), gparent) == 1 by {
                                                                            rewrite(RbTree::Node(unid, unp, uncolor, unl, unr) == usib);
                                                                            assumption();
                                                                        }
                                                                        have unp == gparent by {
                                                                            apply(rb_parent_is_node_parent(unid, unp, uncolor, unl, unr, gparent)) using {
                                                                                rb_parent_is(RbTree::Node(unid, unp, uncolor, unl, unr), gparent) == 1;
                                                                            };
                                                                            assumption();
                                                                        }
                                                                        have usib == RbTree::Node(unid, gparent, Color::Red, unl, unr) by {
                                                                            rewrite(usib == RbTree::Node(unid, unp, uncolor, unl, unr));
                                                                            rewrite(unp == gparent);
                                                                            rewrite(uncolor == Color::Red);
                                                                            normalize();
                                                                        }
                                                                        have cup == Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup) by {
                                                                            rewrite(cup == Context::Left(uid, ugp, ucolor, usib, uup));
                                                                            rewrite(usib == RbTree::Node(unid, gparent, Color::Red, unl, unr));
                                                                            rewrite(ucolor == Color::Black);
                                                                            rewrite(uid == gparent);
                                                                            normalize();
                                                                        }
                                                                        have almost_rb_insert(RbTree::Node(cid, cgp, Color::Red, t.model, csib)) == 1 by {
                                                                            apply(ctx_insert_cursor_left_parent(cid, cgp, t.model, csib, cup)) using {
                                                                                is_rb(t.model) == 1;
                                                                                ctx_rb(Context::Left(cid, cgp, Color::Red, csib, cup), black_height(t.model), Color::Black) == 1;
                                                                            };
                                                                            assumption();
                                                                        }
                                                                        have almost_rb_insert(RbTree::Node(cid, gparent, Color::Red, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib)) == 1 by {
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                                            rewrite(gparent == cgp);
                                                                            assumption();
                                                                        }
                                                                        apply(ctx_insert_case1_left_step(ugp, gparent, cid, unid, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib, unl, unr, uup)) using {
                                                                            almost_rb_insert(RbTree::Node(cid, gparent, Color::Red, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib)) == 1;
                                                                            ctx_rb(Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), black_height(RbTree::Node(nid, nparent, ncolor, nleft, nright)), Color::Red) == 1;
                                                                        };
                                                                        have rb_inorder(plug(Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), RbTree::Node(cid, gparent, Color::Red, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib))) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                                                            apply(plug_left_frame(cid, cgp, ccolor, csib, cup, t.model));
                                                                            rewrite(Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup) == cup);
                                                                            rewrite(gparent == cgp);
                                                                            rewrite(Color::Red == ccolor);
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                                            rewrite(plug(cup, RbTree::Node(cid, cgp, ccolor, t.model, csib))
                                                                                == plug(Context::Left(cid, cgp, ccolor, csib, cup), t.model));
                                                                            assumption();
                                                                        }
                                                                        have rb_parent_consistent(plug(Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), RbTree::Node(cid, gparent, Color::Red, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib)), 0) == 1 by {
                                                                            apply(plug_left_frame(cid, cgp, ccolor, csib, cup, t.model));
                                                                            rewrite(Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup) == cup);
                                                                            rewrite(gparent == cgp);
                                                                            rewrite(Color::Red == ccolor);
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                                            rewrite(plug(cup, RbTree::Node(cid, cgp, ccolor, t.model, csib))
                                                                                == plug(Context::Left(cid, cgp, ccolor, csib, cup), t.model));
                                                                            assumption();
                                                                        }
                                                                        have rb_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib), RbTree::Node(unid, gparent, Color::Black, unl, unr))), 0) == 1 by {
                                                                            rewrite(rb_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib), RbTree::Node(unid, gparent, Color::Black, unl, unr))), 0)
                                                                                == rb_parent_consistent(plug(Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), RbTree::Node(cid, gparent, Color::Red, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib)), 0));
                                                                            assumption();
                                                                        }
                                                                        have rb_tree_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib), RbTree::Node(unid, gparent, Color::Black, unl, unr)))) == 1 by {
                                                                            unfold(rb_tree_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib), RbTree::Node(unid, gparent, Color::Black, unl, unr)))));
                                                                        }
                                                                        have rb_color_bit(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib), RbTree::Node(unid, gparent, Color::Black, unl, unr))) == 0 by {
                                                                            unfold(rb_color_bit(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib), RbTree::Node(unid, gparent, Color::Black, unl, unr))));
                                                                            unfold(color_bit(Color::Red));
                                                                            normalize();
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(nid, nparent, ncolor, nleft, nright), parent) == 1 by {
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                                            assumption();
                                                                        }
                                                                        have color_bit(Color::Black) == 1 by {
                                                                            unfold(color_bit(Color::Black));
                                                                            normalize();
                                                                        }
                                                                        have color_bit(Color::Red) == 0 by {
                                                                            unfold(color_bit(Color::Red));
                                                                            normalize();
                                                                        }
                                                                        mark before_recolor_tags;
                                                                        have at(before_recolor_tags, gparent->rb_left == parent) by { assumption(); }
                                                                        have at(before_recolor_tags, separate(memory(gparent->rb_left), memory(gparent->__rb_parent_color))) by { assumption(); }
                                                                        have at(before_recolor_tags, separate(memory(gparent->rb_left), memory(parent->__rb_parent_color))) by { assumption(); }
                                                                        have at(before_recolor_tags, separate(memory(gparent->rb_left), memory(tmp->__rb_parent_color))) by { assumption(); }
                                                                        have at(before_recolor_tags, gparent->rb_right == tmp) by { assumption(); }
                                                                        have at(before_recolor_tags, separate(memory(gparent->rb_right), memory(gparent->__rb_parent_color))) by { assumption(); }
                                                                        have at(before_recolor_tags, separate(memory(gparent->rb_right), memory(parent->__rb_parent_color))) by { assumption(); }
                                                                        have at(before_recolor_tags, separate(memory(gparent->rb_right), memory(tmp->__rb_parent_color))) by { assumption(); }
                                                                        step();
                                                                        step();
                                                                        step();
                                                                        let un = fold(rb_at(tmp), { model: RbTree::Node(unid, gparent, Color::Black, unl, unr) }, { left: ul, right: ur });
                                                                        let pn = fold(rb_at(parent), { model: RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib) }, { left: t, right: cs });
                                                                        step();
                                                                        step();
                                                                        step();
                                                                        have rb_parent_is(RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib), gparent) == 1 by {
                                                                            unfold(rb_parent_is(RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib), gparent));
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(unid, gparent, Color::Black, unl, unr), gparent) == 1 by {
                                                                            unfold(rb_parent_is(RbTree::Node(unid, gparent, Color::Black, unl, unr), gparent));
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib), RbTree::Node(unid, gparent, Color::Black, unl, unr)), ugp) == 1 by {
                                                                            unfold(rb_parent_is(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib), RbTree::Node(unid, gparent, Color::Black, unl, unr)), ugp));
                                                                        }
                                                                        transport(at(before_recolor_tags, gparent->rb_left == parent), gparent->rb_left == at(before_recolor_tags, parent)) using {
                                                                            at(before_recolor_tags, gparent->rb_left == parent);
                                                                            at(before_recolor_tags, separate(memory(gparent->rb_left), memory(gparent->__rb_parent_color)));
                                                                            at(before_recolor_tags, separate(memory(gparent->rb_left), memory(parent->__rb_parent_color)));
                                                                            at(before_recolor_tags, separate(memory(gparent->rb_left), memory(tmp->__rb_parent_color)));
                                                                        };
                                                                        transport(at(before_recolor_tags, gparent->rb_right == tmp), gparent->rb_right == at(before_recolor_tags, tmp)) using {
                                                                            at(before_recolor_tags, gparent->rb_right == tmp);
                                                                            at(before_recolor_tags, separate(memory(gparent->rb_right), memory(gparent->__rb_parent_color)));
                                                                            at(before_recolor_tags, separate(memory(gparent->rb_right), memory(parent->__rb_parent_color)));
                                                                            at(before_recolor_tags, separate(memory(gparent->rb_right), memory(tmp->__rb_parent_color)));
                                                                        };
                                                                        let gn = fold(rb_at(gparent), { model: RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib), RbTree::Node(unid, gparent, Color::Black, unl, unr)) }, { left: pn, right: un });
                                                                    },
                                                                    Color::Black => {
                                                                        have rb_root_black(usib) == 1 by {
                                                                            rewrite(usib == RbTree::Node(unid, unp, uncolor, unl, unr));
                                                                            rewrite(uncolor == Color::Black);
                                                                            apply(rb_root_black_black_node(unid, unp, unl, unr));
                                                                            assumption();
                                                                        }
                                                                        contradiction(rb_root_black(usib) == 1);
                                                                    },
                                                                }
                                                            },
                                                            RbTree::Empty => {
                                                                have rb_root_black(usib) == 1 by {
                                                                    rewrite(usib == RbTree::Empty);
                                                                    unfold(rb_root_black(RbTree::Empty)); normalize();
                                                                }
                                                                contradiction(rb_root_black(usib) == 1);
                                                            },
                                                        }
                                                    }
                                                },
                                                Context::Right(uid, ugp, ucolor, usib, uup) => {
                                                    have ctx_node_is(Context::Right(uid, ugp, ucolor,
                                                        usib, uup), cgp) == 1 by {
                                                        rewrite(Context::Right(uid, ugp, ucolor, usib, uup)
                                                            == cu.model);
                                                        rewrite(cu.model == cup);
                                                        assumption();
                                                    }
                                                    have cgp == uid by {
                                                        apply(ctx_node_is_right_identity(uid, ugp, ucolor,
                                                            usib, uup, cgp)) using {
                                                            ctx_node_is(Context::Right(uid, ugp, ucolor,
                                                                usib, uup), cgp) == 1;
                                                        };
                                                        assumption();
                                                    }
                                                    have ctx_rb(Context::Right(uid, ugp, ucolor, usib, uup), black_height(t.model), Color::Red) == 1 by {
                                                        rewrite(Context::Right(uid, ugp, ucolor, usib, uup) == cu.model);
                                                        assumption();
                                                    }
                                                    let { sibling: us, up: uu } = unfold(cu);
                                                    step();
                                                    if rb_root_black(usib) == 1 {
                                                        match us.model ensuring {
                                                            owns un: rb_at(tmp);
                                                            fact un.model == usib;
                                                            fact gparent->rb_left == tmp;
                                                        } {
                                                            RbTree::Node(unid, unp, uncolor, unl, unr) => {
                                                                let { left: ul, right: ur } = unfold(us);
                                                                step();
                                                                step();
                                                                have rb_root_black(RbTree::Node(unid, unp, uncolor, unl, unr)) == 1 by {
                                                                    rewrite(RbTree::Node(unid, unp, uncolor, unl, unr) == usib);
                                                                    assumption();
                                                                }
                                                                have color_bit(uncolor) == 1 by {
                                                                    apply(rb_root_black_node_color_bit(unid, unp, uncolor, unl, unr)) using {
                                                                        rb_root_black(RbTree::Node(unid, unp, uncolor, unl, unr)) == 1;
                                                                    };
                                                                    assumption();
                                                                }
                                                                have uncolor == Color::Black by {
                                                                    apply(color_bit_one_is_black(uncolor)) using {
                                                                        color_bit(uncolor) == 1;
                                                                    };
                                                                    assumption();
                                                                }
                                                                step();
                                                                have ucolor == Color::Black by {
                                                                    apply(ctx_rb_right_red_focus_black(uid, ugp, ucolor, usib, uup, black_height(t.model))) using {
                                                                        ctx_rb(Context::Right(uid, ugp, ucolor, usib, uup), black_height(t.model), Color::Red) == 1;
                                                                    };
                                                                    assumption();
                                                                }
                                                                have rb_parent_is(RbTree::Node(unid, unp, uncolor, unl, unr), gparent) == 1 by {
                                                                    rewrite(RbTree::Node(unid, unp, uncolor, unl, unr) == usib);
                                                                    assumption();
                                                                }
                                                                have unp == gparent by {
                                                                    apply(rb_parent_is_node_parent(unid, unp, uncolor, unl, unr, gparent)) using {
                                                                        rb_parent_is(RbTree::Node(unid, unp, uncolor, unl, unr), gparent) == 1;
                                                                    };
                                                                    assumption();
                                                                }
                                                                have usib == RbTree::Node(unid, gparent, Color::Black, unl, unr) by {
                                                                    rewrite(usib == RbTree::Node(unid, unp, uncolor, unl, unr));
                                                                    rewrite(unp == gparent);
                                                                    rewrite(uncolor == Color::Black);
                                                                    normalize();
                                                                }
                                                                have (tmp->__rb_parent_color & 1) == color_bit(Color::Black) by {
                                                                    rewrite(Color::Black == uncolor);
                                                                    assumption();
                                                                }
                                                                have gparent->rb_left == tmp by { assumption(); }
                                                                let un = fold(rb_at(tmp), { model: RbTree::Node(unid, gparent, Color::Black, unl, unr) }, { left: ul, right: ur });
                                                                have un.model == usib by {
                                                                    rewrite(usib == RbTree::Node(unid, gparent, Color::Black, unl, unr));
                                                                    normalize();
                                                                }
                                                            },
                                                            RbTree::Empty => {
                                                                unfold(us);
                                                                step();
                                                                step();
                                                                step();
                                                                have ucolor == Color::Black by {
                                                                    apply(ctx_rb_right_red_focus_black(uid, ugp, ucolor, usib, uup, black_height(t.model))) using {
                                                                        ctx_rb(Context::Right(uid, ugp, ucolor, usib, uup), black_height(t.model), Color::Red) == 1;
                                                                    };
                                                                    assumption();
                                                                }
                                                                have gparent->rb_left == tmp by { assumption(); }
                                                                let un = fold(rb_at(tmp), { model: RbTree::Empty });
                                                                have un.model == usib by {
                                                                    rewrite(usib == RbTree::Empty);
                                                                    normalize();
                                                                }
                                                            },
                                                        }
                                                        mark triangle_uncle_pointer;
                                                        have at(triangle_uncle_pointer, gparent->rb_left == tmp) by { assumption(); }
                                                        have cup == Context::Right(gparent, ugp, Color::Black, usib, uup) by {
                                                            rewrite(cup == Context::Right(uid, ugp, ucolor, usib, uup));
                                                            rewrite(ucolor == Color::Black);
                                                            rewrite(uid == gparent);
                                                            normalize();
                                                        }
                                                        have rb_parent_is(RbTree::Node(nid, nparent, ncolor, nleft, nright), parent) == 1 by {
                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                            assumption();
                                                        }
                                                        have nparent == cid by {
                                                            apply(rb_parent_is_node_parent(nid, nparent, ncolor, nleft, nright, parent)) using {
                                                                rb_parent_is(RbTree::Node(nid, nparent, ncolor, nleft, nright), parent) == 1;
                                                            };
                                                            solve();
                                                        }
                                                        have color_bit(ncolor) == 0 by {
                                                            unfold(rb_color_bit(RbTree::Node(nid, nparent, ncolor, nleft, nright)));
                                                            rewrite(color_bit(ncolor) == rb_color_bit(RbTree::Node(nid, nparent, ncolor, nleft, nright)));
                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                            assumption();
                                                        }
                                                        have ncolor == Color::Red by {
                                                            apply(color_bit_zero_is_red(ncolor)) using {
                                                                color_bit(ncolor) == 0;
                                                            };
                                                            assumption();
                                                        }
                                                        have t.model == RbTree::Node(nid, cid, Color::Red, nleft, nright) by {
                                                            rewrite(t.model == RbTree::Node(nid, nparent, ncolor, nleft, nright));
                                                            rewrite(nparent == cid);
                                                            rewrite(ncolor == Color::Red);
                                                            normalize();
                                                        }
                                                        have is_rb(RbTree::Node(nid, cid, Color::Red, nleft, nright)) == 1 by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright) == t.model);
                                                            assumption();
                                                        }
                                                        have ctx_rb(Context::Left(cid, gparent, Color::Red, csib, Context::Right(gparent, ugp, Color::Black, usib, uup)), black_height(RbTree::Node(nid, cid, Color::Red, nleft, nright)), Color::Black) == 1 by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright) == t.model);
                                                            rewrite(Context::Right(gparent, ugp, Color::Black, usib, uup) == cup);
                                                            rewrite(gparent == cgp);
                                                            rewrite(Color::Red == ccolor);
                                                            assumption();
                                                        }
                                                        have rb_parent_consistent(plug(Context::Left(cid, gparent, Color::Red, csib, Context::Right(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright)), 0) == 1 by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright) == t.model);
                                                            rewrite(Context::Right(gparent, ugp, Color::Black, usib, uup) == cup);
                                                            rewrite(gparent == cgp);
                                                            rewrite(Color::Red == ccolor);
                                                            assumption();
                                                        }
                                                        have rb_inorder(plug(Context::Left(cid, gparent, Color::Red, csib, Context::Right(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright))) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright) == t.model);
                                                            rewrite(Context::Right(gparent, ugp, Color::Black, usib, uup) == cup);
                                                            rewrite(gparent == cgp);
                                                            rewrite(Color::Red == ccolor);
                                                            assumption();
                                                        }
                                                        apply(ctx_insert_case2_right_exit_step(ugp, gparent, cid, nid, usib, nleft, nright, csib, uup)) using {
                                                            is_rb(RbTree::Node(nid, cid, Color::Red, nleft, nright)) == 1;
                                                            rb_root_black(usib) == 1;
                                                            ctx_rb(Context::Left(cid, gparent, Color::Red, csib, Context::Right(gparent, ugp, Color::Black, usib, uup)), black_height(RbTree::Node(nid, cid, Color::Red, nleft, nright)), Color::Black) == 1;
                                                            rb_parent_consistent(plug(Context::Left(cid, gparent, Color::Red, csib, Context::Right(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright)), 0) == 1;
                                                        };
                                                        let { left: nl_at, right: nr_at } = unfold(t);
                                                        have (node->__rb_parent_color & 1) == color_bit(Color::Red) by {
                                                            rewrite(Color::Red == ncolor);
                                                            assumption();
                                                        }
                                                        step();
                                                        step();
                                                        step();
                                                        have separate(memory(parent->rb_left), memory(node->rb_right)) by { assumption(); }
                                                        mark before_inner_parent_right;
                                                        have at(before_inner_parent_right, parent->rb_right == parent->rb_right) by { normalize(); }
                                                        have separate(memory(parent->rb_right), memory(parent->rb_left)) by { assumption(); }
                                                        have separate(memory(parent->rb_right), memory(node->rb_right)) by { assumption(); }
                                                        mark before_inner_node_left;
                                                        have at(before_inner_node_left, node->rb_left == node->rb_left) by { normalize(); }
                                                        have separate(memory(node->rb_left), memory(parent->rb_left)) by { assumption(); }
                                                        have separate(memory(node->rb_left), memory(node->rb_right)) by { assumption(); }
                                                        mark before_triangle_grandparent_tag;
                                                        have at(before_triangle_grandparent_tag, (gparent->__rb_parent_color & 1) == color_bit(ucolor)) by { assumption(); }
                                                        have at(before_triangle_grandparent_tag, ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp) by { assumption(); }
                                                        have separate(memory(gparent->__rb_parent_color), memory(parent->rb_left)) by { assumption(); }
                                                        have separate(memory(gparent->__rb_parent_color), memory(node->rb_right)) by { assumption(); }
                                                        have at(before_triangle_grandparent_tag, gparent->rb_left == at(triangle_uncle_pointer, tmp)) by { assumption(); }
                                                        have separate(memory(gparent->rb_left), memory(parent->rb_left)) by { assumption(); }
                                                        have separate(memory(gparent->rb_left), memory(node->rb_right)) by { assumption(); }
                                                        match nr_at.model ensuring {
                                                            owns bn: rb_at(tmp);
                                                            fact bn.model == rb_reparent(nright, cid);
                                                            fact node->rb_right == parent;
                                                            fact gparent->rb_left == at(triangle_uncle_pointer, tmp);
                                                            fact (gparent->__rb_parent_color & 1) == color_bit(ucolor);
                                                            fact ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp;
                                                            fact parent->rb_left == tmp;
                                                            fact node->rb_left == at(before_inner_node_left, node->rb_left);
                                                            fact parent->rb_right == at(before_inner_parent_right, parent->rb_right);
                                                        } {
                                                            RbTree::Empty => {
                                                                unfold(nr_at);
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                have rb_reparent(nright, cid) == RbTree::Empty by {
                                                                    rewrite(nright == RbTree::Empty);
                                                                    unfold(rb_reparent(RbTree::Empty, cid)); normalize();
                                                                }
                                                                transport(at(before_inner_parent_right, parent->rb_right == parent->rb_right), parent->rb_right == at(before_inner_parent_right, parent->rb_right)) using {
                                                                    at(before_inner_parent_right, parent->rb_right == parent->rb_right);
                                                                    separate(memory(parent->rb_right), memory(parent->rb_left));
                                                                    separate(memory(parent->rb_right), memory(node->rb_right));
                                                                };
                                                                transport(at(before_inner_node_left, node->rb_left == node->rb_left), node->rb_left == at(before_inner_node_left, node->rb_left)) using {
                                                                    at(before_inner_node_left, node->rb_left == node->rb_left);
                                                                    separate(memory(node->rb_left), memory(parent->rb_left));
                                                                    separate(memory(node->rb_left), memory(node->rb_right));
                                                                };
                                                                have parent->rb_left == tmp by { assumption(); }
                                                                transport(at(before_triangle_grandparent_tag, (gparent->__rb_parent_color & 1) == color_bit(ucolor)), (gparent->__rb_parent_color & 1) == color_bit(ucolor)) using {
                                                                    at(before_triangle_grandparent_tag, (gparent->__rb_parent_color & 1) == color_bit(ucolor));
                                                                    separate(memory(gparent->__rb_parent_color), memory(parent->rb_left));
                                                                    separate(memory(gparent->__rb_parent_color), memory(node->rb_right));
                                                                };
                                                                transport(at(before_triangle_grandparent_tag, ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp), ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp) using {
                                                                    at(before_triangle_grandparent_tag, ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp);
                                                                    separate(memory(gparent->__rb_parent_color), memory(parent->rb_left));
                                                                    separate(memory(gparent->__rb_parent_color), memory(node->rb_right));
                                                                };
                                                                transport(at(before_triangle_grandparent_tag, gparent->rb_left == at(triangle_uncle_pointer, tmp)), gparent->rb_left == at(triangle_uncle_pointer, tmp)) using {
                                                                    at(before_triangle_grandparent_tag, gparent->rb_left == at(triangle_uncle_pointer, tmp));
                                                                    separate(memory(gparent->rb_left), memory(parent->rb_left));
                                                                    separate(memory(gparent->rb_left), memory(node->rb_right));
                                                                };
                                                                have node->rb_right == parent by { normalize(); }
                                                                let bn = fold(rb_at(tmp), { model: RbTree::Empty });
                                                                have bn.model == rb_reparent(nright, cid) by {
                                                                    rewrite(rb_reparent(nright, cid) == RbTree::Empty);
                                                                    solve();
                                                                }
                                                            },
                                                            RbTree::Node(bx, bp, bcol, bl, br) => {
                                                                let { left: bl_at, right: br_at } = unfold(nr_at);
                                                                step();
                                                                mark before_inner_child_links;
                                                                have separate(memory(node->rb_right), memory(tmp->__rb_parent_color)) by { assumption(); }
                                                                have separate(memory(gparent->rb_left), memory(tmp->__rb_parent_color)) by { assumption(); }
                                                                have separate(memory(gparent->__rb_parent_color), memory(tmp->__rb_parent_color)) by { assumption(); }
                                                                have separate(memory(node->rb_left), memory(tmp->__rb_parent_color)) by { assumption(); }
                                                                have separate(memory(parent->rb_right), memory(tmp->__rb_parent_color)) by { assumption(); }
                                                                have separate(memory(parent->rb_left), memory(tmp->__rb_parent_color)) by { assumption(); }
                                                                have at(before_inner_child_links, tmp->rb_left == bx->rb_left) by { assumption(); }
                                                                have at(before_inner_child_links, separate(memory(tmp->rb_left), memory(parent->rb_left))) by { assumption(); }
                                                                have at(before_inner_child_links, separate(memory(tmp->rb_left), memory(node->rb_right))) by { assumption(); }
                                                                have at(before_inner_child_links, separate(memory(tmp->rb_left), memory(tmp->__rb_parent_color))) by { assumption(); }
                                                                have at(before_inner_child_links, tmp->rb_right == bx->rb_right) by { assumption(); }
                                                                have at(before_inner_child_links, separate(memory(tmp->rb_right), memory(parent->rb_left))) by { assumption(); }
                                                                have at(before_inner_child_links, separate(memory(tmp->rb_right), memory(node->rb_right))) by { assumption(); }
                                                                have at(before_inner_child_links, separate(memory(tmp->rb_right), memory(tmp->__rb_parent_color))) by { assumption(); }
                                                                have rb_root_black(RbTree::Node(bx, bp, bcol, bl, br)) == 1 by {
                                                                    rewrite(RbTree::Node(bx, bp, bcol, bl, br) == nright);
                                                                    assumption();
                                                                }
                                                                have color_bit(bcol) == 1 by {
                                                                    apply(rb_root_black_node_color_bit(bx, bp, bcol, bl, br)) using {
                                                                        rb_root_black(RbTree::Node(bx, bp, bcol, bl, br)) == 1;
                                                                    };
                                                                    assumption();
                                                                }
                                                                have rb_reparent(nright, cid) == RbTree::Node(bx, cid, bcol, bl, br) by {
                                                                    rewrite(nright == RbTree::Node(bx, bp, bcol, bl, br));
                                                                    unfold(rb_reparent(RbTree::Node(bx, bp, bcol, bl, br), cid)); normalize();
                                                                }
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                transport(at(before_inner_child_links, tmp->rb_left == bx->rb_left), tmp->rb_left == at(before_inner_child_links, bx->rb_left)) using {
                                                                    at(before_inner_child_links, tmp->rb_left == bx->rb_left);
                                                                    at(before_inner_child_links, separate(memory(tmp->rb_left), memory(parent->rb_left)));
                                                                    at(before_inner_child_links, separate(memory(tmp->rb_left), memory(node->rb_right)));
                                                                    at(before_inner_child_links, separate(memory(tmp->rb_left), memory(tmp->__rb_parent_color)));
                                                                };
                                                                transport(at(before_inner_child_links, tmp->rb_right == bx->rb_right), tmp->rb_right == at(before_inner_child_links, bx->rb_right)) using {
                                                                    at(before_inner_child_links, tmp->rb_right == bx->rb_right);
                                                                    at(before_inner_child_links, separate(memory(tmp->rb_right), memory(parent->rb_left)));
                                                                    at(before_inner_child_links, separate(memory(tmp->rb_right), memory(node->rb_right)));
                                                                    at(before_inner_child_links, separate(memory(tmp->rb_right), memory(tmp->__rb_parent_color)));
                                                                };
                                                                transport(at(before_inner_parent_right, parent->rb_right == parent->rb_right), parent->rb_right == at(before_inner_parent_right, parent->rb_right)) using {
                                                                    at(before_inner_parent_right, parent->rb_right == parent->rb_right);
                                                                    separate(memory(parent->rb_right), memory(parent->rb_left));
                                                                    separate(memory(parent->rb_right), memory(node->rb_right));
                                                                    separate(memory(parent->rb_right), memory(tmp->__rb_parent_color));
                                                                };
                                                                transport(at(before_inner_node_left, node->rb_left == node->rb_left), node->rb_left == at(before_inner_node_left, node->rb_left)) using {
                                                                    at(before_inner_node_left, node->rb_left == node->rb_left);
                                                                    separate(memory(node->rb_left), memory(parent->rb_left));
                                                                    separate(memory(node->rb_left), memory(node->rb_right));
                                                                    separate(memory(node->rb_left), memory(tmp->__rb_parent_color));
                                                                };
                                                                have parent->rb_left == tmp by { assumption(); }
                                                                transport(at(before_triangle_grandparent_tag, (gparent->__rb_parent_color & 1) == color_bit(ucolor)), (gparent->__rb_parent_color & 1) == color_bit(ucolor)) using {
                                                                    at(before_triangle_grandparent_tag, (gparent->__rb_parent_color & 1) == color_bit(ucolor));
                                                                    separate(memory(gparent->__rb_parent_color), memory(parent->rb_left));
                                                                    separate(memory(gparent->__rb_parent_color), memory(node->rb_right));
                                                                    separate(memory(gparent->__rb_parent_color), memory(tmp->__rb_parent_color));
                                                                };
                                                                transport(at(before_triangle_grandparent_tag, ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp), ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp) using {
                                                                    at(before_triangle_grandparent_tag, ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp);
                                                                    separate(memory(gparent->__rb_parent_color), memory(parent->rb_left));
                                                                    separate(memory(gparent->__rb_parent_color), memory(node->rb_right));
                                                                    separate(memory(gparent->__rb_parent_color), memory(tmp->__rb_parent_color));
                                                                };
                                                                transport(at(before_triangle_grandparent_tag, gparent->rb_left == at(triangle_uncle_pointer, tmp)), gparent->rb_left == at(triangle_uncle_pointer, tmp)) using {
                                                                    at(before_triangle_grandparent_tag, gparent->rb_left == at(triangle_uncle_pointer, tmp));
                                                                    separate(memory(gparent->rb_left), memory(parent->rb_left));
                                                                    separate(memory(gparent->rb_left), memory(node->rb_right));
                                                                    separate(memory(gparent->rb_left), memory(tmp->__rb_parent_color));
                                                                };
                                                                have node->rb_right == parent by { normalize(); }
                                                                let bn = fold(rb_at(tmp), { model: RbTree::Node(bx, cid, bcol, bl, br) }, { left: bl_at, right: br_at });
                                                                have bn.model == rb_reparent(nright, cid) by {
                                                                    rewrite(rb_reparent(nright, cid) == RbTree::Node(bx, cid, bcol, bl, br));
                                                                    solve();
                                                                }
                                                            },
                                                        }
                                                        mark before_inner_parent_color;
                                                        have at(before_inner_parent_color, node->rb_right == parent) by { assumption(); }
                                                        have separate(memory(node->rb_right), memory(parent->__rb_parent_color)) by { assumption(); }
                                                        have at(before_inner_parent_color, gparent->rb_left == at(triangle_uncle_pointer, tmp)) by { assumption(); }
                                                        have separate(memory(gparent->rb_left), memory(parent->__rb_parent_color)) by { assumption(); }
                                                        have at(before_inner_parent_color, (gparent->__rb_parent_color & 1) == color_bit(ucolor)) by { assumption(); }
                                                        have at(before_inner_parent_color, ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp) by { assumption(); }
                                                        have separate(memory(gparent->__rb_parent_color), memory(parent->__rb_parent_color)) by { assumption(); }
                                                        have at(before_inner_parent_color, parent->rb_left == tmp) by { assumption(); }
                                                        have at(before_inner_parent_color, node->rb_left == at(before_inner_node_left, node->rb_left)) by { assumption(); }
                                                        have separate(memory(node->rb_left), memory(parent->__rb_parent_color)) by { assumption(); }
                                                        have at(before_inner_parent_color, parent->rb_right == at(before_inner_parent_right, parent->rb_right)) by { assumption(); }
                                                        have separate(memory(parent->rb_right), memory(parent->__rb_parent_color)) by { assumption(); }
                                                        have separate(memory(parent->rb_left), memory(parent->__rb_parent_color)) by { assumption(); }
                                                        step();
                                                        transport(at(before_inner_parent_color, parent->rb_left == tmp), parent->rb_left == tmp) using {
                                                            at(before_inner_parent_color, parent->rb_left == tmp);
                                                            separate(memory(parent->rb_left), memory(parent->__rb_parent_color));
                                                        };
                                                        transport(at(before_inner_parent_color, parent->rb_right == at(before_inner_parent_right, parent->rb_right)), parent->rb_right == at(before_inner_parent_right, parent->rb_right)) using {
                                                            at(before_inner_parent_color, parent->rb_right == at(before_inner_parent_right, parent->rb_right));
                                                            separate(memory(parent->rb_right), memory(parent->__rb_parent_color));
                                                        };
                                                        transport(at(before_inner_parent_color, node->rb_left == at(before_inner_node_left, node->rb_left)), node->rb_left == at(before_inner_node_left, node->rb_left)) using {
                                                            at(before_inner_parent_color, node->rb_left == at(before_inner_node_left, node->rb_left));
                                                            separate(memory(node->rb_left), memory(parent->__rb_parent_color));
                                                        };
                                                        transport(at(before_inner_parent_color, (gparent->__rb_parent_color & 1) == color_bit(ucolor)), (gparent->__rb_parent_color & 1) == color_bit(ucolor)) using {
                                                            at(before_inner_parent_color, (gparent->__rb_parent_color & 1) == color_bit(ucolor));
                                                            separate(memory(gparent->__rb_parent_color), memory(parent->__rb_parent_color));
                                                        };
                                                        transport(at(before_inner_parent_color, ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp), ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp) using {
                                                            at(before_inner_parent_color, ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp);
                                                            separate(memory(gparent->__rb_parent_color), memory(parent->__rb_parent_color));
                                                        };
                                                        transport(at(before_inner_parent_color, gparent->rb_left == at(triangle_uncle_pointer, tmp)), gparent->rb_left == at(triangle_uncle_pointer, tmp)) using {
                                                            at(before_inner_parent_color, gparent->rb_left == at(triangle_uncle_pointer, tmp));
                                                            separate(memory(gparent->rb_left), memory(parent->__rb_parent_color));
                                                        };
                                                        transport(at(before_inner_parent_color, node->rb_right == parent), node->rb_right == parent) using {
                                                            at(before_inner_parent_color, node->rb_right == parent);
                                                            separate(memory(node->rb_right), memory(parent->__rb_parent_color));
                                                        };
                                                        have rb_parent_is(rb_reparent(nright, cid), cid) == 1 by {
                                                            apply(rb_reparent_parent_is(nright, cid));
                                                            assumption();
                                                        }
                                                        let pn = fold(rb_at(parent), { model: RbTree::Node(cid, nid, Color::Red, rb_reparent(nright, cid), csib) }, { left: bn, right: cs });
                                                        mark triangle_old_parent;
                                                        have at(triangle_old_parent, node->rb_right == parent) by { assumption(); }
                                                        step();
                                                        step();
                                                        mark before_outer_grandparent_tag;
                                                        have at(before_outer_grandparent_tag, (gparent->__rb_parent_color & 1) == color_bit(ucolor)) by { assumption(); }
                                                        have at(before_outer_grandparent_tag, ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp) by { assumption(); }
                                                        have separate(memory(gparent->__rb_parent_color), memory(gparent->rb_right)) by { assumption(); }
                                                        have separate(memory(gparent->__rb_parent_color), memory(parent->rb_left)) by { assumption(); }
                                                        have at(before_outer_grandparent_tag, gparent->rb_left == at(triangle_uncle_pointer, tmp)) by { assumption(); }
                                                        have separate(memory(gparent->rb_left), memory(gparent->rb_right)) by { assumption(); }
                                                        have separate(memory(gparent->rb_left), memory(parent->rb_left)) by { assumption(); }
                                                        have at(before_outer_grandparent_tag, node->rb_right == at(triangle_old_parent, parent)) by { assumption(); }
                                                        have separate(memory(node->rb_right), memory(gparent->rb_right)) by { assumption(); }
                                                        have separate(memory(node->rb_right), memory(parent->rb_left)) by { assumption(); }
                                                        match nl_at.model ensuring {
                                                            owns rn: rb_at(tmp);
                                                            fact rn.model == rb_reparent(nleft, gparent);
                                                            fact node->rb_right == at(triangle_old_parent, parent);
                                                            fact gparent->rb_left == at(triangle_uncle_pointer, tmp);
                                                            fact (gparent->__rb_parent_color & 1) == color_bit(ucolor);
                                                            fact ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp;
                                                        } {
                                                            RbTree::Empty => {
                                                                unfold(nl_at);
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                have rb_reparent(nleft, gparent) == RbTree::Empty by {
                                                                    rewrite(nleft == RbTree::Empty);
                                                                    unfold(rb_reparent(RbTree::Empty, gparent)); normalize();
                                                                }
                                                                transport(at(before_outer_grandparent_tag, (gparent->__rb_parent_color & 1) == color_bit(ucolor)), (gparent->__rb_parent_color & 1) == color_bit(ucolor)) using {
                                                                    at(before_outer_grandparent_tag, (gparent->__rb_parent_color & 1) == color_bit(ucolor));
                                                                    separate(memory(gparent->__rb_parent_color), memory(gparent->rb_right));
                                                                    separate(memory(gparent->__rb_parent_color), memory(parent->rb_left));
                                                                };
                                                                transport(at(before_outer_grandparent_tag, ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp), ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp) using {
                                                                    at(before_outer_grandparent_tag, ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp);
                                                                    separate(memory(gparent->__rb_parent_color), memory(gparent->rb_right));
                                                                    separate(memory(gparent->__rb_parent_color), memory(parent->rb_left));
                                                                };
                                                                transport(at(before_outer_grandparent_tag, gparent->rb_left == at(triangle_uncle_pointer, tmp)), gparent->rb_left == at(triangle_uncle_pointer, tmp)) using {
                                                                    at(before_outer_grandparent_tag, gparent->rb_left == at(triangle_uncle_pointer, tmp));
                                                                    separate(memory(gparent->rb_left), memory(gparent->rb_right));
                                                                    separate(memory(gparent->rb_left), memory(parent->rb_left));
                                                                };
                                                                transport(at(before_outer_grandparent_tag, node->rb_right == at(triangle_old_parent, parent)), node->rb_right == at(triangle_old_parent, parent)) using {
                                                                    at(before_outer_grandparent_tag, node->rb_right == at(triangle_old_parent, parent));
                                                                    separate(memory(node->rb_right), memory(gparent->rb_right));
                                                                    separate(memory(node->rb_right), memory(parent->rb_left));
                                                                };
                                                                let rn = fold(rb_at(tmp), { model: RbTree::Empty });
                                                                have rn.model == rb_reparent(nleft, gparent) by {
                                                                    rewrite(rb_reparent(nleft, gparent) == RbTree::Empty);
                                                                    solve();
                                                                }
                                                            },
                                                            RbTree::Node(rx, rp, rcol, rl, rr) => {
                                                                let { left: rl_at, right: rr_at } = unfold(nl_at);
                                                                step();
                                                                have separate(memory(node->rb_right), memory(tmp->__rb_parent_color)) by { assumption(); }
                                                                have separate(memory(gparent->rb_left), memory(tmp->__rb_parent_color)) by { assumption(); }
                                                                have separate(memory(gparent->__rb_parent_color), memory(tmp->__rb_parent_color)) by { assumption(); }
                                                                have rb_root_black(RbTree::Node(rx, rp, rcol, rl, rr)) == 1 by {
                                                                    rewrite(RbTree::Node(rx, rp, rcol, rl, rr) == nleft);
                                                                    assumption();
                                                                }
                                                                have color_bit(rcol) == 1 by {
                                                                    apply(rb_root_black_node_color_bit(rx, rp, rcol, rl, rr)) using {
                                                                        rb_root_black(RbTree::Node(rx, rp, rcol, rl, rr)) == 1;
                                                                    };
                                                                    assumption();
                                                                }
                                                                have rb_reparent(nleft, gparent) == RbTree::Node(rx, gparent, rcol, rl, rr) by {
                                                                    rewrite(nleft == RbTree::Node(rx, rp, rcol, rl, rr));
                                                                    unfold(rb_reparent(RbTree::Node(rx, rp, rcol, rl, rr), gparent)); normalize();
                                                                }
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                transport(at(before_outer_grandparent_tag, (gparent->__rb_parent_color & 1) == color_bit(ucolor)), (gparent->__rb_parent_color & 1) == color_bit(ucolor)) using {
                                                                    at(before_outer_grandparent_tag, (gparent->__rb_parent_color & 1) == color_bit(ucolor));
                                                                    separate(memory(gparent->__rb_parent_color), memory(gparent->rb_right));
                                                                    separate(memory(gparent->__rb_parent_color), memory(parent->rb_left));
                                                                    separate(memory(gparent->__rb_parent_color), memory(tmp->__rb_parent_color));
                                                                };
                                                                transport(at(before_outer_grandparent_tag, ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp), ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp) using {
                                                                    at(before_outer_grandparent_tag, ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp);
                                                                    separate(memory(gparent->__rb_parent_color), memory(gparent->rb_right));
                                                                    separate(memory(gparent->__rb_parent_color), memory(parent->rb_left));
                                                                    separate(memory(gparent->__rb_parent_color), memory(tmp->__rb_parent_color));
                                                                };
                                                                transport(at(before_outer_grandparent_tag, gparent->rb_left == at(triangle_uncle_pointer, tmp)), gparent->rb_left == at(triangle_uncle_pointer, tmp)) using {
                                                                    at(before_outer_grandparent_tag, gparent->rb_left == at(triangle_uncle_pointer, tmp));
                                                                    separate(memory(gparent->rb_left), memory(gparent->rb_right));
                                                                    separate(memory(gparent->rb_left), memory(parent->rb_left));
                                                                    separate(memory(gparent->rb_left), memory(tmp->__rb_parent_color));
                                                                };
                                                                transport(at(before_outer_grandparent_tag, node->rb_right == at(triangle_old_parent, parent)), node->rb_right == at(triangle_old_parent, parent)) using {
                                                                    at(before_outer_grandparent_tag, node->rb_right == at(triangle_old_parent, parent));
                                                                    separate(memory(node->rb_right), memory(gparent->rb_right));
                                                                    separate(memory(node->rb_right), memory(parent->rb_left));
                                                                    separate(memory(node->rb_right), memory(tmp->__rb_parent_color));
                                                                };
                                                                let rn = fold(rb_at(tmp), { model: RbTree::Node(rx, gparent, rcol, rl, rr) }, { left: rl_at, right: rr_at });
                                                                have rn.model == rb_reparent(nleft, gparent) by {
                                                                    rewrite(rb_reparent(nleft, gparent) == RbTree::Node(rx, gparent, rcol, rl, rr));
                                                                    solve();
                                                                }
                                                            },
                                                        }
                                                        have (gparent->__rb_parent_color & 1) == 1 by {
                                                            rewrite((gparent->__rb_parent_color & 1) == color_bit(ucolor));
                                                            rewrite(ucolor == Color::Black);
                                                            unfold(color_bit(Color::Black));
                                                            solve();
                                                        }
                                                        mark before_triangle_parent_changes;
                                                        have at(before_triangle_parent_changes, gparent->rb_left == at(triangle_uncle_pointer, tmp)) by { assumption(); }
                                                        have separate(memory(gparent->rb_left), memory(gparent->__rb_parent_color)) by { assumption(); }
                                                        have separate(memory(gparent->rb_left), memory(parent->__rb_parent_color)) by { assumption(); }
                                                        have at(before_triangle_parent_changes, node->rb_right == at(triangle_old_parent, parent)) by { assumption(); }
                                                        have separate(memory(node->rb_right), memory(gparent->__rb_parent_color)) by { assumption(); }
                                                        have separate(memory(node->rb_right), memory(parent->__rb_parent_color)) by { assumption(); }
                                                        match uu.model ensuring {
                                                            owns c: ctx_at(node, root);
                                                            fact c.model == uup;
                                                            fact node->rb_right == at(triangle_old_parent, parent);
                                                            fact gparent->rb_left == at(triangle_uncle_pointer, tmp);
                                                        } {
                                                            Context::Top => {
                                                                have ctx_node_is(Context::Top, ugp) == 1 by {
                                                                    rewrite(Context::Top == uu.model);
                                                                    rewrite(uu.model == uup);
                                                                    assumption();
                                                                }
                                                                have ugp == 0 by {
                                                                    apply(ctx_node_is_top_null(ugp)) using {
                                                                        ctx_node_is(Context::Top, ugp) == 1;
                                                                    };
                                                                    assumption();
                                                                }
                                                                unfold(uu);
                                                                have separate(memory(gparent->rb_left), memory(root->rb_node)) by { assumption(); }
                                                                have separate(memory(node->rb_right), memory(root->rb_node)) by { assumption(); }
                                                                step();
                                                                transport(at(before_triangle_parent_changes, gparent->rb_left == at(triangle_uncle_pointer, tmp)), gparent->rb_left == at(triangle_uncle_pointer, tmp)) using {
                                                                    at(before_triangle_parent_changes, gparent->rb_left == at(triangle_uncle_pointer, tmp));
                                                                    separate(memory(gparent->rb_left), memory(gparent->__rb_parent_color));
                                                                    separate(memory(gparent->rb_left), memory(parent->__rb_parent_color));
                                                                    separate(memory(gparent->rb_left), memory(root->rb_node));
                                                                };
                                                                transport(at(before_triangle_parent_changes, node->rb_right == at(triangle_old_parent, parent)), node->rb_right == at(triangle_old_parent, parent)) using {
                                                                    at(before_triangle_parent_changes, node->rb_right == at(triangle_old_parent, parent));
                                                                    separate(memory(node->rb_right), memory(gparent->__rb_parent_color));
                                                                    separate(memory(node->rb_right), memory(parent->__rb_parent_color));
                                                                    separate(memory(node->rb_right), memory(root->rb_node));
                                                                };
                                                                let c = fold(ctx_at(node, root), { model: Context::Top });
                                                                have c.model == uup by { rewrite(uup == Context::Top); normalize(); }
                                                            },
                                                            Context::Left(xid, xgp, xcol, xsib, xup) => {
                                                                have ctx_node_is(Context::Left(xid, xgp, xcol, xsib, xup), ugp) == 1 by {
                                                                    rewrite(Context::Left(xid, xgp, xcol, xsib, xup) == uu.model);
                                                                    rewrite(uu.model == uup);
                                                                    assumption();
                                                                }
                                                                have ugp == xid by {
                                                                    apply(ctx_node_is_left_identity(xid, xgp, xcol, xsib, xup, ugp)) using {
                                                                        ctx_node_is(Context::Left(xid, xgp, xcol, xsib, xup), ugp) == 1;
                                                                    };
                                                                    assumption();
                                                                }
                                                                let { sibling: xs, up: xu } = unfold(uu);
                                                                have separate(memory(gparent->rb_left), memory(xid->rb_left)) by { assumption(); }
                                                                have separate(memory(node->rb_right), memory(xid->rb_left)) by { assumption(); }
                                                                have separate(memory(gparent->rb_left), memory(xid->rb_right)) by { assumption(); }
                                                                have separate(memory(node->rb_right), memory(xid->rb_right)) by { assumption(); }
                                                                step();
                                                                transport(at(before_triangle_parent_changes, gparent->rb_left == at(triangle_uncle_pointer, tmp)), gparent->rb_left == at(triangle_uncle_pointer, tmp)) using {
                                                                    at(before_triangle_parent_changes, gparent->rb_left == at(triangle_uncle_pointer, tmp));
                                                                    separate(memory(gparent->rb_left), memory(gparent->__rb_parent_color));
                                                                    separate(memory(gparent->rb_left), memory(parent->__rb_parent_color));
                                                                    separate(memory(gparent->rb_left), memory(xid->rb_left));
                                                                    separate(memory(gparent->rb_left), memory(xid->rb_right));
                                                                };
                                                                transport(at(before_triangle_parent_changes, node->rb_right == at(triangle_old_parent, parent)), node->rb_right == at(triangle_old_parent, parent)) using {
                                                                    at(before_triangle_parent_changes, node->rb_right == at(triangle_old_parent, parent));
                                                                    separate(memory(node->rb_right), memory(gparent->__rb_parent_color));
                                                                    separate(memory(node->rb_right), memory(parent->__rb_parent_color));
                                                                    separate(memory(node->rb_right), memory(xid->rb_left));
                                                                    separate(memory(node->rb_right), memory(xid->rb_right));
                                                                };
                                                                let c = fold(ctx_at(node, root), { model: Context::Left(xid, xgp, xcol, xsib, xup) }, { sibling: xs, up: xu });
                                                                have c.model == uup by { rewrite(uup == Context::Left(xid, xgp, xcol, xsib, xup)); normalize(); }
                                                            },
                                                            Context::Right(xid, xgp, xcol, xsib, xup) => {
                                                                have ctx_node_is(Context::Right(xid, xgp, xcol, xsib, xup), ugp) == 1 by {
                                                                    rewrite(Context::Right(xid, xgp, xcol, xsib, xup) == uu.model);
                                                                    rewrite(uu.model == uup);
                                                                    assumption();
                                                                }
                                                                have ugp == xid by {
                                                                    apply(ctx_node_is_right_identity(xid, xgp, xcol, xsib, xup, ugp)) using {
                                                                        ctx_node_is(Context::Right(xid, xgp, xcol, xsib, xup), ugp) == 1;
                                                                    };
                                                                    assumption();
                                                                }
                                                                let { sibling: xs, up: xu } = unfold(uu);
                                                                have separate(memory(gparent->rb_left), memory(xid->rb_left)) by { assumption(); }
                                                                have separate(memory(node->rb_right), memory(xid->rb_left)) by { assumption(); }
                                                                have separate(memory(gparent->rb_left), memory(xid->rb_right)) by { assumption(); }
                                                                have separate(memory(node->rb_right), memory(xid->rb_right)) by { assumption(); }
                                                                mark before_triangle_upper_link;
                                                                have at(before_triangle_upper_link, ((xid->__rb_parent_color & ~3) as (struct rb_node *)) == xgp) by { assumption(); }
                                                                have separate(memory(xid->__rb_parent_color), memory(gparent->__rb_parent_color)) by { assumption(); }
                                                                have separate(memory(xid->__rb_parent_color), memory(parent->__rb_parent_color)) by { assumption(); }
                                                                have separate(memory(xid->__rb_parent_color), memory(xid->rb_left)) by { assumption(); }
                                                                have separate(memory(xid->__rb_parent_color), memory(xid->rb_right)) by { assumption(); }
                                                                match xsib ensuring {
                                                                    owns xs: rb_at(xid->rb_left);
                                                                    fact xs.model == xsib;
                                                                    fact node->rb_right == at(triangle_old_parent, parent);
                                                                    fact gparent->rb_left == at(triangle_uncle_pointer, tmp);
                                                                    fact ((xid->__rb_parent_color & ~3) as (struct rb_node *)) == xgp;
                                                                } {
                                                                    RbTree::Empty => {
                                                                        unfold(xs);
                                                                        step();
                                                                        transport(at(before_triangle_upper_link, ((xid->__rb_parent_color & ~3) as (struct rb_node *)) == xgp), ((xid->__rb_parent_color & ~3) as (struct rb_node *)) == xgp) using {
                                                                            at(before_triangle_upper_link, ((xid->__rb_parent_color & ~3) as (struct rb_node *)) == xgp);
                                                                            separate(memory(xid->__rb_parent_color), memory(gparent->__rb_parent_color));
                                                                            separate(memory(xid->__rb_parent_color), memory(parent->__rb_parent_color));
                                                                            separate(memory(xid->__rb_parent_color), memory(xid->rb_left));
                                                                            separate(memory(xid->__rb_parent_color), memory(xid->rb_right));
                                                                        };
                                                                        transport(at(before_triangle_parent_changes, gparent->rb_left == at(triangle_uncle_pointer, tmp)), gparent->rb_left == at(triangle_uncle_pointer, tmp)) using {
                                                                            at(before_triangle_parent_changes, gparent->rb_left == at(triangle_uncle_pointer, tmp));
                                                                            separate(memory(gparent->rb_left), memory(gparent->__rb_parent_color));
                                                                            separate(memory(gparent->rb_left), memory(parent->__rb_parent_color));
                                                                            separate(memory(gparent->rb_left), memory(xid->rb_left));
                                                                            separate(memory(gparent->rb_left), memory(xid->rb_right));
                                                                        };
                                                                        transport(at(before_triangle_parent_changes, node->rb_right == at(triangle_old_parent, parent)), node->rb_right == at(triangle_old_parent, parent)) using {
                                                                            at(before_triangle_parent_changes, node->rb_right == at(triangle_old_parent, parent));
                                                                            separate(memory(node->rb_right), memory(gparent->__rb_parent_color));
                                                                            separate(memory(node->rb_right), memory(parent->__rb_parent_color));
                                                                            separate(memory(node->rb_right), memory(xid->rb_left));
                                                                            separate(memory(node->rb_right), memory(xid->rb_right));
                                                                        };
                                                                        let xs = fold(rb_at(0), { model: xsib });
                                                                    },
                                                                    RbTree::Node(yid, yp, ycol, yl, yr) => {
                                                                        let { left: yl_at, right: yr_at } = unfold(xs);
                                                                        step();
                                                                        transport(at(before_triangle_upper_link, ((xid->__rb_parent_color & ~3) as (struct rb_node *)) == xgp), ((xid->__rb_parent_color & ~3) as (struct rb_node *)) == xgp) using {
                                                                            at(before_triangle_upper_link, ((xid->__rb_parent_color & ~3) as (struct rb_node *)) == xgp);
                                                                            separate(memory(xid->__rb_parent_color), memory(gparent->__rb_parent_color));
                                                                            separate(memory(xid->__rb_parent_color), memory(parent->__rb_parent_color));
                                                                            separate(memory(xid->__rb_parent_color), memory(xid->rb_left));
                                                                            separate(memory(xid->__rb_parent_color), memory(xid->rb_right));
                                                                        };
                                                                        transport(at(before_triangle_parent_changes, gparent->rb_left == at(triangle_uncle_pointer, tmp)), gparent->rb_left == at(triangle_uncle_pointer, tmp)) using {
                                                                            at(before_triangle_parent_changes, gparent->rb_left == at(triangle_uncle_pointer, tmp));
                                                                            separate(memory(gparent->rb_left), memory(gparent->__rb_parent_color));
                                                                            separate(memory(gparent->rb_left), memory(parent->__rb_parent_color));
                                                                            separate(memory(gparent->rb_left), memory(xid->rb_left));
                                                                            separate(memory(gparent->rb_left), memory(xid->rb_right));
                                                                        };
                                                                        transport(at(before_triangle_parent_changes, node->rb_right == at(triangle_old_parent, parent)), node->rb_right == at(triangle_old_parent, parent)) using {
                                                                            at(before_triangle_parent_changes, node->rb_right == at(triangle_old_parent, parent));
                                                                            separate(memory(node->rb_right), memory(gparent->__rb_parent_color));
                                                                            separate(memory(node->rb_right), memory(parent->__rb_parent_color));
                                                                            separate(memory(node->rb_right), memory(xid->rb_left));
                                                                            separate(memory(node->rb_right), memory(xid->rb_right));
                                                                        };
                                                                        let xs = fold(rb_at(yid), { model: xsib }, { left: yl_at, right: yr_at });
                                                                    },
                                                                }
                                                                let c = fold(ctx_at(node, root), { model: Context::Right(xid, xgp, xcol, xsib, xup) }, { sibling: xs, up: xu });
                                                                have c.model == uup by { rewrite(uup == Context::Right(xid, xgp, xcol, xsib, xup)); normalize(); }
                                                            },
                                                        }
                                                            have rb_parent_is(rb_reparent(nleft, gparent), gparent) == 1 by {
                                                                apply(rb_reparent_parent_is(nleft, gparent));
                                                                assumption();
                                                            }
                                                            let gn = fold(rb_at(gparent), { model: RbTree::Node(gparent, nid, Color::Red, usib, rb_reparent(nleft, gparent)) }, { left: un, right: rn });
                                                            have rb_parent_is(RbTree::Node(cid, nid, Color::Red, rb_reparent(nright, cid), csib), nid) == 1 by {
                                                                unfold(rb_parent_is(RbTree::Node(cid, nid, Color::Red, rb_reparent(nright, cid), csib), nid));
                                                            }
                                                            have rb_parent_is(RbTree::Node(gparent, nid, Color::Red, usib, rb_reparent(nleft, gparent)), nid) == 1 by {
                                                                unfold(rb_parent_is(RbTree::Node(gparent, nid, Color::Red, usib, rb_reparent(nleft, gparent)), nid));
                                                            }
                                                            have (node->__rb_parent_color & 1) == color_bit(Color::Black) by {
                                                                unfold(color_bit(Color::Black));
                                                                solve();
                                                            }
                                                            let t = fold(rb_at(node), { model: RbTree::Node(nid, ugp, Color::Black, RbTree::Node(gparent, nid, Color::Red, usib, rb_reparent(nleft, gparent)), RbTree::Node(cid, nid, Color::Red, rb_reparent(nright, cid), csib)) }, { left: gn, right: pn });
                                                            have rb_inorder(plug(c.model, t.model)) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                                                rewrite(c.model == uup);
                                                                rewrite(t.model == RbTree::Node(nid, ugp, Color::Black, RbTree::Node(gparent, nid, Color::Red, usib, rb_reparent(nleft, gparent)), RbTree::Node(cid, nid, Color::Red, rb_reparent(nright, cid), csib)));
                                                                rewrite(rb_inorder(plug(uup, RbTree::Node(nid, ugp, Color::Black, RbTree::Node(gparent, nid, Color::Red, usib, rb_reparent(nleft, gparent)), RbTree::Node(cid, nid, Color::Red, rb_reparent(nright, cid), csib)))) == rb_inorder(plug(Context::Left(cid, gparent, Color::Red, csib, Context::Right(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright))));
                                                                assumption();
                                                            }
                                                            have is_rb_root(plug(c.model, t.model)) == 1 by {
                                                                rewrite(c.model == uup);
                                                                rewrite(t.model == RbTree::Node(nid, ugp, Color::Black, RbTree::Node(gparent, nid, Color::Red, usib, rb_reparent(nleft, gparent)), RbTree::Node(cid, nid, Color::Red, rb_reparent(nright, cid), csib)));
                                                                assumption();
                                                            }
                                                            have rb_parent_consistent(plug(c.model, t.model), 0) == 1 by {
                                                                rewrite(c.model == uup);
                                                                rewrite(t.model == RbTree::Node(nid, ugp, Color::Black, RbTree::Node(gparent, nid, Color::Red, usib, rb_reparent(nleft, gparent)), RbTree::Node(cid, nid, Color::Red, rb_reparent(nright, cid), csib)));
                                                                assumption();
                                                            }
                                                        have rb_tree_parent_consistent(plug(c.model, t.model)) == 1 by {
                                                            unfold(rb_tree_parent_consistent(plug(c.model, t.model)));
                                                        }
                                                        step();
                                                        step();
                                                    } else {
                                                        match us.model {
                                                            RbTree::Node(unid, unp, uncolor, unl, unr) => {
                                                                let { left: ul, right: ur } = unfold(us);
                                                                step();
                                                                step();
                                                                match uncolor {
                                                                    Color::Red => {
                                                                        have (tmp->__rb_parent_color & 1) == 0 by {
                                                                            rewrite((tmp->__rb_parent_color & 1) == color_bit(uncolor));
                                                                            rewrite(uncolor == Color::Red);
                                                                            unfold(color_bit(Color::Red));
                                                                            solve();
                                                                        }
                                                                        have ucolor == Color::Black by {
                                                                            apply(ctx_rb_right_red_focus_black(uid, ugp, ucolor, usib, uup, black_height(t.model))) using {
                                                                                ctx_rb(Context::Right(uid, ugp, ucolor, usib, uup), black_height(t.model), Color::Red) == 1;
                                                                            };
                                                                            assumption();
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(unid, unp, uncolor, unl, unr), gparent) == 1 by {
                                                                            rewrite(RbTree::Node(unid, unp, uncolor, unl, unr) == usib);
                                                                            assumption();
                                                                        }
                                                                        have unp == gparent by {
                                                                            apply(rb_parent_is_node_parent(unid, unp, uncolor, unl, unr, gparent)) using {
                                                                                rb_parent_is(RbTree::Node(unid, unp, uncolor, unl, unr), gparent) == 1;
                                                                            };
                                                                            assumption();
                                                                        }
                                                                        have usib == RbTree::Node(unid, gparent, Color::Red, unl, unr) by {
                                                                            rewrite(usib == RbTree::Node(unid, unp, uncolor, unl, unr));
                                                                            rewrite(unp == gparent);
                                                                            rewrite(uncolor == Color::Red);
                                                                            normalize();
                                                                        }
                                                                        have cup == Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup) by {
                                                                            rewrite(cup == Context::Right(uid, ugp, ucolor, usib, uup));
                                                                            rewrite(usib == RbTree::Node(unid, gparent, Color::Red, unl, unr));
                                                                            rewrite(ucolor == Color::Black);
                                                                            rewrite(uid == gparent);
                                                                            normalize();
                                                                        }
                                                                        have almost_rb_insert(RbTree::Node(cid, cgp, Color::Red, t.model, csib)) == 1 by {
                                                                            apply(ctx_insert_cursor_left_parent(cid, cgp, t.model, csib, cup)) using {
                                                                                is_rb(t.model) == 1;
                                                                                ctx_rb(Context::Left(cid, cgp, Color::Red, csib, cup), black_height(t.model), Color::Black) == 1;
                                                                            };
                                                                            assumption();
                                                                        }
                                                                        have almost_rb_insert(RbTree::Node(cid, gparent, Color::Red, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib)) == 1 by {
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                                            rewrite(gparent == cgp);
                                                                            assumption();
                                                                        }
                                                                        apply(ctx_insert_case1_right_step(ugp, gparent, cid, unid, unl, unr, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib, uup)) using {
                                                                            almost_rb_insert(RbTree::Node(cid, gparent, Color::Red, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib)) == 1;
                                                                            ctx_rb(Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), black_height(RbTree::Node(nid, nparent, ncolor, nleft, nright)), Color::Red) == 1;
                                                                        };
                                                                        have rb_inorder(plug(Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), RbTree::Node(cid, gparent, Color::Red, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib))) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                                                            apply(plug_left_frame(cid, cgp, ccolor, csib, cup, t.model));
                                                                            rewrite(Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup) == cup);
                                                                            rewrite(gparent == cgp);
                                                                            rewrite(Color::Red == ccolor);
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                                            rewrite(plug(cup, RbTree::Node(cid, cgp, ccolor, t.model, csib))
                                                                                == plug(Context::Left(cid, cgp, ccolor, csib, cup), t.model));
                                                                            assumption();
                                                                        }
                                                                        have rb_parent_consistent(plug(Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), RbTree::Node(cid, gparent, Color::Red, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib)), 0) == 1 by {
                                                                            apply(plug_left_frame(cid, cgp, ccolor, csib, cup, t.model));
                                                                            rewrite(Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup) == cup);
                                                                            rewrite(gparent == cgp);
                                                                            rewrite(Color::Red == ccolor);
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                                            rewrite(plug(cup, RbTree::Node(cid, cgp, ccolor, t.model, csib))
                                                                                == plug(Context::Left(cid, cgp, ccolor, csib, cup), t.model));
                                                                            assumption();
                                                                        }
                                                                        have rb_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib))), 0) == 1 by {
                                                                            rewrite(rb_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib))), 0)
                                                                                == rb_parent_consistent(plug(Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), RbTree::Node(cid, gparent, Color::Red, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib)), 0));
                                                                            assumption();
                                                                        }
                                                                        have rb_tree_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib)))) == 1 by {
                                                                            unfold(rb_tree_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib)))));
                                                                        }
                                                                        have rb_color_bit(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib))) == 0 by {
                                                                            unfold(rb_color_bit(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib))));
                                                                            unfold(color_bit(Color::Red));
                                                                            normalize();
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(nid, nparent, ncolor, nleft, nright), parent) == 1 by {
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                                            assumption();
                                                                        }
                                                                        have color_bit(Color::Black) == 1 by {
                                                                            unfold(color_bit(Color::Black));
                                                                            normalize();
                                                                        }
                                                                        have color_bit(Color::Red) == 0 by {
                                                                            unfold(color_bit(Color::Red));
                                                                            normalize();
                                                                        }
                                                                        mark before_recolor_tags_2;
                                                                        have at(before_recolor_tags_2, gparent->rb_left == tmp) by { assumption(); }
                                                                        have at(before_recolor_tags_2, separate(memory(gparent->rb_left), memory(gparent->__rb_parent_color))) by { assumption(); }
                                                                        have at(before_recolor_tags_2, separate(memory(gparent->rb_left), memory(parent->__rb_parent_color))) by { assumption(); }
                                                                        have at(before_recolor_tags_2, separate(memory(gparent->rb_left), memory(tmp->__rb_parent_color))) by { assumption(); }
                                                                        have at(before_recolor_tags_2, gparent->rb_right == parent) by { assumption(); }
                                                                        have at(before_recolor_tags_2, separate(memory(gparent->rb_right), memory(gparent->__rb_parent_color))) by { assumption(); }
                                                                        have at(before_recolor_tags_2, separate(memory(gparent->rb_right), memory(parent->__rb_parent_color))) by { assumption(); }
                                                                        have at(before_recolor_tags_2, separate(memory(gparent->rb_right), memory(tmp->__rb_parent_color))) by { assumption(); }
                                                                        step();
                                                                        step();
                                                                        step();
                                                                        let un = fold(rb_at(tmp), { model: RbTree::Node(unid, gparent, Color::Black, unl, unr) }, { left: ul, right: ur });
                                                                        let pn = fold(rb_at(parent), { model: RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib) }, { left: t, right: cs });
                                                                        step();
                                                                        step();
                                                                        step();
                                                                        have rb_parent_is(RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib), gparent) == 1 by {
                                                                            unfold(rb_parent_is(RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib), gparent));
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(unid, gparent, Color::Black, unl, unr), gparent) == 1 by {
                                                                            unfold(rb_parent_is(RbTree::Node(unid, gparent, Color::Black, unl, unr), gparent));
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib)), ugp) == 1 by {
                                                                            unfold(rb_parent_is(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib)), ugp));
                                                                        }
                                                                        transport(at(before_recolor_tags_2, gparent->rb_left == tmp), gparent->rb_left == at(before_recolor_tags_2, tmp)) using {
                                                                            at(before_recolor_tags_2, gparent->rb_left == tmp);
                                                                            at(before_recolor_tags_2, separate(memory(gparent->rb_left), memory(gparent->__rb_parent_color)));
                                                                            at(before_recolor_tags_2, separate(memory(gparent->rb_left), memory(parent->__rb_parent_color)));
                                                                            at(before_recolor_tags_2, separate(memory(gparent->rb_left), memory(tmp->__rb_parent_color)));
                                                                        };
                                                                        transport(at(before_recolor_tags_2, gparent->rb_right == parent), gparent->rb_right == at(before_recolor_tags_2, parent)) using {
                                                                            at(before_recolor_tags_2, gparent->rb_right == parent);
                                                                            at(before_recolor_tags_2, separate(memory(gparent->rb_right), memory(gparent->__rb_parent_color)));
                                                                            at(before_recolor_tags_2, separate(memory(gparent->rb_right), memory(parent->__rb_parent_color)));
                                                                            at(before_recolor_tags_2, separate(memory(gparent->rb_right), memory(tmp->__rb_parent_color)));
                                                                        };
                                                                        let gn = fold(rb_at(gparent), { model: RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib)) }, { left: un, right: pn });
                                                                    },
                                                                    Color::Black => {
                                                                        have rb_root_black(usib) == 1 by {
                                                                            rewrite(usib == RbTree::Node(unid, unp, uncolor, unl, unr));
                                                                            rewrite(uncolor == Color::Black);
                                                                            apply(rb_root_black_black_node(unid, unp, unl, unr));
                                                                            assumption();
                                                                        }
                                                                        contradiction(rb_root_black(usib) == 1);
                                                                    },
                                                                }
                                                            },
                                                            RbTree::Empty => {
                                                                have rb_root_black(usib) == 1 by {
                                                                    rewrite(usib == RbTree::Empty);
                                                                    unfold(rb_root_black(RbTree::Empty)); normalize();
                                                                }
                                                                contradiction(rb_root_black(usib) == 1);
                                                            },
                                                        }
                                                    }
                                                },
                                                }
                                            },
                                        }
                                    },
                                    Context::Right(cid, cgp, ccolor, csib, cup) => {
                                        have ctx_node_is(Context::Right(cid, cgp, ccolor,
                                            csib, cup), parent) == 1 by {
                                            rewrite(Context::Right(cid, cgp, ccolor, csib, cup)
                                                == c.model);
                                            assumption();
                                        }
                                        have parent == cid by {
                                            apply(ctx_node_is_right_identity(cid, cgp, ccolor,
                                                csib, cup, parent)) using {
                                                ctx_node_is(Context::Right(cid, cgp, ccolor,
                                                    csib, cup), parent) == 1;
                                            };
                                            assumption();
                                        }
                                        have ctx_rb(Context::Right(cid, cgp, ccolor, csib, cup),
                                            black_height(t.model), Color::Black) == 1 by {
                                            apply(ctx_almost_rb_insert_black_focus(c.model,
                                                black_height(t.model))) using {
                                                ctx_almost_rb_insert(c.model,
                                                    black_height(t.model)) == 1;
                                            };
                                            rewrite(Context::Right(cid, cgp, ccolor, csib, cup)
                                                == c.model);
                                            assumption();
                                        }
                                        have rb_inorder(plug(Context::Right(cid, cgp, ccolor, csib, cup), t.model))
                                            == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                            rewrite(Context::Right(cid, cgp, ccolor, csib, cup) == c.model);
                                            assumption();
                                        }
                                        have rb_parent_consistent(plug(Context::Right(cid, cgp, ccolor, csib, cup), t.model), 0) == 1 by {
                                            unfold(rb_tree_parent_consistent(plug(Context::Right(cid, cgp, ccolor, csib, cup), t.model)));
                                            rewrite(rb_parent_consistent(plug(Context::Right(cid, cgp, ccolor, csib, cup), t.model), 0)
                                                == rb_tree_parent_consistent(plug(Context::Right(cid, cgp, ccolor, csib, cup), t.model)));
                                            rewrite(Context::Right(cid, cgp, ccolor, csib, cup) == c.model);
                                            assumption();
                                        }
                                        have ctx_almost_rb_insert(Context::Right(cid, cgp, ccolor, csib, cup), black_height(t.model)) == 1 by {
                                            rewrite(Context::Right(cid, cgp, ccolor, csib, cup) == c.model);
                                            assumption();
                                        }
                                        let { sibling: cs, up: cu } = unfold(c);
                                        step();
                                        step();
                                        match ccolor {
                                            Color::Black => {
                                                have (parent->__rb_parent_color & 1) == 1 by {
                                                    rewrite((parent->__rb_parent_color & 1)
                                                        == color_bit(ccolor));
                                                    rewrite(ccolor == Color::Black);
                                                    unfold(color_bit(Color::Black));
                                                    solve();
                                                }
                                                have ctx_almost_rb_insert(Context::Right(cid, cgp, Color::Black, csib, cup), black_height(t.model)) == 1 by {
                                                    rewrite(Color::Black == ccolor);
                                                    assumption();
                                                }
                                                have ctx_rb(Context::Right(cid, cgp, Color::Black, csib, cup), black_height(t.model), rb_color(t.model)) == 1 by {
                                                    apply(ctx_black_frame_right_restores(cid, cgp, csib, cup, black_height(t.model), rb_color(t.model))) using {
                                                        ctx_almost_rb_insert(Context::Right(cid, cgp, Color::Black, csib, cup), black_height(t.model)) == 1;
                                                    };
                                                    assumption();
                                                }
                                                have is_rb_root(plug(Context::Right(cid, cgp, Color::Black, csib, cup), t.model)) == 1 by {
                                                    apply(ctx_insert_black_parent_exit(Context::Right(cid, cgp, Color::Black, csib, cup), t.model)) using {
                                                        is_rb(t.model) == 1;
                                                        ctx_rb(Context::Right(cid, cgp, Color::Black, csib, cup), black_height(t.model), rb_color(t.model)) == 1;
                                                    };
                                                    assumption();
                                                }
                                                have (parent->__rb_parent_color & 1) != 0 by {
                                                    rewrite((parent->__rb_parent_color & 1) == 1);
                                                    normalize();
                                                }
                                                step();
                                                let c = fold(ctx_at(node, root),
                                                    { model: Context::Right(cid, cgp, ccolor,
                                                        csib, cup) },
                                                    { sibling: cs, up: cu });
                                                have is_rb_root(plug(c.model, t.model)) == 1 by {
                                                    rewrite(c.model == Context::Right(cid, cgp, ccolor, csib, cup));
                                                    rewrite(ccolor == Color::Black);
                                                    assumption();
                                                }
                                                have rb_tree_parent_consistent(plug(c.model, t.model)) == 1 by {
                                                    unfold(rb_tree_parent_consistent(plug(c.model, t.model)));
                                                }
                                                step();
                                            },
                                            Color::Red => {
                                                have color_bit(ccolor) == 0 by {
                                                    rewrite(ccolor == Color::Red);
                                                    unfold(color_bit(Color::Red));
                                                    solve();
                                                }
                                                have ctx_rb(Context::Right(cid, cgp,
                                                    Color::Red, csib, cup),
                                                    black_height(t.model),
                                                    Color::Black) == 1 by {
                                                    rewrite(Color::Red == ccolor);
                                                    assumption();
                                                }
                                                have ctx_rb(cu.model,
                                                    black_height(t.model), Color::Red) == 1 by {
                                                    apply(ctx_rb_right_red_up(cid, cgp, csib, cup,
                                                        black_height(t.model),
                                                        Color::Black)) using {
                                                        ctx_rb(Context::Right(cid, cgp, Color::Red,
                                                            csib, cup), black_height(t.model),
                                                            Color::Black) == 1;
                                                    };
                                                    rewrite(cu.model == cup);
                                                    assumption();
                                                }
                                                step();
                                                step();
                                                step();
                                                have cu.model != Context::Top by {
                                                    apply(ctx_rb_red_focus_not_top(cu.model,
                                                        black_height(t.model))) using {
                                                        ctx_rb(cu.model,
                                                            black_height(t.model),
                                                            Color::Red) == 1;
                                                    };
                                                    assumption();
                                                }
                                                match cu.model {
                                                Context::Top => {
                                                    contradiction(cu.model == Context::Top);
                                                },
                                                Context::Left(uid, ugp, ucolor, usib, uup) => {
                                                    have ctx_node_is(Context::Left(uid, ugp, ucolor,
                                                        usib, uup), cgp) == 1 by {
                                                        rewrite(Context::Left(uid, ugp, ucolor, usib, uup)
                                                            == cu.model);
                                                        rewrite(cu.model == cup);
                                                        assumption();
                                                    }
                                                    have cgp == uid by {
                                                        apply(ctx_node_is_left_identity(uid, ugp, ucolor,
                                                            usib, uup, cgp)) using {
                                                            ctx_node_is(Context::Left(uid, ugp, ucolor,
                                                                usib, uup), cgp) == 1;
                                                        };
                                                        assumption();
                                                    }
                                                    have ctx_rb(Context::Left(uid, ugp, ucolor, usib, uup), black_height(t.model), Color::Red) == 1 by {
                                                        rewrite(Context::Left(uid, ugp, ucolor, usib, uup) == cu.model);
                                                        assumption();
                                                    }
                                                    let { sibling: us, up: uu } = unfold(cu);
                                                    step();
                                                    if rb_root_black(usib) == 1 {
                                                        match us.model ensuring {
                                                            owns un: rb_at(tmp);
                                                            fact un.model == usib;
                                                            fact gparent->rb_right == tmp;
                                                        } {
                                                            RbTree::Node(unid, unp, uncolor, unl, unr) => {
                                                                let { left: ul, right: ur } = unfold(us);
                                                                step();
                                                                have rb_root_black(RbTree::Node(unid, unp, uncolor, unl, unr)) == 1 by {
                                                                    rewrite(RbTree::Node(unid, unp, uncolor, unl, unr) == usib);
                                                                    assumption();
                                                                }
                                                                have color_bit(uncolor) == 1 by {
                                                                    apply(rb_root_black_node_color_bit(unid, unp, uncolor, unl, unr)) using {
                                                                        rb_root_black(RbTree::Node(unid, unp, uncolor, unl, unr)) == 1;
                                                                    };
                                                                    assumption();
                                                                }
                                                                have uncolor == Color::Black by {
                                                                    apply(color_bit_one_is_black(uncolor)) using {
                                                                        color_bit(uncolor) == 1;
                                                                    };
                                                                    assumption();
                                                                }
                                                                step();
                                                                have ucolor == Color::Black by {
                                                                    apply(ctx_rb_left_red_focus_black(uid, ugp, ucolor, usib, uup, black_height(t.model))) using {
                                                                        ctx_rb(Context::Left(uid, ugp, ucolor, usib, uup), black_height(t.model), Color::Red) == 1;
                                                                    };
                                                                    assumption();
                                                                }
                                                                have rb_parent_is(RbTree::Node(unid, unp, uncolor, unl, unr), gparent) == 1 by {
                                                                    rewrite(RbTree::Node(unid, unp, uncolor, unl, unr) == usib);
                                                                    assumption();
                                                                }
                                                                have unp == gparent by {
                                                                    apply(rb_parent_is_node_parent(unid, unp, uncolor, unl, unr, gparent)) using {
                                                                        rb_parent_is(RbTree::Node(unid, unp, uncolor, unl, unr), gparent) == 1;
                                                                    };
                                                                    assumption();
                                                                }
                                                                have usib == RbTree::Node(unid, gparent, Color::Black, unl, unr) by {
                                                                    rewrite(usib == RbTree::Node(unid, unp, uncolor, unl, unr));
                                                                    rewrite(unp == gparent);
                                                                    rewrite(uncolor == Color::Black);
                                                                    normalize();
                                                                }
                                                                have (tmp->__rb_parent_color & 1) == color_bit(Color::Black) by {
                                                                    rewrite(Color::Black == uncolor);
                                                                    assumption();
                                                                }
                                                                have gparent->rb_right == tmp by { assumption(); }
                                                                let un = fold(rb_at(tmp), { model: RbTree::Node(unid, gparent, Color::Black, unl, unr) }, { left: ul, right: ur });
                                                                have un.model == usib by {
                                                                    rewrite(usib == RbTree::Node(unid, gparent, Color::Black, unl, unr));
                                                                    normalize();
                                                                }
                                                            },
                                                            RbTree::Empty => {
                                                                unfold(us);
                                                                step();
                                                                step();
                                                                have ucolor == Color::Black by {
                                                                    apply(ctx_rb_left_red_focus_black(uid, ugp, ucolor, usib, uup, black_height(t.model))) using {
                                                                        ctx_rb(Context::Left(uid, ugp, ucolor, usib, uup), black_height(t.model), Color::Red) == 1;
                                                                    };
                                                                    assumption();
                                                                }
                                                                have gparent->rb_right == tmp by { assumption(); }
                                                                let un = fold(rb_at(tmp), { model: RbTree::Empty });
                                                                have un.model == usib by {
                                                                    rewrite(usib == RbTree::Empty);
                                                                    normalize();
                                                                }
                                                            },
                                                        }
                                                        mark triangle_uncle_pointer;
                                                        have at(triangle_uncle_pointer, gparent->rb_right == tmp) by { assumption(); }
                                                        have cup == Context::Left(gparent, ugp, Color::Black, usib, uup) by {
                                                            rewrite(cup == Context::Left(uid, ugp, ucolor, usib, uup));
                                                            rewrite(ucolor == Color::Black);
                                                            rewrite(uid == gparent);
                                                            normalize();
                                                        }
                                                        have rb_parent_is(RbTree::Node(nid, nparent, ncolor, nleft, nright), parent) == 1 by {
                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                            assumption();
                                                        }
                                                        have nparent == cid by {
                                                            apply(rb_parent_is_node_parent(nid, nparent, ncolor, nleft, nright, parent)) using {
                                                                rb_parent_is(RbTree::Node(nid, nparent, ncolor, nleft, nright), parent) == 1;
                                                            };
                                                            solve();
                                                        }
                                                        have color_bit(ncolor) == 0 by {
                                                            unfold(rb_color_bit(RbTree::Node(nid, nparent, ncolor, nleft, nright)));
                                                            rewrite(color_bit(ncolor) == rb_color_bit(RbTree::Node(nid, nparent, ncolor, nleft, nright)));
                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                            assumption();
                                                        }
                                                        have ncolor == Color::Red by {
                                                            apply(color_bit_zero_is_red(ncolor)) using {
                                                                color_bit(ncolor) == 0;
                                                            };
                                                            assumption();
                                                        }
                                                        have t.model == RbTree::Node(nid, cid, Color::Red, nleft, nright) by {
                                                            rewrite(t.model == RbTree::Node(nid, nparent, ncolor, nleft, nright));
                                                            rewrite(nparent == cid);
                                                            rewrite(ncolor == Color::Red);
                                                            normalize();
                                                        }
                                                        have is_rb(RbTree::Node(nid, cid, Color::Red, nleft, nright)) == 1 by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright) == t.model);
                                                            assumption();
                                                        }
                                                        have ctx_rb(Context::Right(cid, gparent, Color::Red, csib, Context::Left(gparent, ugp, Color::Black, usib, uup)), black_height(RbTree::Node(nid, cid, Color::Red, nleft, nright)), Color::Black) == 1 by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright) == t.model);
                                                            rewrite(Context::Left(gparent, ugp, Color::Black, usib, uup) == cup);
                                                            rewrite(gparent == cgp);
                                                            rewrite(Color::Red == ccolor);
                                                            assumption();
                                                        }
                                                        have rb_parent_consistent(plug(Context::Right(cid, gparent, Color::Red, csib, Context::Left(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright)), 0) == 1 by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright) == t.model);
                                                            rewrite(Context::Left(gparent, ugp, Color::Black, usib, uup) == cup);
                                                            rewrite(gparent == cgp);
                                                            rewrite(Color::Red == ccolor);
                                                            assumption();
                                                        }
                                                        have rb_inorder(plug(Context::Right(cid, gparent, Color::Red, csib, Context::Left(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright))) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright) == t.model);
                                                            rewrite(Context::Left(gparent, ugp, Color::Black, usib, uup) == cup);
                                                            rewrite(gparent == cgp);
                                                            rewrite(Color::Red == ccolor);
                                                            assumption();
                                                        }
                                                        apply(ctx_insert_case2_left_exit_step(ugp, gparent, cid, nid, csib, nleft, nright, usib, uup)) using {
                                                            is_rb(RbTree::Node(nid, cid, Color::Red, nleft, nright)) == 1;
                                                            rb_root_black(usib) == 1;
                                                            ctx_rb(Context::Right(cid, gparent, Color::Red, csib, Context::Left(gparent, ugp, Color::Black, usib, uup)), black_height(RbTree::Node(nid, cid, Color::Red, nleft, nright)), Color::Black) == 1;
                                                            rb_parent_consistent(plug(Context::Right(cid, gparent, Color::Red, csib, Context::Left(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright)), 0) == 1;
                                                        };
                                                        let { left: nl_at, right: nr_at } = unfold(t);
                                                        have (node->__rb_parent_color & 1) == color_bit(Color::Red) by {
                                                            rewrite(Color::Red == ncolor);
                                                            assumption();
                                                        }
                                                        step();
                                                        step();
                                                        step();
                                                        have separate(memory(parent->rb_right), memory(node->rb_left)) by { assumption(); }
                                                        mark before_inner_parent_right;
                                                        have at(before_inner_parent_right, parent->rb_left == parent->rb_left) by { normalize(); }
                                                        have separate(memory(parent->rb_left), memory(parent->rb_right)) by { assumption(); }
                                                        have separate(memory(parent->rb_left), memory(node->rb_left)) by { assumption(); }
                                                        mark before_inner_node_left;
                                                        have at(before_inner_node_left, node->rb_right == node->rb_right) by { normalize(); }
                                                        have separate(memory(node->rb_right), memory(parent->rb_right)) by { assumption(); }
                                                        have separate(memory(node->rb_right), memory(node->rb_left)) by { assumption(); }
                                                        mark before_triangle_grandparent_tag;
                                                        have at(before_triangle_grandparent_tag, (gparent->__rb_parent_color & 1) == color_bit(ucolor)) by { assumption(); }
                                                        have at(before_triangle_grandparent_tag, ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp) by { assumption(); }
                                                        have separate(memory(gparent->__rb_parent_color), memory(parent->rb_right)) by { assumption(); }
                                                        have separate(memory(gparent->__rb_parent_color), memory(node->rb_left)) by { assumption(); }
                                                        have at(before_triangle_grandparent_tag, gparent->rb_right == at(triangle_uncle_pointer, tmp)) by { assumption(); }
                                                        have separate(memory(gparent->rb_right), memory(parent->rb_right)) by { assumption(); }
                                                        have separate(memory(gparent->rb_right), memory(node->rb_left)) by { assumption(); }
                                                        match nl_at.model ensuring {
                                                            owns bn: rb_at(tmp);
                                                            fact bn.model == rb_reparent(nleft, cid);
                                                            fact node->rb_left == parent;
                                                            fact gparent->rb_right == at(triangle_uncle_pointer, tmp);
                                                            fact (gparent->__rb_parent_color & 1) == color_bit(ucolor);
                                                            fact ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp;
                                                            fact parent->rb_right == tmp;
                                                            fact node->rb_right == at(before_inner_node_left, node->rb_right);
                                                            fact parent->rb_left == at(before_inner_parent_right, parent->rb_left);
                                                        } {
                                                            RbTree::Empty => {
                                                                unfold(nl_at);
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                have rb_reparent(nleft, cid) == RbTree::Empty by {
                                                                    rewrite(nleft == RbTree::Empty);
                                                                    unfold(rb_reparent(RbTree::Empty, cid)); normalize();
                                                                }
                                                                transport(at(before_inner_parent_right, parent->rb_left == parent->rb_left), parent->rb_left == at(before_inner_parent_right, parent->rb_left)) using {
                                                                    at(before_inner_parent_right, parent->rb_left == parent->rb_left);
                                                                    separate(memory(parent->rb_left), memory(parent->rb_right));
                                                                    separate(memory(parent->rb_left), memory(node->rb_left));
                                                                };
                                                                transport(at(before_inner_node_left, node->rb_right == node->rb_right), node->rb_right == at(before_inner_node_left, node->rb_right)) using {
                                                                    at(before_inner_node_left, node->rb_right == node->rb_right);
                                                                    separate(memory(node->rb_right), memory(parent->rb_right));
                                                                    separate(memory(node->rb_right), memory(node->rb_left));
                                                                };
                                                                have parent->rb_right == tmp by { assumption(); }
                                                                transport(at(before_triangle_grandparent_tag, (gparent->__rb_parent_color & 1) == color_bit(ucolor)), (gparent->__rb_parent_color & 1) == color_bit(ucolor)) using {
                                                                    at(before_triangle_grandparent_tag, (gparent->__rb_parent_color & 1) == color_bit(ucolor));
                                                                    separate(memory(gparent->__rb_parent_color), memory(parent->rb_right));
                                                                    separate(memory(gparent->__rb_parent_color), memory(node->rb_left));
                                                                };
                                                                transport(at(before_triangle_grandparent_tag, ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp), ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp) using {
                                                                    at(before_triangle_grandparent_tag, ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp);
                                                                    separate(memory(gparent->__rb_parent_color), memory(parent->rb_right));
                                                                    separate(memory(gparent->__rb_parent_color), memory(node->rb_left));
                                                                };
                                                                transport(at(before_triangle_grandparent_tag, gparent->rb_right == at(triangle_uncle_pointer, tmp)), gparent->rb_right == at(triangle_uncle_pointer, tmp)) using {
                                                                    at(before_triangle_grandparent_tag, gparent->rb_right == at(triangle_uncle_pointer, tmp));
                                                                    separate(memory(gparent->rb_right), memory(parent->rb_right));
                                                                    separate(memory(gparent->rb_right), memory(node->rb_left));
                                                                };
                                                                have node->rb_left == parent by { normalize(); }
                                                                let bn = fold(rb_at(tmp), { model: RbTree::Empty });
                                                                have bn.model == rb_reparent(nleft, cid) by {
                                                                    rewrite(rb_reparent(nleft, cid) == RbTree::Empty);
                                                                    solve();
                                                                }
                                                            },
                                                            RbTree::Node(bx, bp, bcol, bl, br) => {
                                                                let { left: bl_at, right: br_at } = unfold(nl_at);
                                                                step();
                                                                mark before_inner_child_links;
                                                                have separate(memory(node->rb_left), memory(tmp->__rb_parent_color)) by { assumption(); }
                                                                have separate(memory(gparent->rb_right), memory(tmp->__rb_parent_color)) by { assumption(); }
                                                                have separate(memory(gparent->__rb_parent_color), memory(tmp->__rb_parent_color)) by { assumption(); }
                                                                have separate(memory(node->rb_right), memory(tmp->__rb_parent_color)) by { assumption(); }
                                                                have separate(memory(parent->rb_left), memory(tmp->__rb_parent_color)) by { assumption(); }
                                                                have separate(memory(parent->rb_right), memory(tmp->__rb_parent_color)) by { assumption(); }
                                                                have at(before_inner_child_links, tmp->rb_right == bx->rb_right) by { assumption(); }
                                                                have at(before_inner_child_links, separate(memory(tmp->rb_right), memory(parent->rb_right))) by { assumption(); }
                                                                have at(before_inner_child_links, separate(memory(tmp->rb_right), memory(node->rb_left))) by { assumption(); }
                                                                have at(before_inner_child_links, separate(memory(tmp->rb_right), memory(tmp->__rb_parent_color))) by { assumption(); }
                                                                have at(before_inner_child_links, tmp->rb_left == bx->rb_left) by { assumption(); }
                                                                have at(before_inner_child_links, separate(memory(tmp->rb_left), memory(parent->rb_right))) by { assumption(); }
                                                                have at(before_inner_child_links, separate(memory(tmp->rb_left), memory(node->rb_left))) by { assumption(); }
                                                                have at(before_inner_child_links, separate(memory(tmp->rb_left), memory(tmp->__rb_parent_color))) by { assumption(); }
                                                                have rb_root_black(RbTree::Node(bx, bp, bcol, bl, br)) == 1 by {
                                                                    rewrite(RbTree::Node(bx, bp, bcol, bl, br) == nleft);
                                                                    assumption();
                                                                }
                                                                have color_bit(bcol) == 1 by {
                                                                    apply(rb_root_black_node_color_bit(bx, bp, bcol, bl, br)) using {
                                                                        rb_root_black(RbTree::Node(bx, bp, bcol, bl, br)) == 1;
                                                                    };
                                                                    assumption();
                                                                }
                                                                have rb_reparent(nleft, cid) == RbTree::Node(bx, cid, bcol, bl, br) by {
                                                                    rewrite(nleft == RbTree::Node(bx, bp, bcol, bl, br));
                                                                    unfold(rb_reparent(RbTree::Node(bx, bp, bcol, bl, br), cid)); normalize();
                                                                }
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                transport(at(before_inner_child_links, tmp->rb_right == bx->rb_right), tmp->rb_right == at(before_inner_child_links, bx->rb_right)) using {
                                                                    at(before_inner_child_links, tmp->rb_right == bx->rb_right);
                                                                    at(before_inner_child_links, separate(memory(tmp->rb_right), memory(parent->rb_right)));
                                                                    at(before_inner_child_links, separate(memory(tmp->rb_right), memory(node->rb_left)));
                                                                    at(before_inner_child_links, separate(memory(tmp->rb_right), memory(tmp->__rb_parent_color)));
                                                                };
                                                                transport(at(before_inner_child_links, tmp->rb_left == bx->rb_left), tmp->rb_left == at(before_inner_child_links, bx->rb_left)) using {
                                                                    at(before_inner_child_links, tmp->rb_left == bx->rb_left);
                                                                    at(before_inner_child_links, separate(memory(tmp->rb_left), memory(parent->rb_right)));
                                                                    at(before_inner_child_links, separate(memory(tmp->rb_left), memory(node->rb_left)));
                                                                    at(before_inner_child_links, separate(memory(tmp->rb_left), memory(tmp->__rb_parent_color)));
                                                                };
                                                                transport(at(before_inner_parent_right, parent->rb_left == parent->rb_left), parent->rb_left == at(before_inner_parent_right, parent->rb_left)) using {
                                                                    at(before_inner_parent_right, parent->rb_left == parent->rb_left);
                                                                    separate(memory(parent->rb_left), memory(parent->rb_right));
                                                                    separate(memory(parent->rb_left), memory(node->rb_left));
                                                                    separate(memory(parent->rb_left), memory(tmp->__rb_parent_color));
                                                                };
                                                                transport(at(before_inner_node_left, node->rb_right == node->rb_right), node->rb_right == at(before_inner_node_left, node->rb_right)) using {
                                                                    at(before_inner_node_left, node->rb_right == node->rb_right);
                                                                    separate(memory(node->rb_right), memory(parent->rb_right));
                                                                    separate(memory(node->rb_right), memory(node->rb_left));
                                                                    separate(memory(node->rb_right), memory(tmp->__rb_parent_color));
                                                                };
                                                                have parent->rb_right == tmp by { assumption(); }
                                                                transport(at(before_triangle_grandparent_tag, (gparent->__rb_parent_color & 1) == color_bit(ucolor)), (gparent->__rb_parent_color & 1) == color_bit(ucolor)) using {
                                                                    at(before_triangle_grandparent_tag, (gparent->__rb_parent_color & 1) == color_bit(ucolor));
                                                                    separate(memory(gparent->__rb_parent_color), memory(parent->rb_right));
                                                                    separate(memory(gparent->__rb_parent_color), memory(node->rb_left));
                                                                    separate(memory(gparent->__rb_parent_color), memory(tmp->__rb_parent_color));
                                                                };
                                                                transport(at(before_triangle_grandparent_tag, ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp), ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp) using {
                                                                    at(before_triangle_grandparent_tag, ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp);
                                                                    separate(memory(gparent->__rb_parent_color), memory(parent->rb_right));
                                                                    separate(memory(gparent->__rb_parent_color), memory(node->rb_left));
                                                                    separate(memory(gparent->__rb_parent_color), memory(tmp->__rb_parent_color));
                                                                };
                                                                transport(at(before_triangle_grandparent_tag, gparent->rb_right == at(triangle_uncle_pointer, tmp)), gparent->rb_right == at(triangle_uncle_pointer, tmp)) using {
                                                                    at(before_triangle_grandparent_tag, gparent->rb_right == at(triangle_uncle_pointer, tmp));
                                                                    separate(memory(gparent->rb_right), memory(parent->rb_right));
                                                                    separate(memory(gparent->rb_right), memory(node->rb_left));
                                                                    separate(memory(gparent->rb_right), memory(tmp->__rb_parent_color));
                                                                };
                                                                have node->rb_left == parent by { normalize(); }
                                                                let bn = fold(rb_at(tmp), { model: RbTree::Node(bx, cid, bcol, bl, br) }, { left: bl_at, right: br_at });
                                                                have bn.model == rb_reparent(nleft, cid) by {
                                                                    rewrite(rb_reparent(nleft, cid) == RbTree::Node(bx, cid, bcol, bl, br));
                                                                    solve();
                                                                }
                                                            },
                                                        }
                                                        mark before_inner_parent_color;
                                                        have at(before_inner_parent_color, node->rb_left == parent) by { assumption(); }
                                                        have separate(memory(node->rb_left), memory(parent->__rb_parent_color)) by { assumption(); }
                                                        have at(before_inner_parent_color, gparent->rb_right == at(triangle_uncle_pointer, tmp)) by { assumption(); }
                                                        have separate(memory(gparent->rb_right), memory(parent->__rb_parent_color)) by { assumption(); }
                                                        have at(before_inner_parent_color, (gparent->__rb_parent_color & 1) == color_bit(ucolor)) by { assumption(); }
                                                        have at(before_inner_parent_color, ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp) by { assumption(); }
                                                        have separate(memory(gparent->__rb_parent_color), memory(parent->__rb_parent_color)) by { assumption(); }
                                                        have at(before_inner_parent_color, parent->rb_right == tmp) by { assumption(); }
                                                        have at(before_inner_parent_color, node->rb_right == at(before_inner_node_left, node->rb_right)) by { assumption(); }
                                                        have separate(memory(node->rb_right), memory(parent->__rb_parent_color)) by { assumption(); }
                                                        have at(before_inner_parent_color, parent->rb_left == at(before_inner_parent_right, parent->rb_left)) by { assumption(); }
                                                        have separate(memory(parent->rb_left), memory(parent->__rb_parent_color)) by { assumption(); }
                                                        have separate(memory(parent->rb_right), memory(parent->__rb_parent_color)) by { assumption(); }
                                                        step();
                                                        transport(at(before_inner_parent_color, parent->rb_right == tmp), parent->rb_right == tmp) using {
                                                            at(before_inner_parent_color, parent->rb_right == tmp);
                                                            separate(memory(parent->rb_right), memory(parent->__rb_parent_color));
                                                        };
                                                        transport(at(before_inner_parent_color, parent->rb_left == at(before_inner_parent_right, parent->rb_left)), parent->rb_left == at(before_inner_parent_right, parent->rb_left)) using {
                                                            at(before_inner_parent_color, parent->rb_left == at(before_inner_parent_right, parent->rb_left));
                                                            separate(memory(parent->rb_left), memory(parent->__rb_parent_color));
                                                        };
                                                        transport(at(before_inner_parent_color, node->rb_right == at(before_inner_node_left, node->rb_right)), node->rb_right == at(before_inner_node_left, node->rb_right)) using {
                                                            at(before_inner_parent_color, node->rb_right == at(before_inner_node_left, node->rb_right));
                                                            separate(memory(node->rb_right), memory(parent->__rb_parent_color));
                                                        };
                                                        transport(at(before_inner_parent_color, (gparent->__rb_parent_color & 1) == color_bit(ucolor)), (gparent->__rb_parent_color & 1) == color_bit(ucolor)) using {
                                                            at(before_inner_parent_color, (gparent->__rb_parent_color & 1) == color_bit(ucolor));
                                                            separate(memory(gparent->__rb_parent_color), memory(parent->__rb_parent_color));
                                                        };
                                                        transport(at(before_inner_parent_color, ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp), ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp) using {
                                                            at(before_inner_parent_color, ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp);
                                                            separate(memory(gparent->__rb_parent_color), memory(parent->__rb_parent_color));
                                                        };
                                                        transport(at(before_inner_parent_color, gparent->rb_right == at(triangle_uncle_pointer, tmp)), gparent->rb_right == at(triangle_uncle_pointer, tmp)) using {
                                                            at(before_inner_parent_color, gparent->rb_right == at(triangle_uncle_pointer, tmp));
                                                            separate(memory(gparent->rb_right), memory(parent->__rb_parent_color));
                                                        };
                                                        transport(at(before_inner_parent_color, node->rb_left == parent), node->rb_left == parent) using {
                                                            at(before_inner_parent_color, node->rb_left == parent);
                                                            separate(memory(node->rb_left), memory(parent->__rb_parent_color));
                                                        };
                                                        have rb_parent_is(rb_reparent(nleft, cid), cid) == 1 by {
                                                            apply(rb_reparent_parent_is(nleft, cid));
                                                            assumption();
                                                        }
                                                        let pn = fold(rb_at(parent), { model: RbTree::Node(cid, nid, Color::Red, csib, rb_reparent(nleft, cid)) }, { left: cs, right: bn });
                                                        mark triangle_old_parent;
                                                        have at(triangle_old_parent, node->rb_left == parent) by { assumption(); }
                                                        step();
                                                        step();
                                                        mark before_outer_grandparent_tag;
                                                        have at(before_outer_grandparent_tag, (gparent->__rb_parent_color & 1) == color_bit(ucolor)) by { assumption(); }
                                                        have at(before_outer_grandparent_tag, ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp) by { assumption(); }
                                                        have separate(memory(gparent->__rb_parent_color), memory(gparent->rb_left)) by { assumption(); }
                                                        have separate(memory(gparent->__rb_parent_color), memory(parent->rb_right)) by { assumption(); }
                                                        have at(before_outer_grandparent_tag, gparent->rb_right == at(triangle_uncle_pointer, tmp)) by { assumption(); }
                                                        have separate(memory(gparent->rb_right), memory(gparent->rb_left)) by { assumption(); }
                                                        have separate(memory(gparent->rb_right), memory(parent->rb_right)) by { assumption(); }
                                                        have at(before_outer_grandparent_tag, node->rb_left == at(triangle_old_parent, parent)) by { assumption(); }
                                                        have separate(memory(node->rb_left), memory(gparent->rb_left)) by { assumption(); }
                                                        have separate(memory(node->rb_left), memory(parent->rb_right)) by { assumption(); }
                                                        match nr_at.model ensuring {
                                                            owns rn: rb_at(tmp);
                                                            fact rn.model == rb_reparent(nright, gparent);
                                                            fact node->rb_left == at(triangle_old_parent, parent);
                                                            fact gparent->rb_right == at(triangle_uncle_pointer, tmp);
                                                            fact (gparent->__rb_parent_color & 1) == color_bit(ucolor);
                                                            fact ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp;
                                                        } {
                                                            RbTree::Empty => {
                                                                unfold(nr_at);
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                have rb_reparent(nright, gparent) == RbTree::Empty by {
                                                                    rewrite(nright == RbTree::Empty);
                                                                    unfold(rb_reparent(RbTree::Empty, gparent)); normalize();
                                                                }
                                                                transport(at(before_outer_grandparent_tag, (gparent->__rb_parent_color & 1) == color_bit(ucolor)), (gparent->__rb_parent_color & 1) == color_bit(ucolor)) using {
                                                                    at(before_outer_grandparent_tag, (gparent->__rb_parent_color & 1) == color_bit(ucolor));
                                                                    separate(memory(gparent->__rb_parent_color), memory(gparent->rb_left));
                                                                    separate(memory(gparent->__rb_parent_color), memory(parent->rb_right));
                                                                };
                                                                transport(at(before_outer_grandparent_tag, ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp), ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp) using {
                                                                    at(before_outer_grandparent_tag, ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp);
                                                                    separate(memory(gparent->__rb_parent_color), memory(gparent->rb_left));
                                                                    separate(memory(gparent->__rb_parent_color), memory(parent->rb_right));
                                                                };
                                                                transport(at(before_outer_grandparent_tag, gparent->rb_right == at(triangle_uncle_pointer, tmp)), gparent->rb_right == at(triangle_uncle_pointer, tmp)) using {
                                                                    at(before_outer_grandparent_tag, gparent->rb_right == at(triangle_uncle_pointer, tmp));
                                                                    separate(memory(gparent->rb_right), memory(gparent->rb_left));
                                                                    separate(memory(gparent->rb_right), memory(parent->rb_right));
                                                                };
                                                                transport(at(before_outer_grandparent_tag, node->rb_left == at(triangle_old_parent, parent)), node->rb_left == at(triangle_old_parent, parent)) using {
                                                                    at(before_outer_grandparent_tag, node->rb_left == at(triangle_old_parent, parent));
                                                                    separate(memory(node->rb_left), memory(gparent->rb_left));
                                                                    separate(memory(node->rb_left), memory(parent->rb_right));
                                                                };
                                                                let rn = fold(rb_at(tmp), { model: RbTree::Empty });
                                                                have rn.model == rb_reparent(nright, gparent) by {
                                                                    rewrite(rb_reparent(nright, gparent) == RbTree::Empty);
                                                                    solve();
                                                                }
                                                            },
                                                            RbTree::Node(rx, rp, rcol, rl, rr) => {
                                                                let { left: rl_at, right: rr_at } = unfold(nr_at);
                                                                step();
                                                                have separate(memory(node->rb_left), memory(tmp->__rb_parent_color)) by { assumption(); }
                                                                have separate(memory(gparent->rb_right), memory(tmp->__rb_parent_color)) by { assumption(); }
                                                                have separate(memory(gparent->__rb_parent_color), memory(tmp->__rb_parent_color)) by { assumption(); }
                                                                have rb_root_black(RbTree::Node(rx, rp, rcol, rl, rr)) == 1 by {
                                                                    rewrite(RbTree::Node(rx, rp, rcol, rl, rr) == nright);
                                                                    assumption();
                                                                }
                                                                have color_bit(rcol) == 1 by {
                                                                    apply(rb_root_black_node_color_bit(rx, rp, rcol, rl, rr)) using {
                                                                        rb_root_black(RbTree::Node(rx, rp, rcol, rl, rr)) == 1;
                                                                    };
                                                                    assumption();
                                                                }
                                                                have rb_reparent(nright, gparent) == RbTree::Node(rx, gparent, rcol, rl, rr) by {
                                                                    rewrite(nright == RbTree::Node(rx, rp, rcol, rl, rr));
                                                                    unfold(rb_reparent(RbTree::Node(rx, rp, rcol, rl, rr), gparent)); normalize();
                                                                }
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                transport(at(before_outer_grandparent_tag, (gparent->__rb_parent_color & 1) == color_bit(ucolor)), (gparent->__rb_parent_color & 1) == color_bit(ucolor)) using {
                                                                    at(before_outer_grandparent_tag, (gparent->__rb_parent_color & 1) == color_bit(ucolor));
                                                                    separate(memory(gparent->__rb_parent_color), memory(gparent->rb_left));
                                                                    separate(memory(gparent->__rb_parent_color), memory(parent->rb_right));
                                                                    separate(memory(gparent->__rb_parent_color), memory(tmp->__rb_parent_color));
                                                                };
                                                                transport(at(before_outer_grandparent_tag, ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp), ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp) using {
                                                                    at(before_outer_grandparent_tag, ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp);
                                                                    separate(memory(gparent->__rb_parent_color), memory(gparent->rb_left));
                                                                    separate(memory(gparent->__rb_parent_color), memory(parent->rb_right));
                                                                    separate(memory(gparent->__rb_parent_color), memory(tmp->__rb_parent_color));
                                                                };
                                                                transport(at(before_outer_grandparent_tag, gparent->rb_right == at(triangle_uncle_pointer, tmp)), gparent->rb_right == at(triangle_uncle_pointer, tmp)) using {
                                                                    at(before_outer_grandparent_tag, gparent->rb_right == at(triangle_uncle_pointer, tmp));
                                                                    separate(memory(gparent->rb_right), memory(gparent->rb_left));
                                                                    separate(memory(gparent->rb_right), memory(parent->rb_right));
                                                                    separate(memory(gparent->rb_right), memory(tmp->__rb_parent_color));
                                                                };
                                                                transport(at(before_outer_grandparent_tag, node->rb_left == at(triangle_old_parent, parent)), node->rb_left == at(triangle_old_parent, parent)) using {
                                                                    at(before_outer_grandparent_tag, node->rb_left == at(triangle_old_parent, parent));
                                                                    separate(memory(node->rb_left), memory(gparent->rb_left));
                                                                    separate(memory(node->rb_left), memory(parent->rb_right));
                                                                    separate(memory(node->rb_left), memory(tmp->__rb_parent_color));
                                                                };
                                                                let rn = fold(rb_at(tmp), { model: RbTree::Node(rx, gparent, rcol, rl, rr) }, { left: rl_at, right: rr_at });
                                                                have rn.model == rb_reparent(nright, gparent) by {
                                                                    rewrite(rb_reparent(nright, gparent) == RbTree::Node(rx, gparent, rcol, rl, rr));
                                                                    solve();
                                                                }
                                                            },
                                                        }
                                                        have (gparent->__rb_parent_color & 1) == 1 by {
                                                            rewrite((gparent->__rb_parent_color & 1) == color_bit(ucolor));
                                                            rewrite(ucolor == Color::Black);
                                                            unfold(color_bit(Color::Black));
                                                            solve();
                                                        }
                                                        mark before_triangle_parent_changes;
                                                        have at(before_triangle_parent_changes, gparent->rb_right == at(triangle_uncle_pointer, tmp)) by { assumption(); }
                                                        have separate(memory(gparent->rb_right), memory(gparent->__rb_parent_color)) by { assumption(); }
                                                        have separate(memory(gparent->rb_right), memory(parent->__rb_parent_color)) by { assumption(); }
                                                        have at(before_triangle_parent_changes, node->rb_left == at(triangle_old_parent, parent)) by { assumption(); }
                                                        have separate(memory(node->rb_left), memory(gparent->__rb_parent_color)) by { assumption(); }
                                                        have separate(memory(node->rb_left), memory(parent->__rb_parent_color)) by { assumption(); }
                                                        match uu.model ensuring {
                                                            owns c: ctx_at(node, root);
                                                            fact c.model == uup;
                                                            fact node->rb_left == at(triangle_old_parent, parent);
                                                            fact gparent->rb_right == at(triangle_uncle_pointer, tmp);
                                                        } {
                                                            Context::Top => {
                                                                have ctx_node_is(Context::Top, ugp) == 1 by {
                                                                    rewrite(Context::Top == uu.model);
                                                                    rewrite(uu.model == uup);
                                                                    assumption();
                                                                }
                                                                have ugp == 0 by {
                                                                    apply(ctx_node_is_top_null(ugp)) using {
                                                                        ctx_node_is(Context::Top, ugp) == 1;
                                                                    };
                                                                    assumption();
                                                                }
                                                                unfold(uu);
                                                                have separate(memory(gparent->rb_right), memory(root->rb_node)) by { assumption(); }
                                                                have separate(memory(node->rb_left), memory(root->rb_node)) by { assumption(); }
                                                                step();
                                                                transport(at(before_triangle_parent_changes, gparent->rb_right == at(triangle_uncle_pointer, tmp)), gparent->rb_right == at(triangle_uncle_pointer, tmp)) using {
                                                                    at(before_triangle_parent_changes, gparent->rb_right == at(triangle_uncle_pointer, tmp));
                                                                    separate(memory(gparent->rb_right), memory(gparent->__rb_parent_color));
                                                                    separate(memory(gparent->rb_right), memory(parent->__rb_parent_color));
                                                                    separate(memory(gparent->rb_right), memory(root->rb_node));
                                                                };
                                                                transport(at(before_triangle_parent_changes, node->rb_left == at(triangle_old_parent, parent)), node->rb_left == at(triangle_old_parent, parent)) using {
                                                                    at(before_triangle_parent_changes, node->rb_left == at(triangle_old_parent, parent));
                                                                    separate(memory(node->rb_left), memory(gparent->__rb_parent_color));
                                                                    separate(memory(node->rb_left), memory(parent->__rb_parent_color));
                                                                    separate(memory(node->rb_left), memory(root->rb_node));
                                                                };
                                                                let c = fold(ctx_at(node, root), { model: Context::Top });
                                                                have c.model == uup by { rewrite(uup == Context::Top); normalize(); }
                                                            },
                                                            Context::Left(xid, xgp, xcol, xsib, xup) => {
                                                                have ctx_node_is(Context::Left(xid, xgp, xcol, xsib, xup), ugp) == 1 by {
                                                                    rewrite(Context::Left(xid, xgp, xcol, xsib, xup) == uu.model);
                                                                    rewrite(uu.model == uup);
                                                                    assumption();
                                                                }
                                                                have ugp == xid by {
                                                                    apply(ctx_node_is_left_identity(xid, xgp, xcol, xsib, xup, ugp)) using {
                                                                        ctx_node_is(Context::Left(xid, xgp, xcol, xsib, xup), ugp) == 1;
                                                                    };
                                                                    assumption();
                                                                }
                                                                let { sibling: xs, up: xu } = unfold(uu);
                                                                have separate(memory(gparent->rb_right), memory(xid->rb_right)) by { assumption(); }
                                                                have separate(memory(node->rb_left), memory(xid->rb_right)) by { assumption(); }
                                                                have separate(memory(gparent->rb_right), memory(xid->rb_left)) by { assumption(); }
                                                                have separate(memory(node->rb_left), memory(xid->rb_left)) by { assumption(); }
                                                                step();
                                                                transport(at(before_triangle_parent_changes, gparent->rb_right == at(triangle_uncle_pointer, tmp)), gparent->rb_right == at(triangle_uncle_pointer, tmp)) using {
                                                                    at(before_triangle_parent_changes, gparent->rb_right == at(triangle_uncle_pointer, tmp));
                                                                    separate(memory(gparent->rb_right), memory(gparent->__rb_parent_color));
                                                                    separate(memory(gparent->rb_right), memory(parent->__rb_parent_color));
                                                                    separate(memory(gparent->rb_right), memory(xid->rb_right));
                                                                    separate(memory(gparent->rb_right), memory(xid->rb_left));
                                                                };
                                                                transport(at(before_triangle_parent_changes, node->rb_left == at(triangle_old_parent, parent)), node->rb_left == at(triangle_old_parent, parent)) using {
                                                                    at(before_triangle_parent_changes, node->rb_left == at(triangle_old_parent, parent));
                                                                    separate(memory(node->rb_left), memory(gparent->__rb_parent_color));
                                                                    separate(memory(node->rb_left), memory(parent->__rb_parent_color));
                                                                    separate(memory(node->rb_left), memory(xid->rb_right));
                                                                    separate(memory(node->rb_left), memory(xid->rb_left));
                                                                };
                                                                let c = fold(ctx_at(node, root), { model: Context::Left(xid, xgp, xcol, xsib, xup) }, { sibling: xs, up: xu });
                                                                have c.model == uup by { rewrite(uup == Context::Left(xid, xgp, xcol, xsib, xup)); normalize(); }
                                                            },
                                                            Context::Right(xid, xgp, xcol, xsib, xup) => {
                                                                have ctx_node_is(Context::Right(xid, xgp, xcol, xsib, xup), ugp) == 1 by {
                                                                    rewrite(Context::Right(xid, xgp, xcol, xsib, xup) == uu.model);
                                                                    rewrite(uu.model == uup);
                                                                    assumption();
                                                                }
                                                                have ugp == xid by {
                                                                    apply(ctx_node_is_right_identity(xid, xgp, xcol, xsib, xup, ugp)) using {
                                                                        ctx_node_is(Context::Right(xid, xgp, xcol, xsib, xup), ugp) == 1;
                                                                    };
                                                                    assumption();
                                                                }
                                                                let { sibling: xs, up: xu } = unfold(uu);
                                                                have separate(memory(gparent->rb_right), memory(xid->rb_right)) by { assumption(); }
                                                                have separate(memory(node->rb_left), memory(xid->rb_right)) by { assumption(); }
                                                                have separate(memory(gparent->rb_right), memory(xid->rb_left)) by { assumption(); }
                                                                have separate(memory(node->rb_left), memory(xid->rb_left)) by { assumption(); }
                                                                mark before_triangle_upper_link;
                                                                have at(before_triangle_upper_link, ((xid->__rb_parent_color & ~3) as (struct rb_node *)) == xgp) by { assumption(); }
                                                                have separate(memory(xid->__rb_parent_color), memory(gparent->__rb_parent_color)) by { assumption(); }
                                                                have separate(memory(xid->__rb_parent_color), memory(parent->__rb_parent_color)) by { assumption(); }
                                                                have separate(memory(xid->__rb_parent_color), memory(xid->rb_right)) by { assumption(); }
                                                                have separate(memory(xid->__rb_parent_color), memory(xid->rb_left)) by { assumption(); }
                                                                match xsib ensuring {
                                                                    owns xs: rb_at(xid->rb_left);
                                                                    fact xs.model == xsib;
                                                                    fact node->rb_left == at(triangle_old_parent, parent);
                                                                    fact gparent->rb_right == at(triangle_uncle_pointer, tmp);
                                                                    fact ((xid->__rb_parent_color & ~3) as (struct rb_node *)) == xgp;
                                                                } {
                                                                    RbTree::Empty => {
                                                                        unfold(xs);
                                                                        step();
                                                                        transport(at(before_triangle_upper_link, ((xid->__rb_parent_color & ~3) as (struct rb_node *)) == xgp), ((xid->__rb_parent_color & ~3) as (struct rb_node *)) == xgp) using {
                                                                            at(before_triangle_upper_link, ((xid->__rb_parent_color & ~3) as (struct rb_node *)) == xgp);
                                                                            separate(memory(xid->__rb_parent_color), memory(gparent->__rb_parent_color));
                                                                            separate(memory(xid->__rb_parent_color), memory(parent->__rb_parent_color));
                                                                            separate(memory(xid->__rb_parent_color), memory(xid->rb_right));
                                                                            separate(memory(xid->__rb_parent_color), memory(xid->rb_left));
                                                                        };
                                                                        transport(at(before_triangle_parent_changes, gparent->rb_right == at(triangle_uncle_pointer, tmp)), gparent->rb_right == at(triangle_uncle_pointer, tmp)) using {
                                                                            at(before_triangle_parent_changes, gparent->rb_right == at(triangle_uncle_pointer, tmp));
                                                                            separate(memory(gparent->rb_right), memory(gparent->__rb_parent_color));
                                                                            separate(memory(gparent->rb_right), memory(parent->__rb_parent_color));
                                                                            separate(memory(gparent->rb_right), memory(xid->rb_right));
                                                                            separate(memory(gparent->rb_right), memory(xid->rb_left));
                                                                        };
                                                                        transport(at(before_triangle_parent_changes, node->rb_left == at(triangle_old_parent, parent)), node->rb_left == at(triangle_old_parent, parent)) using {
                                                                            at(before_triangle_parent_changes, node->rb_left == at(triangle_old_parent, parent));
                                                                            separate(memory(node->rb_left), memory(gparent->__rb_parent_color));
                                                                            separate(memory(node->rb_left), memory(parent->__rb_parent_color));
                                                                            separate(memory(node->rb_left), memory(xid->rb_right));
                                                                            separate(memory(node->rb_left), memory(xid->rb_left));
                                                                        };
                                                                        let xs = fold(rb_at(0), { model: xsib });
                                                                    },
                                                                    RbTree::Node(yid, yp, ycol, yl, yr) => {
                                                                        let { left: yl_at, right: yr_at } = unfold(xs);
                                                                        step();
                                                                        transport(at(before_triangle_upper_link, ((xid->__rb_parent_color & ~3) as (struct rb_node *)) == xgp), ((xid->__rb_parent_color & ~3) as (struct rb_node *)) == xgp) using {
                                                                            at(before_triangle_upper_link, ((xid->__rb_parent_color & ~3) as (struct rb_node *)) == xgp);
                                                                            separate(memory(xid->__rb_parent_color), memory(gparent->__rb_parent_color));
                                                                            separate(memory(xid->__rb_parent_color), memory(parent->__rb_parent_color));
                                                                            separate(memory(xid->__rb_parent_color), memory(xid->rb_right));
                                                                            separate(memory(xid->__rb_parent_color), memory(xid->rb_left));
                                                                        };
                                                                        transport(at(before_triangle_parent_changes, gparent->rb_right == at(triangle_uncle_pointer, tmp)), gparent->rb_right == at(triangle_uncle_pointer, tmp)) using {
                                                                            at(before_triangle_parent_changes, gparent->rb_right == at(triangle_uncle_pointer, tmp));
                                                                            separate(memory(gparent->rb_right), memory(gparent->__rb_parent_color));
                                                                            separate(memory(gparent->rb_right), memory(parent->__rb_parent_color));
                                                                            separate(memory(gparent->rb_right), memory(xid->rb_right));
                                                                            separate(memory(gparent->rb_right), memory(xid->rb_left));
                                                                        };
                                                                        transport(at(before_triangle_parent_changes, node->rb_left == at(triangle_old_parent, parent)), node->rb_left == at(triangle_old_parent, parent)) using {
                                                                            at(before_triangle_parent_changes, node->rb_left == at(triangle_old_parent, parent));
                                                                            separate(memory(node->rb_left), memory(gparent->__rb_parent_color));
                                                                            separate(memory(node->rb_left), memory(parent->__rb_parent_color));
                                                                            separate(memory(node->rb_left), memory(xid->rb_right));
                                                                            separate(memory(node->rb_left), memory(xid->rb_left));
                                                                        };
                                                                        let xs = fold(rb_at(yid), { model: xsib }, { left: yl_at, right: yr_at });
                                                                    },
                                                                }
                                                                let c = fold(ctx_at(node, root), { model: Context::Right(xid, xgp, xcol, xsib, xup) }, { sibling: xs, up: xu });
                                                                have c.model == uup by { rewrite(uup == Context::Right(xid, xgp, xcol, xsib, xup)); normalize(); }
                                                            },
                                                        }
                                                            have rb_parent_is(rb_reparent(nright, gparent), gparent) == 1 by {
                                                                apply(rb_reparent_parent_is(nright, gparent));
                                                                assumption();
                                                            }
                                                            let gn = fold(rb_at(gparent), { model: RbTree::Node(gparent, nid, Color::Red, rb_reparent(nright, gparent), usib) }, { left: rn, right: un });
                                                            have rb_parent_is(RbTree::Node(cid, nid, Color::Red, csib, rb_reparent(nleft, cid)), nid) == 1 by {
                                                                unfold(rb_parent_is(RbTree::Node(cid, nid, Color::Red, csib, rb_reparent(nleft, cid)), nid));
                                                            }
                                                            have rb_parent_is(RbTree::Node(gparent, nid, Color::Red, rb_reparent(nright, gparent), usib), nid) == 1 by {
                                                                unfold(rb_parent_is(RbTree::Node(gparent, nid, Color::Red, rb_reparent(nright, gparent), usib), nid));
                                                            }
                                                            have (node->__rb_parent_color & 1) == color_bit(Color::Black) by {
                                                                unfold(color_bit(Color::Black));
                                                                solve();
                                                            }
                                                            let t = fold(rb_at(node), { model: RbTree::Node(nid, ugp, Color::Black, RbTree::Node(cid, nid, Color::Red, csib, rb_reparent(nleft, cid)), RbTree::Node(gparent, nid, Color::Red, rb_reparent(nright, gparent), usib)) }, { left: pn, right: gn });
                                                            have rb_inorder(plug(c.model, t.model)) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                                                rewrite(c.model == uup);
                                                                rewrite(t.model == RbTree::Node(nid, ugp, Color::Black, RbTree::Node(cid, nid, Color::Red, csib, rb_reparent(nleft, cid)), RbTree::Node(gparent, nid, Color::Red, rb_reparent(nright, gparent), usib)));
                                                                rewrite(rb_inorder(plug(uup, RbTree::Node(nid, ugp, Color::Black, RbTree::Node(cid, nid, Color::Red, csib, rb_reparent(nleft, cid)), RbTree::Node(gparent, nid, Color::Red, rb_reparent(nright, gparent), usib)))) == rb_inorder(plug(Context::Right(cid, gparent, Color::Red, csib, Context::Left(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright))));
                                                                assumption();
                                                            }
                                                            have is_rb_root(plug(c.model, t.model)) == 1 by {
                                                                rewrite(c.model == uup);
                                                                rewrite(t.model == RbTree::Node(nid, ugp, Color::Black, RbTree::Node(cid, nid, Color::Red, csib, rb_reparent(nleft, cid)), RbTree::Node(gparent, nid, Color::Red, rb_reparent(nright, gparent), usib)));
                                                                assumption();
                                                            }
                                                            have rb_parent_consistent(plug(c.model, t.model), 0) == 1 by {
                                                                rewrite(c.model == uup);
                                                                rewrite(t.model == RbTree::Node(nid, ugp, Color::Black, RbTree::Node(cid, nid, Color::Red, csib, rb_reparent(nleft, cid)), RbTree::Node(gparent, nid, Color::Red, rb_reparent(nright, gparent), usib)));
                                                                assumption();
                                                            }
                                                        have rb_tree_parent_consistent(plug(c.model, t.model)) == 1 by {
                                                            unfold(rb_tree_parent_consistent(plug(c.model, t.model)));
                                                        }
                                                        step();
                                                        step();
                                                    } else {
                                                        match us.model {
                                                            RbTree::Node(unid, unp, uncolor, unl, unr) => {
                                                                let { left: ul, right: ur } = unfold(us);
                                                                step();
                                                                match uncolor {
                                                                    Color::Red => {
                                                                        have (tmp->__rb_parent_color & 1) == 0 by {
                                                                            rewrite((tmp->__rb_parent_color & 1) == color_bit(uncolor));
                                                                            rewrite(uncolor == Color::Red);
                                                                            unfold(color_bit(Color::Red));
                                                                            solve();
                                                                        }
                                                                        have ucolor == Color::Black by {
                                                                            apply(ctx_rb_left_red_focus_black(uid, ugp, ucolor, usib, uup, black_height(t.model))) using {
                                                                                ctx_rb(Context::Left(uid, ugp, ucolor, usib, uup), black_height(t.model), Color::Red) == 1;
                                                                            };
                                                                            assumption();
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(unid, unp, uncolor, unl, unr), gparent) == 1 by {
                                                                            rewrite(RbTree::Node(unid, unp, uncolor, unl, unr) == usib);
                                                                            assumption();
                                                                        }
                                                                        have unp == gparent by {
                                                                            apply(rb_parent_is_node_parent(unid, unp, uncolor, unl, unr, gparent)) using {
                                                                                rb_parent_is(RbTree::Node(unid, unp, uncolor, unl, unr), gparent) == 1;
                                                                            };
                                                                            assumption();
                                                                        }
                                                                        have usib == RbTree::Node(unid, gparent, Color::Red, unl, unr) by {
                                                                            rewrite(usib == RbTree::Node(unid, unp, uncolor, unl, unr));
                                                                            rewrite(unp == gparent);
                                                                            rewrite(uncolor == Color::Red);
                                                                            normalize();
                                                                        }
                                                                        have cup == Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup) by {
                                                                            rewrite(cup == Context::Left(uid, ugp, ucolor, usib, uup));
                                                                            rewrite(usib == RbTree::Node(unid, gparent, Color::Red, unl, unr));
                                                                            rewrite(ucolor == Color::Black);
                                                                            rewrite(uid == gparent);
                                                                            normalize();
                                                                        }
                                                                        have almost_rb_insert(RbTree::Node(cid, cgp, Color::Red, csib, t.model)) == 1 by {
                                                                            apply(ctx_insert_cursor_right_parent(cid, cgp, t.model, csib, cup)) using {
                                                                                is_rb(t.model) == 1;
                                                                                ctx_rb(Context::Right(cid, cgp, Color::Red, csib, cup), black_height(t.model), Color::Black) == 1;
                                                                            };
                                                                            assumption();
                                                                        }
                                                                        have almost_rb_insert(RbTree::Node(cid, gparent, Color::Red, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright))) == 1 by {
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                                            rewrite(gparent == cgp);
                                                                            assumption();
                                                                        }
                                                                        have black_height(csib) == black_height(t.model) by {
                                                                            apply(ctx_insert_cursor_right_parent(cid, cgp, t.model, csib, cup)) using {
                                                                                is_rb(t.model) == 1;
                                                                                ctx_rb(Context::Right(cid, cgp, Color::Red, csib, cup), black_height(t.model), Color::Black) == 1;
                                                                            };
                                                                            assumption();
                                                                        }
                                                                        apply(ctx_insert_case1_left_step(ugp, gparent, cid, unid, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright), unl, unr, uup)) using {
                                                                            almost_rb_insert(RbTree::Node(cid, gparent, Color::Red, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright))) == 1;
                                                                            ctx_rb(Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), black_height(csib), Color::Red) == 1;
                                                                        };
                                                                        have rb_inorder(plug(Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), RbTree::Node(cid, gparent, Color::Red, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)))) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                                                            apply(plug_right_frame(cid, cgp, ccolor, csib, cup, t.model));
                                                                            rewrite(Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup) == cup);
                                                                            rewrite(gparent == cgp);
                                                                            rewrite(Color::Red == ccolor);
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                                            rewrite(plug(cup, RbTree::Node(cid, cgp, ccolor, csib, t.model))
                                                                                == plug(Context::Right(cid, cgp, ccolor, csib, cup), t.model));
                                                                            assumption();
                                                                        }
                                                                        have rb_parent_consistent(plug(Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), RbTree::Node(cid, gparent, Color::Red, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright))), 0) == 1 by {
                                                                            apply(plug_right_frame(cid, cgp, ccolor, csib, cup, t.model));
                                                                            rewrite(Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup) == cup);
                                                                            rewrite(gparent == cgp);
                                                                            rewrite(Color::Red == ccolor);
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                                            rewrite(plug(cup, RbTree::Node(cid, cgp, ccolor, csib, t.model))
                                                                                == plug(Context::Right(cid, cgp, ccolor, csib, cup), t.model));
                                                                            assumption();
                                                                        }
                                                                        have rb_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)), RbTree::Node(unid, gparent, Color::Black, unl, unr))), 0) == 1 by {
                                                                            rewrite(rb_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)), RbTree::Node(unid, gparent, Color::Black, unl, unr))), 0)
                                                                                == rb_parent_consistent(plug(Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), RbTree::Node(cid, gparent, Color::Red, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright))), 0));
                                                                            assumption();
                                                                        }
                                                                        have rb_tree_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)), RbTree::Node(unid, gparent, Color::Black, unl, unr)))) == 1 by {
                                                                            unfold(rb_tree_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)), RbTree::Node(unid, gparent, Color::Black, unl, unr)))));
                                                                        }
                                                                        have rb_color_bit(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)), RbTree::Node(unid, gparent, Color::Black, unl, unr))) == 0 by {
                                                                            unfold(rb_color_bit(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)), RbTree::Node(unid, gparent, Color::Black, unl, unr))));
                                                                            unfold(color_bit(Color::Red));
                                                                            normalize();
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(nid, nparent, ncolor, nleft, nright), parent) == 1 by {
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                                            assumption();
                                                                        }
                                                                        have color_bit(Color::Black) == 1 by {
                                                                            unfold(color_bit(Color::Black));
                                                                            normalize();
                                                                        }
                                                                        have color_bit(Color::Red) == 0 by {
                                                                            unfold(color_bit(Color::Red));
                                                                            normalize();
                                                                        }
                                                                        mark before_recolor_tags_3;
                                                                        have at(before_recolor_tags_3, gparent->rb_left == parent) by { assumption(); }
                                                                        have at(before_recolor_tags_3, separate(memory(gparent->rb_left), memory(gparent->__rb_parent_color))) by { assumption(); }
                                                                        have at(before_recolor_tags_3, separate(memory(gparent->rb_left), memory(parent->__rb_parent_color))) by { assumption(); }
                                                                        have at(before_recolor_tags_3, separate(memory(gparent->rb_left), memory(tmp->__rb_parent_color))) by { assumption(); }
                                                                        have at(before_recolor_tags_3, gparent->rb_right == tmp) by { assumption(); }
                                                                        have at(before_recolor_tags_3, separate(memory(gparent->rb_right), memory(gparent->__rb_parent_color))) by { assumption(); }
                                                                        have at(before_recolor_tags_3, separate(memory(gparent->rb_right), memory(parent->__rb_parent_color))) by { assumption(); }
                                                                        have at(before_recolor_tags_3, separate(memory(gparent->rb_right), memory(tmp->__rb_parent_color))) by { assumption(); }
                                                                        step();
                                                                        step();
                                                                        step();
                                                                        let un = fold(rb_at(tmp), { model: RbTree::Node(unid, gparent, Color::Black, unl, unr) }, { left: ul, right: ur });
                                                                        let pn = fold(rb_at(parent), { model: RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)) }, { left: cs, right: t });
                                                                        step();
                                                                        step();
                                                                        step();
                                                                        have rb_parent_is(RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)), gparent) == 1 by {
                                                                            unfold(rb_parent_is(RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)), gparent));
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(unid, gparent, Color::Black, unl, unr), gparent) == 1 by {
                                                                            unfold(rb_parent_is(RbTree::Node(unid, gparent, Color::Black, unl, unr), gparent));
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)), RbTree::Node(unid, gparent, Color::Black, unl, unr)), ugp) == 1 by {
                                                                            unfold(rb_parent_is(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)), RbTree::Node(unid, gparent, Color::Black, unl, unr)), ugp));
                                                                        }
                                                                        transport(at(before_recolor_tags_3, gparent->rb_left == parent), gparent->rb_left == at(before_recolor_tags_3, parent)) using {
                                                                            at(before_recolor_tags_3, gparent->rb_left == parent);
                                                                            at(before_recolor_tags_3, separate(memory(gparent->rb_left), memory(gparent->__rb_parent_color)));
                                                                            at(before_recolor_tags_3, separate(memory(gparent->rb_left), memory(parent->__rb_parent_color)));
                                                                            at(before_recolor_tags_3, separate(memory(gparent->rb_left), memory(tmp->__rb_parent_color)));
                                                                        };
                                                                        transport(at(before_recolor_tags_3, gparent->rb_right == tmp), gparent->rb_right == at(before_recolor_tags_3, tmp)) using {
                                                                            at(before_recolor_tags_3, gparent->rb_right == tmp);
                                                                            at(before_recolor_tags_3, separate(memory(gparent->rb_right), memory(gparent->__rb_parent_color)));
                                                                            at(before_recolor_tags_3, separate(memory(gparent->rb_right), memory(parent->__rb_parent_color)));
                                                                            at(before_recolor_tags_3, separate(memory(gparent->rb_right), memory(tmp->__rb_parent_color)));
                                                                        };
                                                                        let gn = fold(rb_at(gparent), { model: RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)), RbTree::Node(unid, gparent, Color::Black, unl, unr)) }, { left: pn, right: un });
                                                                    },
                                                                    Color::Black => {
                                                                        have rb_root_black(usib) == 1 by {
                                                                            rewrite(usib == RbTree::Node(unid, unp, uncolor, unl, unr));
                                                                            rewrite(uncolor == Color::Black);
                                                                            apply(rb_root_black_black_node(unid, unp, unl, unr));
                                                                            assumption();
                                                                        }
                                                                        contradiction(rb_root_black(usib) == 1);
                                                                    },
                                                                }
                                                            },
                                                            RbTree::Empty => {
                                                                have rb_root_black(usib) == 1 by {
                                                                    rewrite(usib == RbTree::Empty);
                                                                    unfold(rb_root_black(RbTree::Empty)); normalize();
                                                                }
                                                                contradiction(rb_root_black(usib) == 1);
                                                            },
                                                        }
                                                    }
                                                },
                                                Context::Right(uid, ugp, ucolor, usib, uup) => {
                                                    have ctx_node_is(Context::Right(uid, ugp, ucolor,
                                                        usib, uup), cgp) == 1 by {
                                                        rewrite(Context::Right(uid, ugp, ucolor, usib, uup)
                                                            == cu.model);
                                                        rewrite(cu.model == cup);
                                                        assumption();
                                                    }
                                                    have cgp == uid by {
                                                        apply(ctx_node_is_right_identity(uid, ugp, ucolor,
                                                            usib, uup, cgp)) using {
                                                            ctx_node_is(Context::Right(uid, ugp, ucolor,
                                                                usib, uup), cgp) == 1;
                                                        };
                                                        assumption();
                                                    }
                                                    have ctx_rb(Context::Right(uid, ugp, ucolor, usib, uup), black_height(t.model), Color::Red) == 1 by {
                                                        rewrite(Context::Right(uid, ugp, ucolor, usib, uup) == cu.model);
                                                        assumption();
                                                    }
                                                    let { sibling: us, up: uu } = unfold(cu);
                                                    mark before_grandparent_links;
                                                    have separate(memory(gparent->rb_left), memory(gparent->rb_right)) by { assumption(); }
                                                    have separate(memory(gparent->rb_left), memory(parent->rb_left)) by { assumption(); }
                                                    have separate(memory(gparent->rb_left), memory(gparent->__rb_parent_color)) by { assumption(); }
                                                    have separate(memory(gparent->rb_left), memory(parent->__rb_parent_color)) by { assumption(); }
                                                    have at(before_grandparent_links, ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp) by { assumption(); }
                                                    have separate(memory(gparent->__rb_parent_color), memory(gparent->rb_left)) by { assumption(); }
                                                    have separate(memory(gparent->__rb_parent_color), memory(parent->rb_right)) by { assumption(); }
                                                    step();
                                                    step();
                                                    step();
                                                    mark before_uncle_pointer_changes;
                                                    have at(before_uncle_pointer_changes, gparent->rb_left == at(before_uncle_pointer_changes, tmp)) by { assumption(); }
                                                    have at(before_uncle_pointer_changes, parent->rb_right == node) by { assumption(); }
                                                    have separate(memory(parent->rb_right), memory(gparent->rb_right)) by { assumption(); }
                                                    have separate(memory(parent->rb_right), memory(parent->rb_left)) by { assumption(); }
                                                    have separate(memory(parent->rb_right), memory(gparent->__rb_parent_color)) by { assumption(); }
                                                    have separate(memory(parent->rb_right), memory(parent->__rb_parent_color)) by { assumption(); }
                                                    if rb_root_black(usib) == 1 {
                                                        match us.model ensuring {
                                                            owns un: rb_at(tmp);
                                                            fact un.model == usib;
                                                        } {
                                                            RbTree::Node(unid, unp, uncolor, unl, unr) => {
                                                                let { left: ul, right: ur } = unfold(us);
                                                                have rb_root_black(RbTree::Node(unid, unp, uncolor, unl, unr)) == 1 by {
                                                                    rewrite(RbTree::Node(unid, unp, uncolor, unl, unr) == usib);
                                                                    assumption();
                                                                }
                                                                have color_bit(uncolor) == 1 by {
                                                                    apply(rb_root_black_node_color_bit(unid, unp, uncolor, unl, unr)) using {
                                                                        rb_root_black(RbTree::Node(unid, unp, uncolor, unl, unr)) == 1;
                                                                    };
                                                                    assumption();
                                                                }
                                                                have uncolor == Color::Black by {
                                                                    apply(color_bit_one_is_black(uncolor)) using {
                                                                        color_bit(uncolor) == 1;
                                                                    };
                                                                    assumption();
                                                                }
                                                                step();
                                                                have ucolor == Color::Black by {
                                                                    apply(ctx_rb_right_red_focus_black(uid, ugp, ucolor, usib, uup, black_height(t.model))) using {
                                                                        ctx_rb(Context::Right(uid, ugp, ucolor, usib, uup), black_height(t.model), Color::Red) == 1;
                                                                    };
                                                                    assumption();
                                                                }
                                                                have rb_parent_is(RbTree::Node(unid, unp, uncolor, unl, unr), gparent) == 1 by {
                                                                    rewrite(RbTree::Node(unid, unp, uncolor, unl, unr) == usib);
                                                                    assumption();
                                                                }
                                                                have unp == gparent by {
                                                                    apply(rb_parent_is_node_parent(unid, unp, uncolor, unl, unr, gparent)) using {
                                                                        rb_parent_is(RbTree::Node(unid, unp, uncolor, unl, unr), gparent) == 1;
                                                                    };
                                                                    assumption();
                                                                }
                                                                have usib == RbTree::Node(unid, gparent, Color::Black, unl, unr) by {
                                                                    rewrite(usib == RbTree::Node(unid, unp, uncolor, unl, unr));
                                                                    rewrite(unp == gparent);
                                                                    rewrite(uncolor == Color::Black);
                                                                    normalize();
                                                                }
                                                                have (tmp->__rb_parent_color & 1) == color_bit(Color::Black) by {
                                                                    rewrite(Color::Black == uncolor);
                                                                    assumption();
                                                                }
                                                                let un = fold(rb_at(tmp), { model: RbTree::Node(unid, gparent, Color::Black, unl, unr) }, { left: ul, right: ur });
                                                                have un.model == usib by {
                                                                    rewrite(usib == RbTree::Node(unid, gparent, Color::Black, unl, unr));
                                                                    normalize();
                                                                }
                                                            },
                                                            RbTree::Empty => {
                                                                unfold(us);
                                                                step();
                                                                have ucolor == Color::Black by {
                                                                    apply(ctx_rb_right_red_focus_black(uid, ugp, ucolor, usib, uup, black_height(t.model))) using {
                                                                        ctx_rb(Context::Right(uid, ugp, ucolor, usib, uup), black_height(t.model), Color::Red) == 1;
                                                                    };
                                                                    assumption();
                                                                }
                                                                let un = fold(rb_at(tmp), { model: RbTree::Empty });
                                                                have un.model == usib by {
                                                                    rewrite(usib == RbTree::Empty);
                                                                    normalize();
                                                                }
                                                            },
                                                        }
                                                        have cup == Context::Right(gparent, ugp, Color::Black, usib, uup) by {
                                                            rewrite(cup == Context::Right(uid, ugp, ucolor, usib, uup));
                                                            rewrite(ucolor == Color::Black);
                                                            rewrite(uid == gparent);
                                                            normalize();
                                                        }
                                                        have rb_parent_is(RbTree::Node(nid, nparent, ncolor, nleft, nright), parent) == 1 by {
                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                            assumption();
                                                        }
                                                        have nparent == cid by {
                                                            apply(rb_parent_is_node_parent(nid, nparent, ncolor, nleft, nright, parent)) using {
                                                                rb_parent_is(RbTree::Node(nid, nparent, ncolor, nleft, nright), parent) == 1;
                                                            };
                                                            solve();
                                                        }
                                                        have color_bit(ncolor) == 0 by {
                                                            unfold(rb_color_bit(RbTree::Node(nid, nparent, ncolor, nleft, nright)));
                                                            rewrite(color_bit(ncolor) == rb_color_bit(RbTree::Node(nid, nparent, ncolor, nleft, nright)));
                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                            assumption();
                                                        }
                                                        have ncolor == Color::Red by {
                                                            apply(color_bit_zero_is_red(ncolor)) using {
                                                                color_bit(ncolor) == 0;
                                                            };
                                                            assumption();
                                                        }
                                                        have t.model == RbTree::Node(nid, cid, Color::Red, nleft, nright) by {
                                                            rewrite(t.model == RbTree::Node(nid, nparent, ncolor, nleft, nright));
                                                            rewrite(nparent == cid);
                                                            rewrite(ncolor == Color::Red);
                                                            normalize();
                                                        }
                                                        have is_rb(RbTree::Node(nid, cid, Color::Red, nleft, nright)) == 1 by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright) == t.model);
                                                            assumption();
                                                        }
                                                        have ctx_rb(Context::Right(cid, gparent, Color::Red, csib, Context::Right(gparent, ugp, Color::Black, usib, uup)), black_height(RbTree::Node(nid, cid, Color::Red, nleft, nright)), Color::Black) == 1 by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright) == t.model);
                                                            rewrite(Context::Right(gparent, ugp, Color::Black, usib, uup) == cup);
                                                            rewrite(gparent == cgp);
                                                            rewrite(Color::Red == ccolor);
                                                            assumption();
                                                        }
                                                        have rb_parent_consistent(plug(Context::Right(cid, gparent, Color::Red, csib, Context::Right(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright)), 0) == 1 by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright) == t.model);
                                                            rewrite(Context::Right(gparent, ugp, Color::Black, usib, uup) == cup);
                                                            rewrite(gparent == cgp);
                                                            rewrite(Color::Red == ccolor);
                                                            assumption();
                                                        }
                                                        have rb_inorder(plug(Context::Right(cid, gparent, Color::Red, csib, Context::Right(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright))) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright) == t.model);
                                                            rewrite(Context::Right(gparent, ugp, Color::Black, usib, uup) == cup);
                                                            rewrite(gparent == cgp);
                                                            rewrite(Color::Red == ccolor);
                                                            assumption();
                                                        }
                                                        apply(ctx_insert_case3_right_step(ugp, gparent, cid, nid, usib, csib, nleft, nright, uup)) using {
                                                            is_rb(RbTree::Node(nid, cid, Color::Red, nleft, nright)) == 1;
                                                            rb_root_black(usib) == 1;
                                                            ctx_rb(Context::Right(cid, gparent, Color::Red, csib, Context::Right(gparent, ugp, Color::Black, usib, uup)), black_height(RbTree::Node(nid, cid, Color::Red, nleft, nright)), Color::Black) == 1;
                                                            rb_parent_consistent(plug(Context::Right(cid, gparent, Color::Red, csib, Context::Right(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright)), 0) == 1;
                                                        };
                                                        let { left: nl_at, right: nr_at } = unfold(t);
                                                        have (node->__rb_parent_color & 1) == color_bit(Color::Red) by {
                                                            rewrite(Color::Red == ncolor);
                                                            assumption();
                                                        }
                                                        match cs.model ensuring {
                                                            owns sn: rb_at(tmp);
                                                            fact sn.model == rb_reparent(csib, gparent);
                                                            fact ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp;
                                                            fact gparent->rb_left == at(before_uncle_pointer_changes, tmp);
                                                            fact parent->rb_right == node;
                                                        } {
                                                            RbTree::Empty => {
                                                                unfold(cs);
                                                                step();
                                                                step();
                                                                let t = fold(rb_at(node), { model: RbTree::Node(nid, cid, Color::Red, nleft, nright) }, { left: nl_at, right: nr_at });
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                have rb_reparent(csib, gparent) == RbTree::Empty by {
                                                                    rewrite(csib == RbTree::Empty);
                                                                    unfold(rb_reparent(RbTree::Empty, gparent)); normalize();
                                                                }
                                                                let sn = fold(rb_at(tmp), { model: RbTree::Empty });
                                                                have sn.model == rb_reparent(csib, gparent) by {
                                                                    rewrite(rb_reparent(csib, gparent) == RbTree::Empty);
                                                                    solve();
                                                                }
                                                                transport(at(before_grandparent_links, ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp), ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp);
                                                                transport(at(before_uncle_pointer_changes, gparent->rb_left == at(before_uncle_pointer_changes, tmp)), gparent->rb_left == at(before_uncle_pointer_changes, tmp)) using {
                                                                    at(before_uncle_pointer_changes, gparent->rb_left == at(before_uncle_pointer_changes, tmp));
                                                                    separate(memory(gparent->rb_left), memory(gparent->rb_right));
                                                                    separate(memory(gparent->rb_left), memory(parent->rb_left));
                                                                };
                                                                transport(at(before_uncle_pointer_changes, parent->rb_right == node), parent->rb_right == node) using {
                                                                    at(before_uncle_pointer_changes, parent->rb_right == node);
                                                                    separate(memory(parent->rb_right), memory(gparent->rb_right));
                                                                    separate(memory(parent->rb_right), memory(parent->rb_left));
                                                                };
                                                            },
                                                            RbTree::Node(sx, sp, scol, sl, sr) => {
                                                                let { left: sl_at, right: sr_at } = unfold(cs);
                                                                step();
                                                                step();
                                                                step();
                                                                have gparent == uid by { assumption(); }
                                                                have tmp == sx by { assumption(); }
                                                                have separate(memory(gparent->rb_left), memory(tmp->__rb_parent_color)) by { assumption(); }
                                                                have separate(memory(parent->rb_right), memory(tmp->__rb_parent_color)) by { assumption(); }
                                                                have separate(memory(uid->__rb_parent_color), memory(sx->__rb_parent_color)) by { assumption(); }
                                                                have separate(memory(gparent->__rb_parent_color), memory(tmp->__rb_parent_color)) by {
                                                                    rewrite(gparent == uid);
                                                                    rewrite(tmp == sx);
                                                                    assumption();
                                                                }
                                                                let t = fold(rb_at(node), { model: RbTree::Node(nid, cid, Color::Red, nleft, nright) }, { left: nl_at, right: nr_at });
                                                                have rb_root_black(RbTree::Node(sx, sp, scol, sl, sr)) == 1 by {
                                                                    rewrite(RbTree::Node(sx, sp, scol, sl, sr) == csib);
                                                                    assumption();
                                                                }
                                                                have color_bit(scol) == 1 by {
                                                                    apply(rb_root_black_node_color_bit(sx, sp, scol, sl, sr)) using {
                                                                        rb_root_black(RbTree::Node(sx, sp, scol, sl, sr)) == 1;
                                                                    };
                                                                    assumption();
                                                                }
                                                                have rb_reparent(csib, gparent) == RbTree::Node(sx, gparent, scol, sl, sr) by {
                                                                    rewrite(csib == RbTree::Node(sx, sp, scol, sl, sr));
                                                                    unfold(rb_reparent(RbTree::Node(sx, sp, scol, sl, sr), gparent)); normalize();
                                                                }
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                let sn = fold(rb_at(tmp), { model: RbTree::Node(sx, gparent, scol, sl, sr) }, { left: sl_at, right: sr_at });
                                                                have sn.model == rb_reparent(csib, gparent) by {
                                                                    rewrite(rb_reparent(csib, gparent) == RbTree::Node(sx, gparent, scol, sl, sr));
                                                                    solve();
                                                                }
                                                                transport(at(before_grandparent_links, ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp), ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp);
                                                                transport(at(before_uncle_pointer_changes, gparent->rb_left == at(before_uncle_pointer_changes, tmp)), gparent->rb_left == at(before_uncle_pointer_changes, tmp)) using {
                                                                    at(before_uncle_pointer_changes, gparent->rb_left == at(before_uncle_pointer_changes, tmp));
                                                                    separate(memory(gparent->rb_left), memory(gparent->rb_right));
                                                                    separate(memory(gparent->rb_left), memory(parent->rb_left));
                                                                    separate(memory(gparent->rb_left), memory(tmp->__rb_parent_color));
                                                                };
                                                                transport(at(before_uncle_pointer_changes, parent->rb_right == node), parent->rb_right == node) using {
                                                                    at(before_uncle_pointer_changes, parent->rb_right == node);
                                                                    separate(memory(parent->rb_right), memory(gparent->rb_right));
                                                                    separate(memory(parent->rb_right), memory(parent->rb_left));
                                                                    separate(memory(parent->rb_right), memory(tmp->__rb_parent_color));
                                                                };
                                                            },
                                                        }
                                                        transport(at(before_grandparent_links, ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp), ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp);
                                                        have (gparent->__rb_parent_color & 1) == 1 by {
                                                            rewrite((gparent->__rb_parent_color & 1) == color_bit(ucolor));
                                                            rewrite(ucolor == Color::Black);
                                                            unfold(color_bit(Color::Black));
                                                            solve();
                                                        }
                                                        mark before_rotation_parent_changes;
                                                        have at(before_rotation_parent_changes, gparent->rb_left == at(before_uncle_pointer_changes, tmp)) by { assumption(); }
                                                        have at(before_rotation_parent_changes, parent->rb_right == node) by { assumption(); }
                                                        match uu.model ensuring {
                                                            owns uu: ctx_at(parent, root);
                                                            fact uu.model == uup;
                                                            fact gparent->rb_left == at(before_uncle_pointer_changes, tmp);
                                                            fact parent->rb_right == node;
                                                        } {
                                                            Context::Top => {
                                                                have ctx_node_is(Context::Top, ugp) == 1 by {
                                                                    rewrite(Context::Top == uu.model);
                                                                    rewrite(uu.model == uup);
                                                                    assumption();
                                                                }
                                                                have ugp == 0 by {
                                                                    apply(ctx_node_is_top_null(ugp)) using {
                                                                        ctx_node_is(Context::Top, ugp) == 1;
                                                                    };
                                                                    assumption();
                                                                }
                                                                unfold(uu);
                                                                have separate(memory(gparent->rb_left), memory(root->rb_node)) by { assumption(); }
                                                                have separate(memory(parent->rb_right), memory(root->rb_node)) by { assumption(); }
                                                                step();
                                                                transport(at(before_rotation_parent_changes, gparent->rb_left == at(before_uncle_pointer_changes, tmp)), gparent->rb_left == at(before_uncle_pointer_changes, tmp)) using {
                                                                    at(before_rotation_parent_changes, gparent->rb_left == at(before_uncle_pointer_changes, tmp));
                                                                    separate(memory(gparent->rb_left), memory(gparent->__rb_parent_color));
                                                                    separate(memory(gparent->rb_left), memory(parent->__rb_parent_color));
                                                                    separate(memory(gparent->rb_left), memory(root->rb_node));
                                                                };
                                                                transport(at(before_rotation_parent_changes, parent->rb_right == node), parent->rb_right == node) using {
                                                                    at(before_rotation_parent_changes, parent->rb_right == node);
                                                                    separate(memory(parent->rb_right), memory(gparent->__rb_parent_color));
                                                                    separate(memory(parent->rb_right), memory(parent->__rb_parent_color));
                                                                    separate(memory(parent->rb_right), memory(root->rb_node));
                                                                };
                                                                let uu = fold(ctx_at(parent, root), { model: Context::Top });
                                                                have uu.model == uup by { rewrite(uup == Context::Top); normalize(); }
                                                            },
                                                            Context::Left(xid, xgp, xcol, xsib, xup) => {
                                                                have ctx_node_is(Context::Left(xid, xgp, xcol, xsib, xup), ugp) == 1 by {
                                                                    rewrite(Context::Left(xid, xgp, xcol, xsib, xup) == uu.model);
                                                                    rewrite(uu.model == uup);
                                                                    assumption();
                                                                }
                                                                have ugp == xid by {
                                                                    apply(ctx_node_is_left_identity(xid, xgp, xcol, xsib, xup, ugp)) using {
                                                                        ctx_node_is(Context::Left(xid, xgp, xcol, xsib, xup), ugp) == 1;
                                                                    };
                                                                    assumption();
                                                                }
                                                                let { sibling: xs, up: xu } = unfold(uu);
                                                                have separate(memory(gparent->rb_left), memory(xid->rb_right)) by { assumption(); }
                                                                have separate(memory(parent->rb_right), memory(xid->rb_right)) by { assumption(); }
                                                                have separate(memory(gparent->rb_left), memory(xid->rb_left)) by { assumption(); }
                                                                have separate(memory(parent->rb_right), memory(xid->rb_left)) by { assumption(); }
                                                                step();
                                                                transport(at(before_rotation_parent_changes, gparent->rb_left == at(before_uncle_pointer_changes, tmp)), gparent->rb_left == at(before_uncle_pointer_changes, tmp)) using {
                                                                    at(before_rotation_parent_changes, gparent->rb_left == at(before_uncle_pointer_changes, tmp));
                                                                    separate(memory(gparent->rb_left), memory(gparent->__rb_parent_color));
                                                                    separate(memory(gparent->rb_left), memory(parent->__rb_parent_color));
                                                                    separate(memory(gparent->rb_left), memory(xid->rb_right));
                                                                    separate(memory(gparent->rb_left), memory(xid->rb_left));
                                                                };
                                                                transport(at(before_rotation_parent_changes, parent->rb_right == node), parent->rb_right == node) using {
                                                                    at(before_rotation_parent_changes, parent->rb_right == node);
                                                                    separate(memory(parent->rb_right), memory(gparent->__rb_parent_color));
                                                                    separate(memory(parent->rb_right), memory(parent->__rb_parent_color));
                                                                    separate(memory(parent->rb_right), memory(xid->rb_right));
                                                                    separate(memory(parent->rb_right), memory(xid->rb_left));
                                                                };
                                                                let uu = fold(ctx_at(parent, root), { model: Context::Left(xid, xgp, xcol, xsib, xup) }, { sibling: xs, up: xu });
                                                                have uu.model == uup by { rewrite(uup == Context::Left(xid, xgp, xcol, xsib, xup)); normalize(); }
                                                            },
                                                            Context::Right(xid, xgp, xcol, xsib, xup) => {
                                                                have ctx_node_is(Context::Right(xid, xgp, xcol, xsib, xup), ugp) == 1 by {
                                                                    rewrite(Context::Right(xid, xgp, xcol, xsib, xup) == uu.model);
                                                                    rewrite(uu.model == uup);
                                                                    assumption();
                                                                }
                                                                have ugp == xid by {
                                                                    apply(ctx_node_is_right_identity(xid, xgp, xcol, xsib, xup, ugp)) using {
                                                                        ctx_node_is(Context::Right(xid, xgp, xcol, xsib, xup), ugp) == 1;
                                                                    };
                                                                    assumption();
                                                                }
                                                                let { sibling: xs, up: xu } = unfold(uu);
                                                                have separate(memory(gparent->rb_left), memory(xid->rb_right)) by { assumption(); }
                                                                have separate(memory(parent->rb_right), memory(xid->rb_right)) by { assumption(); }
                                                                have separate(memory(gparent->rb_left), memory(xid->rb_left)) by { assumption(); }
                                                                have separate(memory(parent->rb_right), memory(xid->rb_left)) by { assumption(); }
                                                                mark before_upper_child_change;
                                                                have at(before_upper_child_change, ((xid->__rb_parent_color & ~3) as (struct rb_node *)) == xgp) by { assumption(); }
                                                                have separate(memory(xid->__rb_parent_color), memory(gparent->__rb_parent_color)) by { assumption(); }
                                                                have separate(memory(xid->__rb_parent_color), memory(parent->__rb_parent_color)) by { assumption(); }
                                                                have separate(memory(xid->__rb_parent_color), memory(xid->rb_right)) by { assumption(); }
                                                                have separate(memory(xid->__rb_parent_color), memory(xid->rb_left)) by { assumption(); }
                                                                match xsib ensuring {
                                                                    owns xs: rb_at(xid->rb_left);
                                                                    fact xs.model == xsib;
                                                                    fact gparent->rb_left == at(before_uncle_pointer_changes, tmp);
                                                                    fact parent->rb_right == node;
                                                                    fact ((xid->__rb_parent_color & ~3) as (struct rb_node *)) == xgp;
                                                                } {
                                                                    RbTree::Empty => {
                                                                        unfold(xs);
                                                                        step();
                                                                        transport(at(before_rotation_parent_changes, gparent->rb_left == at(before_uncle_pointer_changes, tmp)), gparent->rb_left == at(before_uncle_pointer_changes, tmp)) using {
                                                                            at(before_rotation_parent_changes, gparent->rb_left == at(before_uncle_pointer_changes, tmp));
                                                                            separate(memory(gparent->rb_left), memory(gparent->__rb_parent_color));
                                                                            separate(memory(gparent->rb_left), memory(parent->__rb_parent_color));
                                                                                    separate(memory(gparent->rb_left), memory(xid->rb_right));
                                                                            separate(memory(gparent->rb_left), memory(xid->rb_left));
                                                                        };
                                                                        transport(at(before_rotation_parent_changes, parent->rb_right == node), parent->rb_right == node) using {
                                                                            at(before_rotation_parent_changes, parent->rb_right == node);
                                                                            separate(memory(parent->rb_right), memory(gparent->__rb_parent_color));
                                                                            separate(memory(parent->rb_right), memory(parent->__rb_parent_color));
                                                                            separate(memory(parent->rb_right), memory(xid->rb_right));
                                                                            separate(memory(parent->rb_right), memory(xid->rb_left));
                                                                        };
                                                                        let xs = fold(rb_at(0), { model: xsib });
                                                                        transport(at(before_upper_child_change, ((xid->__rb_parent_color & ~3) as (struct rb_node *)) == xgp), ((xid->__rb_parent_color & ~3) as (struct rb_node *)) == xgp);
                                                                    },
                                                                    RbTree::Node(yid, yp, ycol, yl, yr) => {
                                                                        let { left: yl_at, right: yr_at } = unfold(xs);
                                                                        step();
                                                                        transport(at(before_rotation_parent_changes, gparent->rb_left == at(before_uncle_pointer_changes, tmp)), gparent->rb_left == at(before_uncle_pointer_changes, tmp)) using {
                                                                            at(before_rotation_parent_changes, gparent->rb_left == at(before_uncle_pointer_changes, tmp));
                                                                            separate(memory(gparent->rb_left), memory(gparent->__rb_parent_color));
                                                                            separate(memory(gparent->rb_left), memory(parent->__rb_parent_color));
                                                                                    separate(memory(gparent->rb_left), memory(xid->rb_right));
                                                                            separate(memory(gparent->rb_left), memory(xid->rb_left));
                                                                        };
                                                                        transport(at(before_rotation_parent_changes, parent->rb_right == node), parent->rb_right == node) using {
                                                                            at(before_rotation_parent_changes, parent->rb_right == node);
                                                                            separate(memory(parent->rb_right), memory(gparent->__rb_parent_color));
                                                                            separate(memory(parent->rb_right), memory(parent->__rb_parent_color));
                                                                            separate(memory(parent->rb_right), memory(xid->rb_right));
                                                                            separate(memory(parent->rb_right), memory(xid->rb_left));
                                                                        };
                                                                        let xs = fold(rb_at(yid), { model: xsib }, { left: yl_at, right: yr_at });
                                                                        transport(at(before_upper_child_change, ((xid->__rb_parent_color & ~3) as (struct rb_node *)) == xgp), ((xid->__rb_parent_color & ~3) as (struct rb_node *)) == xgp);
                                                                    },
                                                                }
                                                                let uu = fold(ctx_at(parent, root), { model: Context::Right(xid, xgp, xcol, xsib, xup) }, { sibling: xs, up: xu });
                                                                have uu.model == uup by { rewrite(uup == Context::Right(xid, xgp, xcol, xsib, xup)); normalize(); }
                                                            },
                                                        }
                                                            have rb_parent_is(rb_reparent(csib, gparent), gparent) == 1 by {
                                                                apply(rb_reparent_parent_is(csib, gparent));
                                                                assumption();
                                                            }
                                                            let gn = fold(rb_at(gparent), { model: RbTree::Node(gparent, cid, Color::Red, usib, rb_reparent(csib, gparent)) }, { left: un, right: sn });
                                                            have rb_parent_is(RbTree::Node(gparent, cid, Color::Red, usib, rb_reparent(csib, gparent)), cid) == 1 by {
                                                                unfold(rb_parent_is(RbTree::Node(gparent, cid, Color::Red, usib, rb_reparent(csib, gparent)), cid));
                                                            }
                                                            have (parent->__rb_parent_color & 1) == color_bit(Color::Black) by {
                                                                unfold(color_bit(Color::Black));
                                                                solve();
                                                            }
                                                        let c = fold(ctx_at(node, root), { model: Context::Right(cid, ugp, Color::Black, RbTree::Node(gparent, cid, Color::Red, usib, rb_reparent(csib, gparent)), uup) }, { sibling: gn, up: uu });
                                                        have rb_inorder(plug(c.model, t.model)) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                                            rewrite(c.model == Context::Right(cid, ugp, Color::Black, RbTree::Node(gparent, cid, Color::Red, usib, rb_reparent(csib, gparent)), uup));
                                                            rewrite(t.model == RbTree::Node(nid, cid, Color::Red, nleft, nright));
                                                            rewrite(rb_inorder(plug(Context::Right(cid, ugp, Color::Black, RbTree::Node(gparent, cid, Color::Red, usib, rb_reparent(csib, gparent)), uup), RbTree::Node(nid, cid, Color::Red, nleft, nright))) == rb_inorder(plug(Context::Right(cid, gparent, Color::Red, csib, Context::Right(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright))));
                                                            assumption();
                                                        }
                                                        have rb_tree_parent_consistent(plug(c.model, t.model)) == 1 by {
                                                            unfold(rb_tree_parent_consistent(plug(c.model, t.model)));
                                                        }
                                                        step();
                                                        step();
                                                    } else {
                                                        match us.model {
                                                            RbTree::Node(unid, unp, uncolor, unl, unr) => {
                                                                let { left: ul, right: ur } = unfold(us);
                                                                match uncolor {
                                                                    Color::Red => {
                                                                        have (tmp->__rb_parent_color & 1) == 0 by {
                                                                            rewrite((tmp->__rb_parent_color & 1) == color_bit(uncolor));
                                                                            rewrite(uncolor == Color::Red);
                                                                            unfold(color_bit(Color::Red));
                                                                            solve();
                                                                        }
                                                                        have ucolor == Color::Black by {
                                                                            apply(ctx_rb_right_red_focus_black(uid, ugp, ucolor, usib, uup, black_height(t.model))) using {
                                                                                ctx_rb(Context::Right(uid, ugp, ucolor, usib, uup), black_height(t.model), Color::Red) == 1;
                                                                            };
                                                                            assumption();
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(unid, unp, uncolor, unl, unr), gparent) == 1 by {
                                                                            rewrite(RbTree::Node(unid, unp, uncolor, unl, unr) == usib);
                                                                            assumption();
                                                                        }
                                                                        have unp == gparent by {
                                                                            apply(rb_parent_is_node_parent(unid, unp, uncolor, unl, unr, gparent)) using {
                                                                                rb_parent_is(RbTree::Node(unid, unp, uncolor, unl, unr), gparent) == 1;
                                                                            };
                                                                            assumption();
                                                                        }
                                                                        have usib == RbTree::Node(unid, gparent, Color::Red, unl, unr) by {
                                                                            rewrite(usib == RbTree::Node(unid, unp, uncolor, unl, unr));
                                                                            rewrite(unp == gparent);
                                                                            rewrite(uncolor == Color::Red);
                                                                            normalize();
                                                                        }
                                                                        have cup == Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup) by {
                                                                            rewrite(cup == Context::Right(uid, ugp, ucolor, usib, uup));
                                                                            rewrite(usib == RbTree::Node(unid, gparent, Color::Red, unl, unr));
                                                                            rewrite(ucolor == Color::Black);
                                                                            rewrite(uid == gparent);
                                                                            normalize();
                                                                        }
                                                                        have almost_rb_insert(RbTree::Node(cid, cgp, Color::Red, csib, t.model)) == 1 by {
                                                                            apply(ctx_insert_cursor_right_parent(cid, cgp, t.model, csib, cup)) using {
                                                                                is_rb(t.model) == 1;
                                                                                ctx_rb(Context::Right(cid, cgp, Color::Red, csib, cup), black_height(t.model), Color::Black) == 1;
                                                                            };
                                                                            assumption();
                                                                        }
                                                                        have almost_rb_insert(RbTree::Node(cid, gparent, Color::Red, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright))) == 1 by {
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                                            rewrite(gparent == cgp);
                                                                            assumption();
                                                                        }
                                                                        have black_height(csib) == black_height(t.model) by {
                                                                            apply(ctx_insert_cursor_right_parent(cid, cgp, t.model, csib, cup)) using {
                                                                                is_rb(t.model) == 1;
                                                                                ctx_rb(Context::Right(cid, cgp, Color::Red, csib, cup), black_height(t.model), Color::Black) == 1;
                                                                            };
                                                                            assumption();
                                                                        }
                                                                        apply(ctx_insert_case1_right_step(ugp, gparent, cid, unid, unl, unr, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright), uup)) using {
                                                                            almost_rb_insert(RbTree::Node(cid, gparent, Color::Red, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright))) == 1;
                                                                            ctx_rb(Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), black_height(csib), Color::Red) == 1;
                                                                        };
                                                                        have rb_inorder(plug(Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), RbTree::Node(cid, gparent, Color::Red, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)))) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                                                            apply(plug_right_frame(cid, cgp, ccolor, csib, cup, t.model));
                                                                            rewrite(Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup) == cup);
                                                                            rewrite(gparent == cgp);
                                                                            rewrite(Color::Red == ccolor);
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                                            rewrite(plug(cup, RbTree::Node(cid, cgp, ccolor, csib, t.model))
                                                                                == plug(Context::Right(cid, cgp, ccolor, csib, cup), t.model));
                                                                            assumption();
                                                                        }
                                                                        have rb_parent_consistent(plug(Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), RbTree::Node(cid, gparent, Color::Red, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright))), 0) == 1 by {
                                                                            apply(plug_right_frame(cid, cgp, ccolor, csib, cup, t.model));
                                                                            rewrite(Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup) == cup);
                                                                            rewrite(gparent == cgp);
                                                                            rewrite(Color::Red == ccolor);
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                                            rewrite(plug(cup, RbTree::Node(cid, cgp, ccolor, csib, t.model))
                                                                                == plug(Context::Right(cid, cgp, ccolor, csib, cup), t.model));
                                                                            assumption();
                                                                        }
                                                                        have rb_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)))), 0) == 1 by {
                                                                            rewrite(rb_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)))), 0)
                                                                                == rb_parent_consistent(plug(Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), RbTree::Node(cid, gparent, Color::Red, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright))), 0));
                                                                            assumption();
                                                                        }
                                                                        have rb_tree_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright))))) == 1 by {
                                                                            unfold(rb_tree_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright))))));
                                                                        }
                                                                        have rb_color_bit(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)))) == 0 by {
                                                                            unfold(rb_color_bit(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)))));
                                                                            unfold(color_bit(Color::Red));
                                                                            normalize();
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(nid, nparent, ncolor, nleft, nright), parent) == 1 by {
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                                            assumption();
                                                                        }
                                                                        have color_bit(Color::Black) == 1 by {
                                                                            unfold(color_bit(Color::Black));
                                                                            normalize();
                                                                        }
                                                                        have color_bit(Color::Red) == 0 by {
                                                                            unfold(color_bit(Color::Red));
                                                                            normalize();
                                                                        }
                                                                        mark before_recolor_tags_4;
                                                                        have at(before_recolor_tags_4, gparent->rb_left == tmp) by { assumption(); }
                                                                        have at(before_recolor_tags_4, separate(memory(gparent->rb_left), memory(gparent->__rb_parent_color))) by { assumption(); }
                                                                        have at(before_recolor_tags_4, separate(memory(gparent->rb_left), memory(parent->__rb_parent_color))) by { assumption(); }
                                                                        have at(before_recolor_tags_4, separate(memory(gparent->rb_left), memory(tmp->__rb_parent_color))) by { assumption(); }
                                                                        have at(before_recolor_tags_4, gparent->rb_right == parent) by { assumption(); }
                                                                        have at(before_recolor_tags_4, separate(memory(gparent->rb_right), memory(gparent->__rb_parent_color))) by { assumption(); }
                                                                        have at(before_recolor_tags_4, separate(memory(gparent->rb_right), memory(parent->__rb_parent_color))) by { assumption(); }
                                                                        have at(before_recolor_tags_4, separate(memory(gparent->rb_right), memory(tmp->__rb_parent_color))) by { assumption(); }
                                                                        step();
                                                                        step();
                                                                        step();
                                                                        let un = fold(rb_at(tmp), { model: RbTree::Node(unid, gparent, Color::Black, unl, unr) }, { left: ul, right: ur });
                                                                        let pn = fold(rb_at(parent), { model: RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)) }, { left: cs, right: t });
                                                                        step();
                                                                        step();
                                                                        step();
                                                                        have rb_parent_is(RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)), gparent) == 1 by {
                                                                            unfold(rb_parent_is(RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)), gparent));
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(unid, gparent, Color::Black, unl, unr), gparent) == 1 by {
                                                                            unfold(rb_parent_is(RbTree::Node(unid, gparent, Color::Black, unl, unr), gparent));
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright))), ugp) == 1 by {
                                                                            unfold(rb_parent_is(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright))), ugp));
                                                                        }
                                                                        transport(at(before_recolor_tags_4, gparent->rb_left == tmp), gparent->rb_left == at(before_recolor_tags_4, tmp)) using {
                                                                            at(before_recolor_tags_4, gparent->rb_left == tmp);
                                                                            at(before_recolor_tags_4, separate(memory(gparent->rb_left), memory(gparent->__rb_parent_color)));
                                                                            at(before_recolor_tags_4, separate(memory(gparent->rb_left), memory(parent->__rb_parent_color)));
                                                                            at(before_recolor_tags_4, separate(memory(gparent->rb_left), memory(tmp->__rb_parent_color)));
                                                                        };
                                                                        transport(at(before_recolor_tags_4, gparent->rb_right == parent), gparent->rb_right == at(before_recolor_tags_4, parent)) using {
                                                                            at(before_recolor_tags_4, gparent->rb_right == parent);
                                                                            at(before_recolor_tags_4, separate(memory(gparent->rb_right), memory(gparent->__rb_parent_color)));
                                                                            at(before_recolor_tags_4, separate(memory(gparent->rb_right), memory(parent->__rb_parent_color)));
                                                                            at(before_recolor_tags_4, separate(memory(gparent->rb_right), memory(tmp->__rb_parent_color)));
                                                                        };
                                                                        let gn = fold(rb_at(gparent), { model: RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright))) }, { left: un, right: pn });
                                                                    },
                                                                    Color::Black => {
                                                                        have rb_root_black(usib) == 1 by {
                                                                            rewrite(usib == RbTree::Node(unid, unp, uncolor, unl, unr));
                                                                            rewrite(uncolor == Color::Black);
                                                                            apply(rb_root_black_black_node(unid, unp, unl, unr));
                                                                            assumption();
                                                                        }
                                                                        contradiction(rb_root_black(usib) == 1);
                                                                    },
                                                                }
                                                            },
                                                            RbTree::Empty => {
                                                                have rb_root_black(usib) == 1 by {
                                                                    rewrite(usib == RbTree::Empty);
                                                                    unfold(rb_root_black(RbTree::Empty)); normalize();
                                                                }
                                                                contradiction(rb_root_black(usib) == 1);
                                                            },
                                                        }
                                                    }
                                                },
                                                }
                                            },
                                        }
                                    },
                                }
                            }
                        },
                    }
                }
            }
            have rb_inorder(plug(c.model, t.model)) == rb_inorder(plug(old(c.model), old(t.model))) by {
                rewrite(old(t.model) == RbTree::Node(identity, node_parent, color, left_model, right_model));
                assumption();
            }
            mark refold;
            let { whole: tree } = refold_to_root(node, root, { c: c, t: t });
            have rb_inorder(tree.model) == rb_inorder(plug(old(c.model), old(t.model))) by {
                rewrite(tree.model == at(refold, plug(c.model, t.model)));
                assumption();
            }
            have is_rb_root(tree.model) == 1 by {
                rewrite(tree.model == at(refold, plug(c.model, t.model)));
                assumption();
            }
            have rb_tree_parent_consistent(tree.model) == 1 by {
                rewrite(tree.model == at(refold, plug(c.model, t.model)));
                assumption();
            }
            step();
            solve();
        },
    }
}

void rb_insert_color(struct rb_node* node, struct rb_root* root) {
    consumes c: ctx_at(node, root);
    consumes t: rb_at(node);
    requires t.model != RbTree::Empty;
    requires rb_color_bit(t.model) == 0;
    requires ctx_holds(c.model, t.model) == 1;
    requires is_rb(t.model) == 1;
    requires ctx_almost_rb_insert(c.model, black_height(t.model)) == 1;
    requires rb_tree_parent_consistent(plug(c.model, t.model)) == 1;
    produces tree: rb_root_at(root);
    ensures rb_inorder(tree.model) == rb_inorder(plug(old(c.model), old(t.model)));
    ensures is_rb_root(tree.model) == 1;
    ensures rb_tree_parent_consistent(tree.model) == 1;
} by {
    let { tree: tree } = step(__rb_insert, { c: c, t: t });
    step();
    solve();
}
