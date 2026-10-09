verifying "rb_erase_color.c";
import "../rbtree-model/rbtree_spine_resources.click";

# Repeated case-2 color flips with either orientation at every ancestor.
# Black parents propagate to their strict outer context; a red parent or
# the root ends the loop. The selector leaves every rotation in the pinned C
# while specifying exactly which paths this sidecar verifies.

function erase_flips(ctx: Context) -> int32
    decreases ctx
{
    match ctx {
        Context::Top => 1,
        Context::Right(id, above, pc, sibling, up) =>
        match sibling {
            RbTree::Empty => 0,
            RbTree::Node(sid, sp, sc, sr, sl) =>
            if sc == Color::Black {
                if rb_root_black(sl) == 1 {
                    if rb_root_black(sr) == 1 {
                        match pc {
                            Color::Red => 1,
                            Color::Black => erase_flips(up),
                        }
                    } else { 0 }
                } else { 0 }
            } else { 0 },
        },
        Context::Left(id, above, pc, sibling, up) =>
        match sibling {
            RbTree::Empty => 0,
            RbTree::Node(sid, sp, sc, sl, sr) =>
            if sc == Color::Black {
                if rb_root_black(sl) == 1 {
                    if rb_root_black(sr) == 1 {
                        match pc {
                            Color::Red => 1,
                            Color::Black => erase_flips(up),
                        }
                    } else { 0 }
                } else { 0 }
            } else { 0 },
        },
    }
}

function erase_flips_result(ctx: Context, focus: RbTree) -> RbTree
    decreases ctx
{
    match ctx {
        Context::Top => focus,
        Context::Right(id, above, pc, sibling, up) =>
        match pc {
            Color::Red => plug(up, RbTree::Node(id, above, Color::Black, rb_recolor(sibling, Color::Red), focus)),
            Color::Black => erase_flips_result(up, RbTree::Node(id, above, Color::Black, rb_recolor(sibling, Color::Red), focus)),
        },
        Context::Left(id, above, pc, sibling, up) =>
        match pc {
            Color::Red => plug(up, RbTree::Node(id, above, Color::Black, focus, rb_recolor(sibling, Color::Red))),
            Color::Black => erase_flips_result(up, RbTree::Node(id, above, Color::Black, focus, rb_recolor(sibling, Color::Red))),
        },
    }
}

theorem ctx_node_is_left_identity(cid: struct rb_node*, grandparent: struct rb_node*,
                                  ccolor: Color, sibling_model: RbTree, up_model: Context,
                                  p: struct rb_node*) {
    requires ctx_node_is(Context::Left(cid, grandparent, ccolor, sibling_model, up_model),
        p) == 1;

    ensures p == cid by {
        if p == cid {
            assumption();
        } else {
            have ctx_node_is(
                Context::Left(cid, grandparent, ccolor, sibling_model, up_model), p) != 1 by {
                unfold(ctx_node_is(
                    Context::Left(cid, grandparent, ccolor, sibling_model, up_model), p));
                normalize() using { not(p == cid); }
            }
            contradiction(ctx_node_is(
                Context::Left(cid, grandparent, ccolor, sibling_model, up_model), p) == 1);
        }
    }
}

theorem ctx_node_is_right_identity(cid: struct rb_node*, grandparent: struct rb_node*,
                                   ccolor: Color, sibling_model: RbTree, up_model: Context,
                                   p: struct rb_node*) {
    requires ctx_node_is(Context::Right(cid, grandparent, ccolor, sibling_model, up_model),
        p) == 1;

    ensures p == cid by {
        if p == cid {
            assumption();
        } else {
            have ctx_node_is(
                Context::Right(cid, grandparent, ccolor, sibling_model, up_model), p) != 1 by {
                unfold(ctx_node_is(
                    Context::Right(cid, grandparent, ccolor, sibling_model, up_model), p));
                normalize() using { not(p == cid); }
            }
            contradiction(ctx_node_is(
                Context::Right(cid, grandparent, ccolor, sibling_model, up_model), p) == 1);
        }
    }
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
                normalize() using { not(p == cid); }
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
                normalize() using { not(p == cid); }
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

    ensures p == 0 by {
        if p == 0 {
            assumption();
        } else {
            have ctx_node_is(Context::Top, p) != 1 by {
                unfold(ctx_node_is(Context::Top, p));
                normalize() using { not(p == 0); }
            }
            contradiction(ctx_node_is(Context::Top, p) == 1);
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
                arithmetic() using { 0 <= ctx_depth(up_model); }
            }
            Context::Right(identity, grandparent, color, sibling_model, up_model) => {
                apply(ih(up_model));
                unfold(ctx_depth(Context::Right(identity, grandparent, color, sibling_model, up_model)));
                arithmetic() using { 0 <= ctx_depth(up_model); }
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
            have plug(Context::Top, old(t.model)) == old(t.model) by {
                unfold(plug(Context::Top, old(t.model)));
                normalize();
            }
            have whole.model == plug(old(c.model), old(t.model)) by {
                rewrite(old(c.model) == Context::Top);
                rewrite(plug(Context::Top, old(t.model)) == old(t.model));
                simp();
            }
        },
        Context::Left(identity, grandparent, color, sibling_model, up_model) => {
            have rb_parent_consistent(plug(Context::Left(identity, grandparent, color, sibling_model, up_model), t.model), 0) == 1 by {
                rewrite(Context::Left(identity, grandparent, color, sibling_model, up_model) == c.model);
                have rb_parent_consistent(plug(c.model, t.model), 0)
                == rb_tree_parent_consistent(plug(c.model, t.model)) by {
                    unfold(rb_tree_parent_consistent(plug(c.model, t.model)));
                    normalize();
                }
                rewrite(rb_parent_consistent(plug(c.model, t.model), 0)
                    == rb_tree_parent_consistent(plug(c.model, t.model)));
                assumption();
            }
            apply(plug_parent_consistent_ctx(Context::Left(identity, grandparent, color, sibling_model, up_model), t.model, 0)) using {
                rb_parent_consistent(plug(Context::Left(identity, grandparent, color, sibling_model, up_model), t.model), 0) == 1;
            }
            apply(ctx_consistent_left_focus(identity, grandparent, color, sibling_model, up_model, t.model, 0)) using {
                ctx_consistent(Context::Left(identity, grandparent, color, sibling_model, up_model), t.model, 0) == 1;
            }
            apply(erase_parent_consistent_parent_is(t.model, identity)) using {
                rb_parent_consistent(t.model, identity) == 1;
            }
            let { sibling: s, up: u } = unfold(c);
            let sub = fold(rb_at(identity), { model: RbTree::Node(identity, grandparent, color, old(t.model), sibling_model) }, { left: t, right: s });
            apply(ctx_depth_is_nonnegative(up_model));
            have 0 <= ctx_depth(u.model) by {
                rewrite(u.model == up_model);
                assumption();
            }
            have ctx_depth(old(c.model)) == ctx_depth(up_model) + 1 by {
                rewrite(old(c.model) == Context::Left(identity, grandparent, color, sibling_model, up_model));
                unfold(ctx_depth(Context::Left(identity, grandparent, color, sibling_model, up_model)));
                normalize();
            }
            have ctx_depth(u.model) < ctx_depth(old(c.model)) by {
                rewrite(u.model == up_model);
                arithmetic() using { ctx_depth(old(c.model)) == ctx_depth(up_model) + 1; }
            }
            have plug(Context::Left(identity, grandparent, color, sibling_model, up_model), old(t.model)) == plug(up_model, RbTree::Node(identity, grandparent, color, old(t.model), sibling_model)) by {
                unfold(plug(Context::Left(identity, grandparent, color, sibling_model, up_model), old(t.model)));
                normalize();
            }
            have rb_tree_parent_consistent(plug(u.model, sub.model)) == 1 by {
                rewrite(u.model == up_model);
                rewrite(sub.model == RbTree::Node(identity, grandparent, color, old(t.model), sibling_model));
                rewrite(plug(up_model, RbTree::Node(identity, grandparent, color, old(t.model), sibling_model)) == plug(Context::Left(identity, grandparent, color, sibling_model, up_model), old(t.model)));
                rewrite(Context::Left(identity, grandparent, color, sibling_model, up_model) == old(c.model));
                assumption();
            }
            let { whole: whole } = refold_to_root(identity, root, { c: u, t: sub });
            have whole.model == plug(old(c.model), old(t.model)) by {
                rewrite(old(c.model) == Context::Left(identity, grandparent, color, sibling_model, up_model));
                rewrite(plug(Context::Left(identity, grandparent, color, sibling_model, up_model), old(t.model)) == plug(up_model, RbTree::Node(identity, grandparent, color, old(t.model), sibling_model)));
                simp();
            }
        },
        Context::Right(identity, grandparent, color, sibling_model, up_model) => {
            have rb_parent_consistent(plug(Context::Right(identity, grandparent, color, sibling_model, up_model), t.model), 0) == 1 by {
                rewrite(Context::Right(identity, grandparent, color, sibling_model, up_model) == c.model);
                have rb_parent_consistent(plug(c.model, t.model), 0)
                == rb_tree_parent_consistent(plug(c.model, t.model)) by {
                    unfold(rb_tree_parent_consistent(plug(c.model, t.model)));
                    normalize();
                }
                rewrite(rb_parent_consistent(plug(c.model, t.model), 0)
                    == rb_tree_parent_consistent(plug(c.model, t.model)));
                assumption();
            }
            apply(plug_parent_consistent_ctx(Context::Right(identity, grandparent, color, sibling_model, up_model), t.model, 0)) using {
                rb_parent_consistent(plug(Context::Right(identity, grandparent, color, sibling_model, up_model), t.model), 0) == 1;
            }
            apply(ctx_consistent_right_focus(identity, grandparent, color, sibling_model, up_model, t.model, 0)) using {
                ctx_consistent(Context::Right(identity, grandparent, color, sibling_model, up_model), t.model, 0) == 1;
            }
            apply(erase_parent_consistent_parent_is(t.model, identity)) using {
                rb_parent_consistent(t.model, identity) == 1;
            }
            let { sibling: s, up: u } = unfold(c);
            let sub = fold(rb_at(identity), { model: RbTree::Node(identity, grandparent, color, sibling_model, old(t.model)) }, { left: s, right: t });
            apply(ctx_depth_is_nonnegative(up_model));
            have 0 <= ctx_depth(u.model) by {
                rewrite(u.model == up_model);
                assumption();
            }
            have ctx_depth(old(c.model)) == ctx_depth(up_model) + 1 by {
                rewrite(old(c.model) == Context::Right(identity, grandparent, color, sibling_model, up_model));
                unfold(ctx_depth(Context::Right(identity, grandparent, color, sibling_model, up_model)));
                normalize();
            }
            have ctx_depth(u.model) < ctx_depth(old(c.model)) by {
                rewrite(u.model == up_model);
                arithmetic() using { ctx_depth(old(c.model)) == ctx_depth(up_model) + 1; }
            }
            have plug(Context::Right(identity, grandparent, color, sibling_model, up_model), old(t.model)) == plug(up_model, RbTree::Node(identity, grandparent, color, sibling_model, old(t.model))) by {
                unfold(plug(Context::Right(identity, grandparent, color, sibling_model, up_model), old(t.model)));
                normalize();
            }
            have rb_tree_parent_consistent(plug(u.model, sub.model)) == 1 by {
                rewrite(u.model == up_model);
                rewrite(sub.model == RbTree::Node(identity, grandparent, color, sibling_model, old(t.model)));
                rewrite(plug(up_model, RbTree::Node(identity, grandparent, color, sibling_model, old(t.model))) == plug(Context::Right(identity, grandparent, color, sibling_model, up_model), old(t.model)));
                rewrite(Context::Right(identity, grandparent, color, sibling_model, up_model) == old(c.model));
                assumption();
            }
            let { whole: whole } = refold_to_root(identity, root, { c: u, t: sub });
            have whole.model == plug(old(c.model), old(t.model)) by {
                rewrite(old(c.model) == Context::Right(identity, grandparent, color, sibling_model, up_model));
                rewrite(plug(Context::Right(identity, grandparent, color, sibling_model, up_model), old(t.model)) == plug(up_model, RbTree::Node(identity, grandparent, color, sibling_model, old(t.model))));
                simp();
            }
        },
    }
}


void ____rb_erase_color(struct rb_node* parent, struct rb_root* root,
    void (*augment_rotate)(struct rb_node* old, struct rb_node* new)) {
    consumes c: ctx_at(0, root);
    requires c.model != Context::Top;
    requires ctx_node_is(c.model, parent) == 1;
    requires erase_flips(c.model) == 1;
    requires ctx_rb(c.model, Nat::Succ(black_height(RbTree::Empty)), Color::Black) == 1;
    requires rb_tree_parent_consistent(plug(c.model, RbTree::Empty)) == 1;
    produces whole: rb_root_at(root);
    ensures whole.model == erase_flips_result(old(c.model), RbTree::Empty);
    ensures is_rb_root(whole.model) == 1;
    ensures rb_tree_parent_consistent(whole.model) == 1;
    ensures rb_inorder(whole.model) == rb_inorder(plug(old(c.model), RbTree::Empty));
} by {
    have c.model == ctx_reroot(c.model, parent) by {
        apply(ctx_reroot_fixed(c.model, parent)) using { ctx_node_is(c.model, parent) == 1; }
        assumption();
    }
    execute_until(loop(0));
    have node == 0 by { simp(); }
    let t = fold(rb_at(node), { model: RbTree::Empty });
    have is_rb(t.model) == 1 by { rewrite(t.model == RbTree::Empty); unfold(is_rb(RbTree::Empty)); normalize(); }
    have rb_root_black(t.model) == 1 by { rewrite(t.model == RbTree::Empty); unfold(rb_root_black(RbTree::Empty)); normalize(); }
    have rb_parent_is(t.model, parent) == 1 by { rewrite(t.model == RbTree::Empty); unfold(rb_parent_is(RbTree::Empty, parent)); normalize(); }
    loop {
        owns c: ctx_at(node, root);
        owns t: rb_at(node);
        decreases c;
        invariant c.model != Context::Top;
        invariant ctx_node_is(c.model, parent) == 1;
        invariant c.model == ctx_reroot(c.model, parent);
        invariant erase_flips(c.model) == 1;
        invariant is_rb(t.model) == 1;
        invariant rb_root_black(t.model) == 1;
        invariant rb_parent_is(t.model, parent) == 1;
        invariant ctx_rb(c.model, Nat::Succ(black_height(t.model)), Color::Black) == 1;
        invariant rb_tree_parent_consistent(plug(c.model, t.model)) == 1;
        invariant erase_flips_result(c.model, t.model) == erase_flips_result(old(c.model), RbTree::Empty);
        invariant rb_inorder(plug(c.model, t.model)) == rb_inorder(plug(old(c.model), RbTree::Empty));
        initialize by simp;
        preserve by {
            mark iteration;
            match c.model {
                Context::Top => { contradiction(c.model == Context::Top); },
                Context::Right(id, above, pc, sm, um) => {
                    have ctx_node_is(Context::Right(id, above, pc, sm, um), parent) == 1 by {
                        rewrite(Context::Right(id, above, pc, sm, um) == c.model); assumption();
                    }
                    have parent == id by {
                        apply(ctx_node_is_right_identity(id, above, pc, sm, um, parent)) using {
                            ctx_node_is(Context::Right(id, above, pc, sm, um), parent) == 1;
                        }
                        assumption();
                    }
                    match sm {
                        RbTree::Empty => {
                            have erase_flips(c.model) == 0 by {
                                rewrite(c.model == Context::Right(id, above, pc, sm, um)); rewrite(sm == RbTree::Empty);
                                unfold(erase_flips(Context::Right(id, above, pc, RbTree::Empty, um))); normalize();
                            }
                            have not(erase_flips(c.model) == 1) by { rewrite(erase_flips(c.model) == 0); normalize(); }
                            contradiction(erase_flips(c.model) == 1);
                        },
                        RbTree::Node(sid, sp, sc, srm, slm) => {
                            have sc == Color::Black by {
                                if sc == Color::Black { assumption(); } else {
                                    have erase_flips(c.model) == 0 by {
                                        rewrite(c.model == Context::Right(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, sp, sc, srm, slm));
                                        unfold(erase_flips(Context::Right(id, above, pc, RbTree::Node(sid, sp, sc, srm, slm), um)));
                                        normalize() using {  not(sc == Color::Black); }
                                    }
                                    have not(erase_flips(c.model) == 1) by { rewrite(erase_flips(c.model) == 0); normalize(); }
                                    contradiction(erase_flips(c.model) == 1);
                                }
                            }
                            have rb_root_black(slm) == 1 by {
                                if rb_root_black(slm) == 1 { assumption(); } else {
                                    have erase_flips(c.model) == 0 by {
                                        rewrite(c.model == Context::Right(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, sp, sc, srm, slm));
                                        unfold(erase_flips(Context::Right(id, above, pc, RbTree::Node(sid, sp, sc, srm, slm), um)));
                                        normalize() using { sc == Color::Black; not(rb_root_black(slm) == 1); }
                                    }
                                    have not(erase_flips(c.model) == 1) by { rewrite(erase_flips(c.model) == 0); normalize(); }
                                    contradiction(erase_flips(c.model) == 1);
                                }
                            }
                            have rb_root_black(srm) == 1 by {
                                if rb_root_black(srm) == 1 { assumption(); } else {
                                    have erase_flips(c.model) == 0 by {
                                        rewrite(c.model == Context::Right(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, sp, sc, srm, slm));
                                        unfold(erase_flips(Context::Right(id, above, pc, RbTree::Node(sid, sp, sc, srm, slm), um)));
                                        normalize() using { sc == Color::Black; rb_root_black(slm) == 1; not(rb_root_black(srm) == 1); }
                                    }
                                    have not(erase_flips(c.model) == 1) by { rewrite(erase_flips(c.model) == 0); normalize(); }
                                    contradiction(erase_flips(c.model) == 1);
                                }
                            }
                            have at(iteration, c.model) == c.model by { normalize(); }
                            have at(iteration, c.model) == Context::Right(id, above, pc, sm, um) by { rewrite(at(iteration, c.model) == c.model); assumption(); }
                            let { sibling: s, up: u } = unfold(c);
                            have aligned(id, 8) by { rewrite(id == parent); assumption(); }
                            have rb_parent_is(RbTree::Node(sid, sp, sc, srm, slm), id) == 1 by {
                                rewrite(RbTree::Node(sid, sp, sc, srm, slm) == sm); rewrite(id == parent); assumption();
                            }
                            apply(rb_parent_is_node_parent(sid, sp, sc, srm, slm, id));
                            have s.model == RbTree::Node(sid, id, Color::Black, srm, slm) by {
                                rewrite(s.model == sm); rewrite(sm == RbTree::Node(sid, sp, sc, srm, slm));
                                rewrite(sp == id); rewrite(sc == Color::Black); normalize();
                            }
                            have sm == RbTree::Node(sid, id, Color::Black, srm, slm) by {
                                rewrite(sm == RbTree::Node(sid, sp, sc, srm, slm)); rewrite(sp == id); rewrite(sc == Color::Black); normalize();
                            }
                            have at(iteration, c.model) == Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um) by {
                                rewrite(at(iteration, c.model) == Context::Right(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, id, Color::Black, srm, slm)); normalize();
                            }
                            let { right: sl, left: sr } = unfold(s);
                            step(); # Read the right child, which is the focus.
                            mark focus_split;
                            match t.model ensuring {
                                owns nt: rb_at(node);
                                fact nt.model == at(focus_split, t.model);
                            } {
                                RbTree::Empty => {
                                    have at(focus_split, t.model) == t.model by { normalize(); }
                                    have at(focus_split, t.model) == RbTree::Empty by { rewrite(at(focus_split, t.model) == t.model); assumption(); }
                                    unfold(t);
                                    step(); # The right child equals the null focus.
                                    let nt = fold(rb_at(node), { model: RbTree::Empty });
                                    have nt.model == at(focus_split, t.model) by { rewrite(nt.model == RbTree::Empty); rewrite(at(focus_split, t.model) == RbTree::Empty); normalize(); }
                                },
                                RbTree::Node(tid, tp, tc, trm, tlm) => {
                                    have at(focus_split, t.model) == t.model by { normalize(); }
                                    have at(focus_split, t.model) == RbTree::Node(tid, tp, tc, trm, tlm) by { rewrite(at(focus_split, t.model) == t.model); assumption(); }
                                    let { right: tl, left: tr } = unfold(t);
                                    step(); # The right child equals the current focus.
                                    let nt = fold(rb_at(node), { model: RbTree::Node(tid, tp, tc, trm, tlm) }, { right: tl, left: tr });
                                    have nt.model == at(focus_split, t.model) by { rewrite(nt.model == RbTree::Node(tid, tp, tc, trm, tlm)); rewrite(at(focus_split, t.model) == RbTree::Node(tid, tp, tc, trm, tlm)); normalize(); }
                                },
                            }
                            step(); # Read the left sibling on the mirrored C arm.
                            have is_rb(nt.model) == 1 by { rewrite(nt.model == at(focus_split, t.model)); assumption(); }
                            have rb_root_black(nt.model) == 1 by { rewrite(nt.model == at(focus_split, t.model)); assumption(); }
                            have rb_parent_is(nt.model, parent) == 1 by { rewrite(nt.model == at(focus_split, t.model)); assumption(); }
                            have (sid->__rb_parent_color & 1) == 1 by {
                                rewrite((sid->__rb_parent_color & 1) == color_bit(Color::Black)); unfold(color_bit(Color::Black)); normalize();
                            }
                            step(); step(); # Skip the red-sibling rotation.
                            step(); # Read the sibling's left child.
                            match sr.model ensuring {
                                owns rs: rb_at(tmp1);
                                fact rs.model == srm;
                            } {
                                RbTree::Empty => {
                                    have srm == RbTree::Empty by { rewrite(srm == sr.model); assumption(); }
                                    unfold(sr);
                                    step(); # The null child satisfies the black-child guard.
                                    let rs = fold(rb_at(tmp1), { model: RbTree::Empty });
                                    have rs.model == srm by { rewrite(srm == RbTree::Empty); normalize(); }
                                },
                                RbTree::Node(cid, cp, cc, crm, clm) => {
                                    have srm == RbTree::Node(cid, cp, cc, crm, clm) by { rewrite(srm == sr.model); assumption(); }
                                    have rb_root_black(RbTree::Node(cid, cp, cc, crm, clm)) == 1 by { rewrite(RbTree::Node(cid, cp, cc, crm, clm) == srm); assumption(); }
                                    apply(rb_root_black_node_color_bit(cid, cp, cc, crm, clm));
                                    let { right: cl, left: cr } = unfold(sr);
                                    step(); # The owned black child's tag satisfies the guard.
                                    let rs = fold(rb_at(tmp1), { model: RbTree::Node(cid, cp, cc, crm, clm) }, { right: cl, left: cr });
                                    have rs.model == srm by { rewrite(srm == RbTree::Node(cid, cp, cc, crm, clm)); normalize(); }
                                },
                            }
                            step(); # Read the sibling's right child.
                            match sl.model ensuring {
                                owns ls: rb_at(tmp2);
                                fact ls.model == slm;
                            } {
                                RbTree::Empty => {
                                    have slm == RbTree::Empty by { rewrite(slm == sl.model); assumption(); }
                                    unfold(sl);
                                    step(); # The null child satisfies the black-child guard.
                                    let ls = fold(rb_at(tmp2), { model: RbTree::Empty });
                                    have ls.model == slm by { rewrite(slm == RbTree::Empty); normalize(); }
                                },
                                RbTree::Node(cid, cp, cc, crm, clm) => {
                                    have slm == RbTree::Node(cid, cp, cc, crm, clm) by { rewrite(slm == sl.model); assumption(); }
                                    have rb_root_black(RbTree::Node(cid, cp, cc, crm, clm)) == 1 by { rewrite(RbTree::Node(cid, cp, cc, crm, clm) == slm); assumption(); }
                                    apply(rb_root_black_node_color_bit(cid, cp, cc, crm, clm));
                                    let { right: cl, left: cr } = unfold(sl);
                                    step(); # The owned black child's tag satisfies the guard.
                                    let ls = fold(rb_at(tmp2), { model: RbTree::Node(cid, cp, cc, crm, clm) }, { right: cl, left: cr });
                                    have ls.model == slm by { rewrite(slm == RbTree::Node(cid, cp, cc, crm, clm)); normalize(); }
                                },
                            }
                            have ctx_rb(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um), Nat::Succ(black_height(nt.model)), Color::Black) == 1 by {
                                rewrite(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um) == at(iteration, c.model)); rewrite(nt.model == at(focus_split, t.model)); assumption();
                            }
                            have rb_tree_parent_consistent(plug(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model)) == 1 by {
                                rewrite(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um) == at(iteration, c.model)); rewrite(nt.model == at(focus_split, t.model)); assumption();
                            }
                            have rb_parent_consistent(plug(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model), 0) == 1 by {
                                unfold(rb_tree_parent_consistent(plug(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model)));
                                rewrite(rb_parent_consistent(plug(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model), 0) == rb_tree_parent_consistent(plug(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model))); assumption();
                            }
                            have erase_flips_result(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model) == erase_flips_result(old(c.model), RbTree::Empty) by {
                                rewrite(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um) == at(iteration, c.model)); rewrite(nt.model == at(focus_split, t.model)); assumption();
                            }
                            have rb_inorder(plug(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model)) == rb_inorder(plug(old(c.model), RbTree::Empty)) by {
                                rewrite(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um) == at(iteration, c.model)); rewrite(nt.model == at(focus_split, t.model)); assumption();
                            }
                            step(); # Recolor the sibling red, preserving its parent.
                            have sid->__rb_parent_color == address(id) by { rewrite(id == parent); simp(); }
                            have (sid->__rb_parent_color & 1) == 0 by { rewrite(sid->__rb_parent_color == address(id)); arithmetic() using { aligned(id, 8); } }
                            have (sid->__rb_parent_color & 1) == color_bit(Color::Red) by { unfold(color_bit(Color::Red)); assumption(); }
                            have sid->__rb_parent_color == address(id) + (sid->__rb_parent_color & 1) by { rewrite((sid->__rb_parent_color & 1) == 0); rewrite(sid->__rb_parent_color == address(id)); normalize(); }
                            let sn = fold(rb_at(sid), { model: RbTree::Node(sid, id, Color::Red, srm, slm) }, { right: ls, left: rs });
                            have rb_parent_is(nt.model, id) == 1 by { rewrite(id == parent); assumption(); }
                            have rb_parent_is(sn.model, id) == 1 by { rewrite(sn.model == RbTree::Node(sid, id, Color::Red, srm, slm)); unfold(rb_parent_is(RbTree::Node(sid, id, Color::Red, srm, slm), id)); normalize(); }
                            match pc {
                                Color::Red => {
                                    have ctx_rb(Context::Right(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, srm, slm), um), Nat::Succ(black_height(nt.model)), Color::Black) == 1 by { rewrite(Color::Red == pc); assumption(); }
                                    have rb_parent_consistent(plug(Context::Right(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model), 0) == 1 by { rewrite(Color::Red == pc); assumption(); }
                                    apply(ctx_erase_case2_right_red_exit(above, id, sid, nt.model, srm, slm, um)) using {
                                        is_rb(nt.model) == 1;
                                        rb_root_black(nt.model) == 1;
                                        ctx_rb(Context::Right(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, srm, slm), um), Nat::Succ(black_height(nt.model)), Color::Black) == 1;
                                        rb_root_black(slm) == 1;
                                        rb_root_black(srm) == 1;
                                        rb_parent_consistent(plug(Context::Right(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model), 0) == 1;
                                    }
                                    have (parent->__rb_parent_color & 1) == 0 by {
                                        rewrite((parent->__rb_parent_color & 1) == color_bit(pc)); rewrite(pc == Color::Red); unfold(color_bit(Color::Red)); normalize();
                                    }
                                    have parent->__rb_parent_color == address(above) by {
                                        rewrite(parent->__rb_parent_color == address(above) + (parent->__rb_parent_color & 1)); rewrite((parent->__rb_parent_color & 1) == 0); normalize();
                                    }
                                    mark red_flip;
                                    have at(red_flip, parent->__rb_parent_color) == address(above) by { assumption(); }
                                    step(); step(); # Select the red parent and blacken it.
                                    have parent->__rb_parent_color == at(red_flip, parent->__rb_parent_color) + 1 by { simp(); }
                                    have parent->__rb_parent_color == address(above) + 1 by { rewrite(parent->__rb_parent_color == at(red_flip, parent->__rb_parent_color) + 1); rewrite(at(red_flip, parent->__rb_parent_color) == address(above)); normalize(); }
                                    have (parent->__rb_parent_color & 1) == 1 by { rewrite(parent->__rb_parent_color == address(above) + 1); arithmetic() using { aligned(above, 8); } }
                                    have (parent->__rb_parent_color & 1) == color_bit(Color::Black) by { unfold(color_bit(Color::Black)); assumption(); }
                                    have parent->__rb_parent_color == address(above) + (parent->__rb_parent_color & 1) by { rewrite((parent->__rb_parent_color & 1) == 1); assumption(); }
                                    let nc = fold(ctx_at(node, root), { model: Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), um) }, { sibling: sn, up: u });
                                    have plug(nc.model, nt.model) == plug(um, RbTree::Node(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), nt.model)) by { rewrite(nc.model == Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), um)); unfold(plug(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), um), nt.model)); normalize(); }
                                    have is_rb_root(plug(nc.model, nt.model)) == 1 by { rewrite(plug(nc.model, nt.model) == plug(um, RbTree::Node(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), nt.model))); assumption(); }
                                    have rb_tree_parent_consistent(plug(nc.model, nt.model)) == 1 by {
                                        unfold(rb_tree_parent_consistent(plug(nc.model, nt.model)));
                                        rewrite(plug(nc.model, nt.model) == plug(um, RbTree::Node(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), nt.model))); assumption();
                                    }
                                    have erase_flips_result(Context::Right(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model) == plug(um, RbTree::Node(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), nt.model)) by {
                                        unfold(erase_flips_result(Context::Right(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model)); unfold(rb_recolor(RbTree::Node(sid, id, Color::Black, srm, slm), Color::Red)); normalize();
                                    }
                                    have plug(nc.model, nt.model) == erase_flips_result(old(c.model), RbTree::Empty) by {
                                        rewrite(plug(nc.model, nt.model) == plug(um, RbTree::Node(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), nt.model))); rewrite(plug(um, RbTree::Node(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), nt.model)) == erase_flips_result(Context::Right(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model));
                                        rewrite(Color::Red == pc); assumption();
                                    }
                                    have rb_inorder(plug(nc.model, nt.model)) == rb_inorder(plug(old(c.model), RbTree::Empty)) by {
                                        rewrite(plug(nc.model, nt.model) == plug(um, RbTree::Node(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), nt.model)));
                                        rewrite(rb_inorder(plug(um, RbTree::Node(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), nt.model))) == rb_inorder(plug(Context::Right(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model)));
                                        rewrite(Color::Red == pc); assumption();
                                    }
                                    step(); # Break with a balanced whole tree.
                                },
                                Color::Black => {
                                    have Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, srm, slm), um) == Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um) by { rewrite(pc == Color::Black); normalize(); }
                                    have ctx_rb(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, srm, slm), um), Nat::Succ(black_height(nt.model)), Color::Black) == 1 by { rewrite(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, srm, slm), um) == Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um)); assumption(); }
                                    have rb_parent_consistent(plug(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model), 0) == 1 by { rewrite(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, srm, slm), um) == Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um)); assumption(); }
                                    apply(ctx_erase_case2_right_black_step(above, id, sid, nt.model, srm, slm, um)) using {
                                        is_rb(nt.model) == 1;
                                        rb_root_black(nt.model) == 1;
                                        ctx_rb(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, srm, slm), um), Nat::Succ(black_height(nt.model)), Color::Black) == 1;
                                        rb_root_black(slm) == 1;
                                        rb_root_black(srm) == 1;
                                        rb_parent_consistent(plug(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model), 0) == 1;
                                    }
                                    have (parent->__rb_parent_color & 1) == 1 by {
                                        rewrite((parent->__rb_parent_color & 1) == color_bit(pc)); rewrite(pc == Color::Black); unfold(color_bit(Color::Black)); normalize();
                                    }
                                    have parent->__rb_parent_color == address(above) + 1 by {
                                        rewrite(parent->__rb_parent_color == address(above) + (parent->__rb_parent_color & 1)); rewrite((parent->__rb_parent_color & 1) == 1); normalize();
                                    }
                                    have id->__rb_parent_color == address(above) + 1 by { assumption(); }
                                    have (id->__rb_parent_color & 1) == color_bit(Color::Black) by { unfold(color_bit(Color::Black)); assumption(); }
                                    have rb_inorder(plug(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model)) == rb_inorder(plug(old(c.model), RbTree::Empty)) by { rewrite(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, srm, slm), um) == Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um)); assumption(); }
                                    have erase_flips_result(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model) == erase_flips_result(old(c.model), RbTree::Empty) by { rewrite(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, srm, slm), um) == Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um)); assumption(); }
                                    step(); # The black parent cannot absorb the deficit.
                                    step(); step(); # Move the deficit node and decode its parent.
                                    have node == id by { simp(); }
                                    have parent == above by { simp(); }
                                    have id->__rb_parent_color == address(above) + (id->__rb_parent_color & 1) by {
                                        rewrite((id->__rb_parent_color & 1) == color_bit(Color::Black)); unfold(color_bit(Color::Black)); assumption();
                                    }
                                    mark parent_fold;
                                    have at(parent_fold, nt.model) == nt.model by { normalize(); }
                                    let sub = fold(rb_at(id), { model: RbTree::Node(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), nt.model) }, { right: nt, left: sn });
                                    have sub.model == RbTree::Node(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), at(parent_fold, nt.model)) by { normalize(); }
                                    have is_rb(sub.model) == 1 by { rewrite(sub.model == RbTree::Node(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), at(parent_fold, nt.model))); assumption(); }
                                    have rb_root_black(sub.model) == 1 by { rewrite(sub.model == RbTree::Node(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), at(parent_fold, nt.model))); assumption(); }
                                    have rb_parent_is(sub.model, parent) == 1 by { rewrite(sub.model == RbTree::Node(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), at(parent_fold, nt.model))); rewrite(parent == above); unfold(rb_parent_is(RbTree::Node(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), at(parent_fold, nt.model)), above)); normalize(); }
                                    have ctx_rb(u.model, Nat::Succ(black_height(sub.model)), Color::Black) == 1 by { rewrite(u.model == um); rewrite(sub.model == RbTree::Node(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), at(parent_fold, nt.model))); assumption(); }
                                    have rb_tree_parent_consistent(plug(u.model, sub.model)) == 1 by { unfold(rb_tree_parent_consistent(plug(u.model, sub.model))); assumption(); }
                                    have rb_inorder(plug(u.model, sub.model)) == rb_inorder(plug(old(c.model), RbTree::Empty)) by {
                                        rewrite(u.model == um); rewrite(sub.model == RbTree::Node(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), at(parent_fold, nt.model)));
                                        rewrite(rb_inorder(plug(um, RbTree::Node(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), at(parent_fold, nt.model)))) == rb_inorder(plug(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, srm, slm), um), at(parent_fold, nt.model)))); assumption();
                                    }
                                    have erase_flips_result(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, srm, slm), um), at(parent_fold, nt.model)) == erase_flips_result(um, RbTree::Node(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), at(parent_fold, nt.model))) by {
                                        unfold(erase_flips_result(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, srm, slm), um), at(parent_fold, nt.model))); unfold(rb_recolor(RbTree::Node(sid, id, Color::Black, srm, slm), Color::Red)); normalize();
                                    }
                                    have erase_flips_result(u.model, sub.model) == erase_flips_result(old(c.model), RbTree::Empty) by {
                                        rewrite(u.model == um); rewrite(sub.model == RbTree::Node(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), at(parent_fold, nt.model)));
                                        rewrite(erase_flips_result(um, RbTree::Node(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), at(parent_fold, nt.model))) == erase_flips_result(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, srm, slm), um), at(parent_fold, nt.model))); assumption();
                                    }

                                    have ctx_node_is(u.model, parent) == 1 by { rewrite(u.model == um); rewrite(parent == above); assumption(); }
                                    have u.model == ctx_reroot(u.model, parent) by { rewrite(u.model == um); rewrite(parent == above); assumption(); }
                                    have erase_flips(u.model) == 1 by {
                                        rewrite(u.model == um);
                                        have erase_flips(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, srm, slm), um)) == erase_flips(um) by {
                                            unfold(erase_flips(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, srm, slm), um))); normalize() using { rb_root_black(slm) == 1; rb_root_black(srm) == 1; }
                                        }
                                        rewrite(erase_flips(um) == erase_flips(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, srm, slm), um)));
                                        rewrite(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, srm, slm), um) == Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um)); rewrite(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um) == at(iteration, c.model)); assumption();
                                    }
                                    if parent == 0 {
                                        match u.model {
                                            Context::Top => {
                                                have is_rb_root(sub.model) == 1 by { apply(is_rb_root_from_parts(sub.model)) using { is_rb(sub.model) == 1; rb_root_black(sub.model) == 1; } assumption(); }
                                                have plug(u.model, sub.model) == sub.model by { rewrite(u.model == Context::Top); unfold(plug(Context::Top, sub.model)); normalize(); }
                                                have erase_flips_result(u.model, sub.model) == sub.model by { rewrite(u.model == Context::Top); unfold(erase_flips_result(Context::Top, sub.model)); normalize(); }
                                                have is_rb_root(plug(u.model, sub.model)) == 1 by { rewrite(plug(u.model, sub.model) == sub.model); assumption(); }
                                                have plug(u.model, sub.model) == erase_flips_result(old(c.model), RbTree::Empty) by {
                                                    rewrite(plug(u.model, sub.model) == sub.model); rewrite(sub.model == erase_flips_result(u.model, sub.model)); assumption();
                                                }
                                                step(); step(); step(); # Null parent: skip continue and break.
                                            },
                                            Context::Right(uid, ugp, uc, usm, uum) => {
                                                have ctx_node_is(Context::Right(uid, ugp, uc, usm, uum), parent) == 1 by { rewrite(Context::Right(uid, ugp, uc, usm, uum) == u.model); assumption(); }
                                                have parent == uid by { apply(ctx_node_is_right_identity(uid, ugp, uc, usm, uum, parent)) using { ctx_node_is(Context::Right(uid, ugp, uc, usm, uum), parent) == 1; } assumption(); }
                                                let { sibling: us, up: uu } = unfold(u);
                                                contradiction(parent == 0);
                                            },
                                            Context::Left(uid, ugp, uc, usm, uum) => {
                                                have ctx_node_is(Context::Left(uid, ugp, uc, usm, uum), parent) == 1 by { rewrite(Context::Left(uid, ugp, uc, usm, uum) == u.model); assumption(); }
                                                have parent == uid by { apply(ctx_node_is_left_identity(uid, ugp, uc, usm, uum, parent)) using { ctx_node_is(Context::Left(uid, ugp, uc, usm, uum), parent) == 1; } assumption(); }
                                                let { sibling: us, up: uu } = unfold(u);
                                                contradiction(parent == 0);
                                            },
                                        }
                                    } else {
                                        have u.model != Context::Top by {
                                            if u.model == Context::Top {
                                                have ctx_node_is(Context::Top, parent) == 1 by { rewrite(Context::Top == u.model); assumption(); }
                                                apply(ctx_node_is_top_null(parent)) using { ctx_node_is(Context::Top, parent) == 1; }
                                                contradiction(parent == 0);
                                            } else { assumption(); }
                                        }
                                        step(); step(); # A live parent continues with the strict child context.
                                        close_invariants();
                                    }
                                },
                            }

                        },
                    }
                },
                Context::Left(id, above, pc, sm, um) => {
                    have ctx_node_is(Context::Left(id, above, pc, sm, um), parent) == 1 by {
                        rewrite(Context::Left(id, above, pc, sm, um) == c.model); assumption();
                    }
                    have parent == id by {
                        apply(ctx_node_is_left_identity(id, above, pc, sm, um, parent)) using {
                            ctx_node_is(Context::Left(id, above, pc, sm, um), parent) == 1;
                        }
                        assumption();
                    }
                    match sm {
                        RbTree::Empty => {
                            have erase_flips(c.model) == 0 by {
                                rewrite(c.model == Context::Left(id, above, pc, sm, um)); rewrite(sm == RbTree::Empty);
                                unfold(erase_flips(Context::Left(id, above, pc, RbTree::Empty, um))); normalize();
                            }
                            have not(erase_flips(c.model) == 1) by { rewrite(erase_flips(c.model) == 0); normalize(); }
                            contradiction(erase_flips(c.model) == 1);
                        },
                        RbTree::Node(sid, sp, sc, slm, srm) => {
                            have sc == Color::Black by {
                                if sc == Color::Black { assumption(); } else {
                                    have erase_flips(c.model) == 0 by {
                                        rewrite(c.model == Context::Left(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, sp, sc, slm, srm));
                                        unfold(erase_flips(Context::Left(id, above, pc, RbTree::Node(sid, sp, sc, slm, srm), um)));
                                        normalize() using {  not(sc == Color::Black); }
                                    }
                                    have not(erase_flips(c.model) == 1) by { rewrite(erase_flips(c.model) == 0); normalize(); }
                                    contradiction(erase_flips(c.model) == 1);
                                }
                            }
                            have rb_root_black(slm) == 1 by {
                                if rb_root_black(slm) == 1 { assumption(); } else {
                                    have erase_flips(c.model) == 0 by {
                                        rewrite(c.model == Context::Left(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, sp, sc, slm, srm));
                                        unfold(erase_flips(Context::Left(id, above, pc, RbTree::Node(sid, sp, sc, slm, srm), um)));
                                        normalize() using { sc == Color::Black; not(rb_root_black(slm) == 1); }
                                    }
                                    have not(erase_flips(c.model) == 1) by { rewrite(erase_flips(c.model) == 0); normalize(); }
                                    contradiction(erase_flips(c.model) == 1);
                                }
                            }
                            have rb_root_black(srm) == 1 by {
                                if rb_root_black(srm) == 1 { assumption(); } else {
                                    have erase_flips(c.model) == 0 by {
                                        rewrite(c.model == Context::Left(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, sp, sc, slm, srm));
                                        unfold(erase_flips(Context::Left(id, above, pc, RbTree::Node(sid, sp, sc, slm, srm), um)));
                                        normalize() using { sc == Color::Black; rb_root_black(slm) == 1; not(rb_root_black(srm) == 1); }
                                    }
                                    have not(erase_flips(c.model) == 1) by { rewrite(erase_flips(c.model) == 0); normalize(); }
                                    contradiction(erase_flips(c.model) == 1);
                                }
                            }
                            have at(iteration, c.model) == c.model by { normalize(); }
                            have at(iteration, c.model) == Context::Left(id, above, pc, sm, um) by { rewrite(at(iteration, c.model) == c.model); assumption(); }
                            let { sibling: s, up: u } = unfold(c);
                            have aligned(id, 8) by { rewrite(id == parent); assumption(); }
                            have rb_parent_is(RbTree::Node(sid, sp, sc, slm, srm), id) == 1 by {
                                rewrite(RbTree::Node(sid, sp, sc, slm, srm) == sm); rewrite(id == parent); assumption();
                            }
                            apply(rb_parent_is_node_parent(sid, sp, sc, slm, srm, id));
                            have s.model == RbTree::Node(sid, id, Color::Black, slm, srm) by {
                                rewrite(s.model == sm); rewrite(sm == RbTree::Node(sid, sp, sc, slm, srm));
                                rewrite(sp == id); rewrite(sc == Color::Black); normalize();
                            }
                            have sm == RbTree::Node(sid, id, Color::Black, slm, srm) by {
                                rewrite(sm == RbTree::Node(sid, sp, sc, slm, srm)); rewrite(sp == id); rewrite(sc == Color::Black); normalize();
                            }
                            have at(iteration, c.model) == Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um) by {
                                rewrite(at(iteration, c.model) == Context::Left(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, id, Color::Black, slm, srm)); normalize();
                            }
                            let { left: sl, right: sr } = unfold(s);
                            step(); # Read the sibling.
                            mark focus_split;
                            match t.model ensuring {
                                owns nt: rb_at(node);
                                fact nt.model == at(focus_split, t.model);
                            } {
                                RbTree::Empty => {
                                    have at(focus_split, t.model) == t.model by { normalize(); }
                                    have at(focus_split, t.model) == RbTree::Empty by { rewrite(at(focus_split, t.model) == t.model); assumption(); }
                                    unfold(t);
                                    step(); # The null focus differs from the sibling.
                                    let nt = fold(rb_at(node), { model: RbTree::Empty });
                                    have nt.model == at(focus_split, t.model) by { rewrite(nt.model == RbTree::Empty); rewrite(at(focus_split, t.model) == RbTree::Empty); normalize(); }
                                },
                                RbTree::Node(tid, tp, tc, tlm, trm) => {
                                    have at(focus_split, t.model) == t.model by { normalize(); }
                                    have at(focus_split, t.model) == RbTree::Node(tid, tp, tc, tlm, trm) by { rewrite(at(focus_split, t.model) == t.model); assumption(); }
                                    let { left: tl, right: tr } = unfold(t);
                                    step(); # Separate owned roots distinguish the two pointers.
                                    let nt = fold(rb_at(node), { model: RbTree::Node(tid, tp, tc, tlm, trm) }, { left: tl, right: tr });
                                    have nt.model == at(focus_split, t.model) by { rewrite(nt.model == RbTree::Node(tid, tp, tc, tlm, trm)); rewrite(at(focus_split, t.model) == RbTree::Node(tid, tp, tc, tlm, trm)); normalize(); }
                                },
                            }
                            have is_rb(nt.model) == 1 by { rewrite(nt.model == at(focus_split, t.model)); assumption(); }
                            have rb_root_black(nt.model) == 1 by { rewrite(nt.model == at(focus_split, t.model)); assumption(); }
                            have rb_parent_is(nt.model, parent) == 1 by { rewrite(nt.model == at(focus_split, t.model)); assumption(); }
                            have (sid->__rb_parent_color & 1) == 1 by {
                                rewrite((sid->__rb_parent_color & 1) == color_bit(Color::Black)); unfold(color_bit(Color::Black)); normalize();
                            }
                            step(); step(); # Skip the red-sibling rotation.
                            step(); # Read the sibling's right child.
                            match sr.model ensuring {
                                owns rs: rb_at(tmp1);
                                fact rs.model == srm;
                            } {
                                RbTree::Empty => {
                                    have srm == RbTree::Empty by { rewrite(srm == sr.model); assumption(); }
                                    unfold(sr);
                                    step(); # The null child satisfies the black-child guard.
                                    let rs = fold(rb_at(tmp1), { model: RbTree::Empty });
                                    have rs.model == srm by { rewrite(srm == RbTree::Empty); normalize(); }
                                },
                                RbTree::Node(cid, cp, cc, clm, crm) => {
                                    have srm == RbTree::Node(cid, cp, cc, clm, crm) by { rewrite(srm == sr.model); assumption(); }
                                    have rb_root_black(RbTree::Node(cid, cp, cc, clm, crm)) == 1 by { rewrite(RbTree::Node(cid, cp, cc, clm, crm) == srm); assumption(); }
                                    apply(rb_root_black_node_color_bit(cid, cp, cc, clm, crm));
                                    let { left: cl, right: cr } = unfold(sr);
                                    step(); # The owned black child's tag satisfies the guard.
                                    let rs = fold(rb_at(tmp1), { model: RbTree::Node(cid, cp, cc, clm, crm) }, { left: cl, right: cr });
                                    have rs.model == srm by { rewrite(srm == RbTree::Node(cid, cp, cc, clm, crm)); normalize(); }
                                },
                            }
                            step(); # Read the sibling's left child.
                            match sl.model ensuring {
                                owns ls: rb_at(tmp2);
                                fact ls.model == slm;
                            } {
                                RbTree::Empty => {
                                    have slm == RbTree::Empty by { rewrite(slm == sl.model); assumption(); }
                                    unfold(sl);
                                    step(); # The null child satisfies the black-child guard.
                                    let ls = fold(rb_at(tmp2), { model: RbTree::Empty });
                                    have ls.model == slm by { rewrite(slm == RbTree::Empty); normalize(); }
                                },
                                RbTree::Node(cid, cp, cc, clm, crm) => {
                                    have slm == RbTree::Node(cid, cp, cc, clm, crm) by { rewrite(slm == sl.model); assumption(); }
                                    have rb_root_black(RbTree::Node(cid, cp, cc, clm, crm)) == 1 by { rewrite(RbTree::Node(cid, cp, cc, clm, crm) == slm); assumption(); }
                                    apply(rb_root_black_node_color_bit(cid, cp, cc, clm, crm));
                                    let { left: cl, right: cr } = unfold(sl);
                                    step(); # The owned black child's tag satisfies the guard.
                                    let ls = fold(rb_at(tmp2), { model: RbTree::Node(cid, cp, cc, clm, crm) }, { left: cl, right: cr });
                                    have ls.model == slm by { rewrite(slm == RbTree::Node(cid, cp, cc, clm, crm)); normalize(); }
                                },
                            }
                            have ctx_rb(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um), Nat::Succ(black_height(nt.model)), Color::Black) == 1 by {
                                rewrite(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um) == at(iteration, c.model)); rewrite(nt.model == at(focus_split, t.model)); assumption();
                            }
                            have rb_tree_parent_consistent(plug(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model)) == 1 by {
                                rewrite(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um) == at(iteration, c.model)); rewrite(nt.model == at(focus_split, t.model)); assumption();
                            }
                            have rb_parent_consistent(plug(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model), 0) == 1 by {
                                unfold(rb_tree_parent_consistent(plug(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model)));
                                rewrite(rb_parent_consistent(plug(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model), 0) == rb_tree_parent_consistent(plug(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model))); assumption();
                            }
                            have erase_flips_result(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model) == erase_flips_result(old(c.model), RbTree::Empty) by {
                                rewrite(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um) == at(iteration, c.model)); rewrite(nt.model == at(focus_split, t.model)); assumption();
                            }
                            have rb_inorder(plug(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model)) == rb_inorder(plug(old(c.model), RbTree::Empty)) by {
                                rewrite(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um) == at(iteration, c.model)); rewrite(nt.model == at(focus_split, t.model)); assumption();
                            }
                            step(); # Recolor the sibling red, preserving its parent.
                            have sid->__rb_parent_color == address(id) by { rewrite(id == parent); simp(); }
                            have (sid->__rb_parent_color & 1) == 0 by { rewrite(sid->__rb_parent_color == address(id)); arithmetic() using { aligned(id, 8); } }
                            have (sid->__rb_parent_color & 1) == color_bit(Color::Red) by { unfold(color_bit(Color::Red)); assumption(); }
                            have sid->__rb_parent_color == address(id) + (sid->__rb_parent_color & 1) by { rewrite((sid->__rb_parent_color & 1) == 0); rewrite(sid->__rb_parent_color == address(id)); normalize(); }
                            let sn = fold(rb_at(sid), { model: RbTree::Node(sid, id, Color::Red, slm, srm) }, { left: ls, right: rs });
                            have rb_parent_is(nt.model, id) == 1 by { rewrite(id == parent); assumption(); }
                            have rb_parent_is(sn.model, id) == 1 by { rewrite(sn.model == RbTree::Node(sid, id, Color::Red, slm, srm)); unfold(rb_parent_is(RbTree::Node(sid, id, Color::Red, slm, srm), id)); normalize(); }
                            match pc {
                                Color::Red => {
                                    have ctx_rb(Context::Left(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, slm, srm), um), Nat::Succ(black_height(nt.model)), Color::Black) == 1 by { rewrite(Color::Red == pc); assumption(); }
                                    have rb_parent_consistent(plug(Context::Left(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model), 0) == 1 by { rewrite(Color::Red == pc); assumption(); }
                                    apply(ctx_erase_case2_left_red_exit(above, id, sid, nt.model, slm, srm, um)) using {
                                        is_rb(nt.model) == 1;
                                        rb_root_black(nt.model) == 1;
                                        ctx_rb(Context::Left(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, slm, srm), um), Nat::Succ(black_height(nt.model)), Color::Black) == 1;
                                        rb_root_black(slm) == 1;
                                        rb_root_black(srm) == 1;
                                        rb_parent_consistent(plug(Context::Left(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model), 0) == 1;
                                    }
                                    have (parent->__rb_parent_color & 1) == 0 by {
                                        rewrite((parent->__rb_parent_color & 1) == color_bit(pc)); rewrite(pc == Color::Red); unfold(color_bit(Color::Red)); normalize();
                                    }
                                    have parent->__rb_parent_color == address(above) by {
                                        rewrite(parent->__rb_parent_color == address(above) + (parent->__rb_parent_color & 1)); rewrite((parent->__rb_parent_color & 1) == 0); normalize();
                                    }
                                    mark red_flip;
                                    have at(red_flip, parent->__rb_parent_color) == address(above) by { assumption(); }
                                    step(); step(); # Select the red parent and blacken it.
                                    have parent->__rb_parent_color == at(red_flip, parent->__rb_parent_color) + 1 by { simp(); }
                                    have parent->__rb_parent_color == address(above) + 1 by { rewrite(parent->__rb_parent_color == at(red_flip, parent->__rb_parent_color) + 1); rewrite(at(red_flip, parent->__rb_parent_color) == address(above)); normalize(); }
                                    have (parent->__rb_parent_color & 1) == 1 by { rewrite(parent->__rb_parent_color == address(above) + 1); arithmetic() using { aligned(above, 8); } }
                                    have (parent->__rb_parent_color & 1) == color_bit(Color::Black) by { unfold(color_bit(Color::Black)); assumption(); }
                                    have parent->__rb_parent_color == address(above) + (parent->__rb_parent_color & 1) by { rewrite((parent->__rb_parent_color & 1) == 1); assumption(); }
                                    let nc = fold(ctx_at(node, root), { model: Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, slm, srm), um) }, { sibling: sn, up: u });
                                    have plug(nc.model, nt.model) == plug(um, RbTree::Node(id, above, Color::Black, nt.model, RbTree::Node(sid, id, Color::Red, slm, srm))) by { rewrite(nc.model == Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, slm, srm), um)); unfold(plug(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, slm, srm), um), nt.model)); normalize(); }
                                    have is_rb_root(plug(nc.model, nt.model)) == 1 by { rewrite(plug(nc.model, nt.model) == plug(um, RbTree::Node(id, above, Color::Black, nt.model, RbTree::Node(sid, id, Color::Red, slm, srm)))); assumption(); }
                                    have rb_tree_parent_consistent(plug(nc.model, nt.model)) == 1 by {
                                        unfold(rb_tree_parent_consistent(plug(nc.model, nt.model)));
                                        rewrite(plug(nc.model, nt.model) == plug(um, RbTree::Node(id, above, Color::Black, nt.model, RbTree::Node(sid, id, Color::Red, slm, srm)))); assumption();
                                    }
                                    have erase_flips_result(Context::Left(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model) == plug(um, RbTree::Node(id, above, Color::Black, nt.model, RbTree::Node(sid, id, Color::Red, slm, srm))) by {
                                        unfold(erase_flips_result(Context::Left(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model)); unfold(rb_recolor(RbTree::Node(sid, id, Color::Black, slm, srm), Color::Red)); normalize();
                                    }
                                    have plug(nc.model, nt.model) == erase_flips_result(old(c.model), RbTree::Empty) by {
                                        rewrite(plug(nc.model, nt.model) == plug(um, RbTree::Node(id, above, Color::Black, nt.model, RbTree::Node(sid, id, Color::Red, slm, srm)))); rewrite(plug(um, RbTree::Node(id, above, Color::Black, nt.model, RbTree::Node(sid, id, Color::Red, slm, srm))) == erase_flips_result(Context::Left(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model));
                                        rewrite(Color::Red == pc); assumption();
                                    }
                                    have rb_inorder(plug(nc.model, nt.model)) == rb_inorder(plug(old(c.model), RbTree::Empty)) by {
                                        rewrite(plug(nc.model, nt.model) == plug(um, RbTree::Node(id, above, Color::Black, nt.model, RbTree::Node(sid, id, Color::Red, slm, srm))));
                                        rewrite(rb_inorder(plug(um, RbTree::Node(id, above, Color::Black, nt.model, RbTree::Node(sid, id, Color::Red, slm, srm)))) == rb_inorder(plug(Context::Left(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model)));
                                        rewrite(Color::Red == pc); assumption();
                                    }
                                    step(); # Break with a balanced whole tree.
                                },
                                Color::Black => {
                                    have Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, slm, srm), um) == Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um) by { rewrite(pc == Color::Black); normalize(); }
                                    have ctx_rb(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, slm, srm), um), Nat::Succ(black_height(nt.model)), Color::Black) == 1 by { rewrite(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, slm, srm), um) == Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um)); assumption(); }
                                    have rb_parent_consistent(plug(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model), 0) == 1 by { rewrite(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, slm, srm), um) == Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um)); assumption(); }
                                    apply(ctx_erase_case2_left_black_step(above, id, sid, nt.model, slm, srm, um)) using {
                                        is_rb(nt.model) == 1;
                                        rb_root_black(nt.model) == 1;
                                        ctx_rb(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, slm, srm), um), Nat::Succ(black_height(nt.model)), Color::Black) == 1;
                                        rb_root_black(slm) == 1;
                                        rb_root_black(srm) == 1;
                                        rb_parent_consistent(plug(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model), 0) == 1;
                                    }
                                    have (parent->__rb_parent_color & 1) == 1 by {
                                        rewrite((parent->__rb_parent_color & 1) == color_bit(pc)); rewrite(pc == Color::Black); unfold(color_bit(Color::Black)); normalize();
                                    }
                                    have parent->__rb_parent_color == address(above) + 1 by {
                                        rewrite(parent->__rb_parent_color == address(above) + (parent->__rb_parent_color & 1)); rewrite((parent->__rb_parent_color & 1) == 1); normalize();
                                    }
                                    have id->__rb_parent_color == address(above) + 1 by { assumption(); }
                                    have (id->__rb_parent_color & 1) == color_bit(Color::Black) by { unfold(color_bit(Color::Black)); assumption(); }
                                    have rb_inorder(plug(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model)) == rb_inorder(plug(old(c.model), RbTree::Empty)) by { rewrite(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, slm, srm), um) == Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um)); assumption(); }
                                    have erase_flips_result(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model) == erase_flips_result(old(c.model), RbTree::Empty) by { rewrite(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, slm, srm), um) == Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um)); assumption(); }
                                    step(); # The black parent cannot absorb the deficit.
                                    step(); step(); # Move the deficit node and decode its parent.
                                    have node == id by { simp(); }
                                    have parent == above by { simp(); }
                                    have id->__rb_parent_color == address(above) + (id->__rb_parent_color & 1) by {
                                        rewrite((id->__rb_parent_color & 1) == color_bit(Color::Black)); unfold(color_bit(Color::Black)); assumption();
                                    }
                                    mark parent_fold;
                                    have at(parent_fold, nt.model) == nt.model by { normalize(); }
                                    let sub = fold(rb_at(id), { model: RbTree::Node(id, above, Color::Black, nt.model, RbTree::Node(sid, id, Color::Red, slm, srm)) }, { left: nt, right: sn });
                                    have sub.model == RbTree::Node(id, above, Color::Black, at(parent_fold, nt.model), RbTree::Node(sid, id, Color::Red, slm, srm)) by { normalize(); }
                                    have is_rb(sub.model) == 1 by { rewrite(sub.model == RbTree::Node(id, above, Color::Black, at(parent_fold, nt.model), RbTree::Node(sid, id, Color::Red, slm, srm))); assumption(); }
                                    have rb_root_black(sub.model) == 1 by { rewrite(sub.model == RbTree::Node(id, above, Color::Black, at(parent_fold, nt.model), RbTree::Node(sid, id, Color::Red, slm, srm))); assumption(); }
                                    have rb_parent_is(sub.model, parent) == 1 by { rewrite(sub.model == RbTree::Node(id, above, Color::Black, at(parent_fold, nt.model), RbTree::Node(sid, id, Color::Red, slm, srm))); rewrite(parent == above); unfold(rb_parent_is(RbTree::Node(id, above, Color::Black, at(parent_fold, nt.model), RbTree::Node(sid, id, Color::Red, slm, srm)), above)); normalize(); }
                                    have ctx_rb(u.model, Nat::Succ(black_height(sub.model)), Color::Black) == 1 by { rewrite(u.model == um); rewrite(sub.model == RbTree::Node(id, above, Color::Black, at(parent_fold, nt.model), RbTree::Node(sid, id, Color::Red, slm, srm))); assumption(); }
                                    have rb_tree_parent_consistent(plug(u.model, sub.model)) == 1 by { unfold(rb_tree_parent_consistent(plug(u.model, sub.model))); assumption(); }
                                    have rb_inorder(plug(u.model, sub.model)) == rb_inorder(plug(old(c.model), RbTree::Empty)) by {
                                        rewrite(u.model == um); rewrite(sub.model == RbTree::Node(id, above, Color::Black, at(parent_fold, nt.model), RbTree::Node(sid, id, Color::Red, slm, srm)));
                                        rewrite(rb_inorder(plug(um, RbTree::Node(id, above, Color::Black, at(parent_fold, nt.model), RbTree::Node(sid, id, Color::Red, slm, srm)))) == rb_inorder(plug(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, slm, srm), um), at(parent_fold, nt.model)))); assumption();
                                    }
                                    have erase_flips_result(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, slm, srm), um), at(parent_fold, nt.model)) == erase_flips_result(um, RbTree::Node(id, above, Color::Black, at(parent_fold, nt.model), RbTree::Node(sid, id, Color::Red, slm, srm))) by {
                                        unfold(erase_flips_result(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, slm, srm), um), at(parent_fold, nt.model))); unfold(rb_recolor(RbTree::Node(sid, id, Color::Black, slm, srm), Color::Red)); normalize();
                                    }
                                    have erase_flips_result(u.model, sub.model) == erase_flips_result(old(c.model), RbTree::Empty) by {
                                        rewrite(u.model == um); rewrite(sub.model == RbTree::Node(id, above, Color::Black, at(parent_fold, nt.model), RbTree::Node(sid, id, Color::Red, slm, srm)));
                                        rewrite(erase_flips_result(um, RbTree::Node(id, above, Color::Black, at(parent_fold, nt.model), RbTree::Node(sid, id, Color::Red, slm, srm))) == erase_flips_result(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, slm, srm), um), at(parent_fold, nt.model))); assumption();
                                    }

                                    have ctx_node_is(u.model, parent) == 1 by { rewrite(u.model == um); rewrite(parent == above); assumption(); }
                                    have u.model == ctx_reroot(u.model, parent) by { rewrite(u.model == um); rewrite(parent == above); assumption(); }
                                    have erase_flips(u.model) == 1 by {
                                        rewrite(u.model == um);
                                        have erase_flips(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, slm, srm), um)) == erase_flips(um) by {
                                            unfold(erase_flips(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, slm, srm), um))); normalize() using { rb_root_black(slm) == 1; rb_root_black(srm) == 1; }
                                        }
                                        rewrite(erase_flips(um) == erase_flips(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, slm, srm), um)));
                                        rewrite(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, slm, srm), um) == Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um)); rewrite(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um) == at(iteration, c.model)); assumption();
                                    }
                                    if parent == 0 {
                                        match u.model {
                                            Context::Top => {
                                                have is_rb_root(sub.model) == 1 by { apply(is_rb_root_from_parts(sub.model)) using { is_rb(sub.model) == 1; rb_root_black(sub.model) == 1; } assumption(); }
                                                have plug(u.model, sub.model) == sub.model by { rewrite(u.model == Context::Top); unfold(plug(Context::Top, sub.model)); normalize(); }
                                                have erase_flips_result(u.model, sub.model) == sub.model by { rewrite(u.model == Context::Top); unfold(erase_flips_result(Context::Top, sub.model)); normalize(); }
                                                have is_rb_root(plug(u.model, sub.model)) == 1 by { rewrite(plug(u.model, sub.model) == sub.model); assumption(); }
                                                have plug(u.model, sub.model) == erase_flips_result(old(c.model), RbTree::Empty) by {
                                                    rewrite(plug(u.model, sub.model) == sub.model); rewrite(sub.model == erase_flips_result(u.model, sub.model)); assumption();
                                                }
                                                step(); step(); step(); # Null parent: skip continue and break.
                                            },
                                            Context::Left(uid, ugp, uc, usm, uum) => {
                                                have ctx_node_is(Context::Left(uid, ugp, uc, usm, uum), parent) == 1 by { rewrite(Context::Left(uid, ugp, uc, usm, uum) == u.model); assumption(); }
                                                have parent == uid by { apply(ctx_node_is_left_identity(uid, ugp, uc, usm, uum, parent)) using { ctx_node_is(Context::Left(uid, ugp, uc, usm, uum), parent) == 1; } assumption(); }
                                                let { sibling: us, up: uu } = unfold(u);
                                                contradiction(parent == 0);
                                            },
                                            Context::Right(uid, ugp, uc, usm, uum) => {
                                                have ctx_node_is(Context::Right(uid, ugp, uc, usm, uum), parent) == 1 by { rewrite(Context::Right(uid, ugp, uc, usm, uum) == u.model); assumption(); }
                                                have parent == uid by { apply(ctx_node_is_right_identity(uid, ugp, uc, usm, uum, parent)) using { ctx_node_is(Context::Right(uid, ugp, uc, usm, uum), parent) == 1; } assumption(); }
                                                let { sibling: us, up: uu } = unfold(u);
                                                contradiction(parent == 0);
                                            },
                                        }
                                    } else {
                                        have u.model != Context::Top by {
                                            if u.model == Context::Top {
                                                have ctx_node_is(Context::Top, parent) == 1 by { rewrite(Context::Top == u.model); assumption(); }
                                                apply(ctx_node_is_top_null(parent)) using { ctx_node_is(Context::Top, parent) == 1; }
                                                contradiction(parent == 0);
                                            } else { assumption(); }
                                        }
                                        step(); step(); # A live parent continues with the strict child context.
                                        close_invariants();
                                    }
                                },
                            }

                        },
                    }
                },
            }
        }
    }
    mark refold;
    let { whole: whole } = refold_to_root(node, root, { c: c, t: t });
    have whole.model == erase_flips_result(old(c.model), RbTree::Empty) by { rewrite(whole.model == at(refold, plug(c.model, t.model))); assumption(); }
    have is_rb_root(whole.model) == 1 by { rewrite(whole.model == at(refold, plug(c.model, t.model))); assumption(); }
    have rb_tree_parent_consistent(whole.model) == 1 by { rewrite(whole.model == at(refold, plug(c.model, t.model))); assumption(); }
    have rb_inorder(whole.model) == rb_inorder(plug(old(c.model), RbTree::Empty)) by { rewrite(whole.model == at(refold, plug(c.model, t.model))); assumption(); }
    execute(); simp();
}
