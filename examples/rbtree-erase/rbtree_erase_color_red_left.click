verifying "rb_erase_color.c";
import "../rbtree-model/rbtree_spine_resources.click";

function erase_red_parent_left(ctx: Context, parent: struct rb_node*) -> int32 {
    match ctx {
        Context::Top => 0,
        Context::Left(id, above, color, sibling, up) =>
        if id == parent {
            if color == Color::Red {
                match sibling {
                    RbTree::Empty => 0,
                    RbTree::Node(sid, sp, sc, sl, sr) =>
                    if sc == Color::Black {
                        if sl == RbTree::Empty {
                            if sr == RbTree::Empty { 1 } else { 0 }
                        } else { 0 }
                    } else { 0 },
                }
            } else { 0 }
        } else { 0 },
        Context::Right(id, above, color, sibling, up) => 0,
    }
}

function erase_left_red_flip(ctx: Context) -> RbTree {
    match ctx {
        Context::Top => RbTree::Empty,
        Context::Left(parent, above, color, sibling, up) =>
        plug(up, RbTree::Node(parent, above, Color::Black, RbTree::Empty,
            rb_recolor(sibling, Color::Red))),
        Context::Right(parent, above, color, sibling, up) => RbTree::Empty,
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
    requires erase_red_parent_left(c.model, parent) == 1;
    requires ctx_rb(c.model, Nat::Succ(black_height(RbTree::Empty)), Color::Black) == 1;
    requires rb_parent_consistent(plug(c.model, RbTree::Empty), 0) == 1;
    produces whole: rb_root_at(root);
    ensures whole.model == erase_left_red_flip(old(c.model));
    ensures is_rb_root(whole.model) == 1;
    ensures rb_parent_consistent(whole.model, 0) == 1;
    ensures rb_inorder(whole.model) == rb_inorder(plug(old(c.model), RbTree::Empty));
} by {
    match c.model {
        Context::Top => {
            have erase_red_parent_left(c.model, parent) == 0 by {
                rewrite(c.model == Context::Top); unfold(erase_red_parent_left(Context::Top, parent)); normalize();
            }
            have not(erase_red_parent_left(c.model, parent) == 1) by {
                rewrite(erase_red_parent_left(c.model, parent) == 0); normalize();
            }
            contradiction(erase_red_parent_left(c.model, parent) == 1);
        },
        Context::Right(id, above, pc, sm, um) => {
            have erase_red_parent_left(c.model, parent) == 0 by {
                rewrite(c.model == Context::Right(id, above, pc, sm, um));
                unfold(erase_red_parent_left(Context::Right(id, above, pc, sm, um), parent)); normalize();
            }
            have not(erase_red_parent_left(c.model, parent) == 1) by {
                rewrite(erase_red_parent_left(c.model, parent) == 0); normalize();
            }
            contradiction(erase_red_parent_left(c.model, parent) == 1);
        },
        Context::Left(id, above, pc, sm, um) => {
            have id == parent by {
                if id == parent { assumption(); } else {
                    have erase_red_parent_left(c.model, parent) == 0 by {
                        rewrite(c.model == Context::Left(id, above, pc, sm, um));
                        unfold(erase_red_parent_left(Context::Left(id, above, pc, sm, um), parent));
                        normalize() using { not(id == parent); }
                    }
                    have not(erase_red_parent_left(c.model, parent) == 1) by {
                        rewrite(erase_red_parent_left(c.model, parent) == 0); normalize();
                    }
                    contradiction(erase_red_parent_left(c.model, parent) == 1);
                }
            }
            have pc == Color::Red by {
                if pc == Color::Red { assumption(); } else {
                    have erase_red_parent_left(c.model, parent) == 0 by {
                        rewrite(c.model == Context::Left(id, above, pc, sm, um));
                        unfold(erase_red_parent_left(Context::Left(id, above, pc, sm, um), parent));
                        normalize() using { id == parent; not(pc == Color::Red); }
                    }
                    have not(erase_red_parent_left(c.model, parent) == 1) by {
                        rewrite(erase_red_parent_left(c.model, parent) == 0); normalize();
                    }
                    contradiction(erase_red_parent_left(c.model, parent) == 1);
                }
            }
            match sm {
                RbTree::Empty => {
                    have erase_red_parent_left(c.model, parent) == 0 by {
                        rewrite(c.model == Context::Left(id, above, pc, sm, um));
                        rewrite(sm == RbTree::Empty);
                        unfold(erase_red_parent_left(Context::Left(id, above, pc, RbTree::Empty, um), parent));
                        normalize() using { id == parent; pc == Color::Red; }
                    }
                    have not(erase_red_parent_left(c.model, parent) == 1) by {
                        rewrite(erase_red_parent_left(c.model, parent) == 0); normalize();
                    }
                    contradiction(erase_red_parent_left(c.model, parent) == 1);
                },
                RbTree::Node(sid, sp, sc, slm, srm) => {
                    have sc == Color::Black by {
                        if sc == Color::Black { assumption(); } else {
                            have erase_red_parent_left(c.model, parent) == 0 by {
                                rewrite(c.model == Context::Left(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, sp, sc, slm, srm));
                                unfold(erase_red_parent_left(Context::Left(id, above, pc, RbTree::Node(sid, sp, sc, slm, srm), um), parent));
                                normalize() using { id == parent; pc == Color::Red; not(sc == Color::Black); }
                            }
                            have not(erase_red_parent_left(c.model, parent) == 1) by {
                                rewrite(erase_red_parent_left(c.model, parent) == 0); normalize();
                            }
                            contradiction(erase_red_parent_left(c.model, parent) == 1);
                        }
                    }
                    have slm == RbTree::Empty by {
                        if slm == RbTree::Empty { assumption(); } else {
                            have erase_red_parent_left(c.model, parent) == 0 by {
                                rewrite(c.model == Context::Left(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, sp, sc, slm, srm));
                                unfold(erase_red_parent_left(Context::Left(id, above, pc, RbTree::Node(sid, sp, sc, slm, srm), um), parent));
                                normalize() using { id == parent; pc == Color::Red; sc == Color::Black; not(slm == RbTree::Empty); }
                            }
                            have not(erase_red_parent_left(c.model, parent) == 1) by {
                                rewrite(erase_red_parent_left(c.model, parent) == 0); normalize();
                            }
                            contradiction(erase_red_parent_left(c.model, parent) == 1);
                        }
                    }
                    have srm == RbTree::Empty by {
                        if srm == RbTree::Empty { assumption(); } else {
                            have erase_red_parent_left(c.model, parent) == 0 by {
                                rewrite(c.model == Context::Left(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, sp, sc, slm, srm));
                                unfold(erase_red_parent_left(Context::Left(id, above, pc, RbTree::Node(sid, sp, sc, slm, srm), um), parent));
                                normalize() using { id == parent; pc == Color::Red; sc == Color::Black; slm == RbTree::Empty; not(srm == RbTree::Empty); }
                            }
                            have not(erase_red_parent_left(c.model, parent) == 1) by {
                                rewrite(erase_red_parent_left(c.model, parent) == 0); normalize();
                            }
                            contradiction(erase_red_parent_left(c.model, parent) == 1);
                        }
                    }
                    have c.model == Context::Left(parent, above, Color::Red,
                        RbTree::Node(sid, sp, Color::Black, RbTree::Empty, RbTree::Empty), um) by {
                        rewrite(c.model == Context::Left(id, above, pc, sm, um));
                        rewrite(sm == RbTree::Node(sid, sp, sc, slm, srm));
                        rewrite(id == parent); rewrite(pc == Color::Red);
                        rewrite(sc == Color::Black); rewrite(slm == RbTree::Empty); rewrite(srm == RbTree::Empty);
                        normalize();
                    }
                    apply(plug_parent_consistent_ctx(c.model, RbTree::Empty, 0));
                    have ctx_consistent(Context::Left(parent, above, Color::Red,
                        RbTree::Node(sid, sp, Color::Black, RbTree::Empty, RbTree::Empty), um), RbTree::Empty, 0) == 1 by {
                        rewrite(Context::Left(parent, above, Color::Red,
                            RbTree::Node(sid, sp, Color::Black, RbTree::Empty, RbTree::Empty), um) == c.model);
                        assumption();
                    }
                    apply(ctx_consistent_left_sibling(parent, above, Color::Red,
                        RbTree::Node(sid, sp, Color::Black, RbTree::Empty, RbTree::Empty), um, RbTree::Empty, 0));
                    apply(rb_parent_consistent_node_fixes_parent(sid, sp, Color::Black, RbTree::Empty, RbTree::Empty, parent));
                    have sp == parent by { simp(); }
                    have is_rb(RbTree::Empty) == 1 by { unfold(is_rb(RbTree::Empty)); normalize(); }
                    have rb_root_black(RbTree::Empty) == 1 by { unfold(rb_root_black(RbTree::Empty)); normalize(); }
                    have c.model == Context::Left(parent, above, Color::Red, RbTree::Node(sid, parent, Color::Black, RbTree::Empty, RbTree::Empty), um) by {
                        rewrite(c.model == Context::Left(parent, above, Color::Red, RbTree::Node(sid, sp, Color::Black, RbTree::Empty, RbTree::Empty), um)); rewrite(sp == parent); normalize();
                    }
                    have ctx_rb(Context::Left(parent, above, Color::Red, RbTree::Node(sid, parent, Color::Black, RbTree::Empty, RbTree::Empty), um), Nat::Succ(black_height(RbTree::Empty)), Color::Black) == 1 by {
                        rewrite(Context::Left(parent, above, Color::Red, RbTree::Node(sid, parent, Color::Black, RbTree::Empty, RbTree::Empty), um) == c.model); assumption();
                    }
                    have rb_parent_consistent(plug(Context::Left(parent, above, Color::Red, RbTree::Node(sid, parent, Color::Black, RbTree::Empty, RbTree::Empty), um), RbTree::Empty), 0) == 1 by {
                        rewrite(Context::Left(parent, above, Color::Red, RbTree::Node(sid, parent, Color::Black, RbTree::Empty, RbTree::Empty), um) == c.model); assumption();
                    }
                    apply(ctx_erase_case2_left_red_exit(above, parent, sid, RbTree::Empty, RbTree::Empty, RbTree::Empty, um));
                    let { sibling: s, up: u } = unfold(c);
                    let { left: sl, right: sr } = unfold(s);
                    unfold(sl); unfold(sr);
                    have parent->rb_left == 0 by { simp(); }
                    have parent->rb_right == sid by { simp(); }
                    have sid->rb_left == 0 by { simp(); }
                    have sid->rb_right == 0 by { simp(); }
                    have (sid->__rb_parent_color & 1) == 1 by {
                        rewrite((sid->__rb_parent_color & 1) == color_bit(Color::Black)); unfold(color_bit(Color::Black)); normalize();
                    }
                    have (parent->__rb_parent_color & 1) == 0 by {
                        rewrite((parent->__rb_parent_color & 1) == color_bit(Color::Red)); unfold(color_bit(Color::Red)); normalize();
                    }
                    have parent->__rb_parent_color == address(above) by {
                        rewrite(parent->__rb_parent_color == address(above) + (parent->__rb_parent_color & 1));
                        rewrite((parent->__rb_parent_color & 1) == 0); normalize();
                    }
                    execute_until(loop(0));
                    step(); # Enter the first loop iteration.
                    step(); # Read the right sibling.
                    step(); # Select the empty-left-child branch.
                    step(); step(); # Skip the red-sibling rotation.
                    step(); step(); step(); step(); # Both sibling children are null.
                    step(); # Recolor the sibling red.
                    step(); step(); # Select the red parent and blacken it.
                    have parent->__rb_parent_color == address(above) + 1 by { simp(); }
                    have (parent->__rb_parent_color & 1) == 1 by {
                        rewrite(parent->__rb_parent_color == address(above) + 1);
                        arithmetic() using { aligned(above, 8); }
                    }
                    have (sid->__rb_parent_color & 1) == 0 by { simp(); }
                    have sid->rb_left == 0 by { simp(); }
                    have sid->rb_right == 0 by { simp(); }
                    have parent->rb_left == 0 by { simp(); }
                    have parent->rb_right == sid by { simp(); }
                    let sl = fold(rb_at(sid->rb_left), { model: RbTree::Empty });
                    let sr = fold(rb_at(sid->rb_right), { model: RbTree::Empty });
                    let s = fold(rb_at(sid), { model: RbTree::Node(sid, parent, Color::Red, RbTree::Empty, RbTree::Empty) }, { left: sl, right: sr });
                    let t = fold(rb_at(parent->rb_left), { model: RbTree::Empty });
                    have rb_parent_is(RbTree::Empty, parent) == 1 by {
                        unfold(rb_parent_is(RbTree::Empty, parent)); normalize();
                    }
                    have rb_parent_is(s.model, parent) == 1 by {
                        rewrite(s.model == RbTree::Node(sid, parent, Color::Red, RbTree::Empty, RbTree::Empty));
                        unfold(rb_parent_is(RbTree::Node(sid, parent, Color::Red, RbTree::Empty, RbTree::Empty), parent)); normalize();
                    }
                    let sub = fold(rb_at(parent), { model: RbTree::Node(parent, above, Color::Black, RbTree::Empty, s.model) }, { left: t, right: s });
                    have rb_tree_parent_consistent(plug(u.model, sub.model)) == 1 by { unfold(rb_tree_parent_consistent(plug(u.model, sub.model))); simp(); }
                    mark closing_root;
                    let { whole: whole } = refold_to_root(parent, root, { c: u, t: sub });
                    have whole.model == plug(um, RbTree::Node(parent, above, Color::Black, RbTree::Empty, RbTree::Node(sid, parent, Color::Red, RbTree::Empty, RbTree::Empty))) by {
                        rewrite(whole.model == plug(at(closing_root, u.model), RbTree::Node(parent, above, Color::Black, RbTree::Empty, RbTree::Node(sid, parent, Color::Red, RbTree::Empty, RbTree::Empty))));
                        rewrite(at(closing_root, u.model) == um); normalize();
                    }
                    have whole.model == erase_left_red_flip(old(c.model)) by {
                        rewrite(whole.model == plug(um, RbTree::Node(parent, above, Color::Black, RbTree::Empty, RbTree::Node(sid, parent, Color::Red, RbTree::Empty, RbTree::Empty))));
                        rewrite(old(c.model) == Context::Left(parent, above, Color::Red, RbTree::Node(sid, parent, Color::Black, RbTree::Empty, RbTree::Empty), um));
                        unfold(erase_left_red_flip(Context::Left(parent, above, Color::Red, RbTree::Node(sid, parent, Color::Black, RbTree::Empty, RbTree::Empty), um)));
                        unfold(rb_recolor(RbTree::Node(sid, parent, Color::Black, RbTree::Empty, RbTree::Empty), Color::Red)); normalize();
                    }
                    have is_rb_root(whole.model) == 1 by {
                        rewrite(whole.model == plug(um, RbTree::Node(parent, above, Color::Black, RbTree::Empty, RbTree::Node(sid, parent, Color::Red, RbTree::Empty, RbTree::Empty)))); assumption();
                    }
                    have rb_parent_consistent(whole.model, 0) == 1 by {
                        rewrite(whole.model == plug(um, RbTree::Node(parent, above, Color::Black, RbTree::Empty, RbTree::Node(sid, parent, Color::Red, RbTree::Empty, RbTree::Empty)))); assumption();
                    }
                    have rb_inorder(whole.model) == rb_inorder(plug(old(c.model), RbTree::Empty)) by {
                        rewrite(whole.model == plug(um, RbTree::Node(parent, above, Color::Black, RbTree::Empty, RbTree::Node(sid, parent, Color::Red, RbTree::Empty, RbTree::Empty))));
                        rewrite(old(c.model) == Context::Left(parent, above, Color::Red, RbTree::Node(sid, parent, Color::Black, RbTree::Empty, RbTree::Empty), um)); assumption();
                    }
                    execute(); simp();
                },
            }
        },
    }
}
