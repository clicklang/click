verifying "rb_erase_color.c";
import "../rbtree-model/rbtree_spine_resources.click";

function erase_black_root_left(ctx: Context, parent: struct rb_node*) -> int32 {
    match ctx {
        Context::Top => 0,
        Context::Right(id, above, color, sibling, up) => 0,
        Context::Left(id, above, color, sibling, up) =>
        if id == parent {
            if above == 0 {
                if up == Context::Top {
                    if color == Color::Black {
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
                } else { 0 }
            } else { 0 }
        } else { 0 },
    }
}

function erase_black_root_left_result(ctx: Context) -> RbTree {
    match ctx {
        Context::Top => RbTree::Empty,
        Context::Left(id, above, color, sibling, up) =>
        RbTree::Node(id, above, Color::Black, RbTree::Empty, rb_recolor(sibling, Color::Red)),
        Context::Right(id, above, color, sibling, up) => RbTree::Empty,
    }
}

void ____rb_erase_color(struct rb_node* parent, struct rb_root* root,
    void (*augment_rotate)(struct rb_node* old, struct rb_node* new)) {
    consumes c: ctx_at(0, root);
    requires erase_black_root_left(c.model, parent) == 1;
    requires ctx_rb(c.model, Nat::Succ(black_height(RbTree::Empty)), Color::Black) == 1;
    requires rb_parent_consistent(plug(c.model, RbTree::Empty), 0) == 1;
    produces whole: rb_root_at(root);
    ensures whole.model == erase_black_root_left_result(old(c.model));
    ensures is_rb_root(whole.model) == 1;
    ensures rb_parent_consistent(whole.model, 0) == 1;
    ensures rb_inorder(whole.model) == rb_inorder(plug(old(c.model), RbTree::Empty));
} by {
    match c.model {
        Context::Top => {
            have erase_black_root_left(c.model, parent) == 0 by {
                rewrite(c.model == Context::Top); unfold(erase_black_root_left(Context::Top, parent)); normalize();
            }
            have not(erase_black_root_left(c.model, parent) == 1) by { rewrite(erase_black_root_left(c.model, parent) == 0); normalize(); }
            contradiction(erase_black_root_left(c.model, parent) == 1);
        },
        Context::Right(id, above, pc, sm, um) => {
            have erase_black_root_left(c.model, parent) == 0 by {
                rewrite(c.model == Context::Right(id, above, pc, sm, um)); unfold(erase_black_root_left(Context::Right(id, above, pc, sm, um), parent)); normalize();
            }
            have not(erase_black_root_left(c.model, parent) == 1) by { rewrite(erase_black_root_left(c.model, parent) == 0); normalize(); }
            contradiction(erase_black_root_left(c.model, parent) == 1);
        },
        Context::Left(id, above, pc, sm, um) => {
            have id == parent by {
                if id == parent { assumption(); } else {
                    have erase_black_root_left(c.model, parent) == 0 by {
                        rewrite(c.model == Context::Left(id, above, pc, sm, um)); unfold(erase_black_root_left(Context::Left(id, above, pc, sm, um), parent));
                        normalize() using { not(id == parent); }
                    }
                    have not(erase_black_root_left(c.model, parent) == 1) by { rewrite(erase_black_root_left(c.model, parent) == 0); normalize(); }
                    contradiction(erase_black_root_left(c.model, parent) == 1);
                }
            }
            have above == 0 by {
                if above == 0 { assumption(); } else {
                    have erase_black_root_left(c.model, parent) == 0 by {
                        rewrite(c.model == Context::Left(id, above, pc, sm, um)); unfold(erase_black_root_left(Context::Left(id, above, pc, sm, um), parent));
                        normalize() using { id == parent; not(above == 0); }
                    }
                    have not(erase_black_root_left(c.model, parent) == 1) by { rewrite(erase_black_root_left(c.model, parent) == 0); normalize(); }
                    contradiction(erase_black_root_left(c.model, parent) == 1);
                }
            }
            have um == Context::Top by {
                if um == Context::Top { assumption(); } else {
                    have erase_black_root_left(c.model, parent) == 0 by {
                        rewrite(c.model == Context::Left(id, above, pc, sm, um)); unfold(erase_black_root_left(Context::Left(id, above, pc, sm, um), parent));
                        normalize() using { id == parent; above == 0; not(um == Context::Top); }
                    }
                    have not(erase_black_root_left(c.model, parent) == 1) by { rewrite(erase_black_root_left(c.model, parent) == 0); normalize(); }
                    contradiction(erase_black_root_left(c.model, parent) == 1);
                }
            }
            have pc == Color::Black by {
                if pc == Color::Black { assumption(); } else {
                    have erase_black_root_left(c.model, parent) == 0 by {
                        rewrite(c.model == Context::Left(id, above, pc, sm, um)); unfold(erase_black_root_left(Context::Left(id, above, pc, sm, um), parent));
                        normalize() using { id == parent; above == 0; um == Context::Top; not(pc == Color::Black); }
                    }
                    have not(erase_black_root_left(c.model, parent) == 1) by { rewrite(erase_black_root_left(c.model, parent) == 0); normalize(); }
                    contradiction(erase_black_root_left(c.model, parent) == 1);
                }
            }
            match sm {
                RbTree::Empty => {
                    have erase_black_root_left(c.model, parent) == 0 by {
                        rewrite(c.model == Context::Left(id, above, pc, sm, um)); rewrite(sm == RbTree::Empty);
                        unfold(erase_black_root_left(Context::Left(id, above, pc, RbTree::Empty, um), parent));
                        normalize() using { id == parent; above == 0; um == Context::Top; pc == Color::Black; }
                    }
                    have not(erase_black_root_left(c.model, parent) == 1) by { rewrite(erase_black_root_left(c.model, parent) == 0); normalize(); }
                    contradiction(erase_black_root_left(c.model, parent) == 1);
                },
                RbTree::Node(sid, sp, sc, slm, srm) => {
                    have sc == Color::Black by {
                        if sc == Color::Black { assumption(); } else {
                            have erase_black_root_left(c.model, parent) == 0 by {
                                rewrite(c.model == Context::Left(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, sp, sc, slm, srm)); unfold(erase_black_root_left(Context::Left(id, above, pc, RbTree::Node(sid, sp, sc, slm, srm), um), parent));
                                normalize() using { id == parent; above == 0; um == Context::Top; pc == Color::Black; not(sc == Color::Black); }
                            }
                            have not(erase_black_root_left(c.model, parent) == 1) by { rewrite(erase_black_root_left(c.model, parent) == 0); normalize(); }
                            contradiction(erase_black_root_left(c.model, parent) == 1);
                        }
                    }
                    have slm == RbTree::Empty by {
                        if slm == RbTree::Empty { assumption(); } else {
                            have erase_black_root_left(c.model, parent) == 0 by {
                                rewrite(c.model == Context::Left(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, sp, sc, slm, srm)); unfold(erase_black_root_left(Context::Left(id, above, pc, RbTree::Node(sid, sp, sc, slm, srm), um), parent));
                                normalize() using { id == parent; above == 0; um == Context::Top; pc == Color::Black; sc == Color::Black; not(slm == RbTree::Empty); }
                            }
                            have not(erase_black_root_left(c.model, parent) == 1) by { rewrite(erase_black_root_left(c.model, parent) == 0); normalize(); }
                            contradiction(erase_black_root_left(c.model, parent) == 1);
                        }
                    }
                    have srm == RbTree::Empty by {
                        if srm == RbTree::Empty { assumption(); } else {
                            have erase_black_root_left(c.model, parent) == 0 by {
                                rewrite(c.model == Context::Left(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, sp, sc, slm, srm)); unfold(erase_black_root_left(Context::Left(id, above, pc, RbTree::Node(sid, sp, sc, slm, srm), um), parent));
                                normalize() using { id == parent; above == 0; um == Context::Top; pc == Color::Black; sc == Color::Black; slm == RbTree::Empty; not(srm == RbTree::Empty); }
                            }
                            have not(erase_black_root_left(c.model, parent) == 1) by { rewrite(erase_black_root_left(c.model, parent) == 0); normalize(); }
                            contradiction(erase_black_root_left(c.model, parent) == 1);
                        }
                    }
                    have c.model == Context::Left(id, 0, Color::Black, RbTree::Node(sid, sp, Color::Black, RbTree::Empty, RbTree::Empty), Context::Top) by {
                        rewrite(c.model == Context::Left(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, sp, sc, slm, srm));
                        rewrite(above == 0); rewrite(um == Context::Top); rewrite(pc == Color::Black);
                        rewrite(sc == Color::Black); rewrite(slm == RbTree::Empty); rewrite(srm == RbTree::Empty); normalize();
                    }
                    apply(plug_parent_consistent_ctx(c.model, RbTree::Empty, 0));
                    have ctx_consistent(Context::Left(id, 0, Color::Black, RbTree::Node(sid, sp, Color::Black, RbTree::Empty, RbTree::Empty), Context::Top), RbTree::Empty, 0) == 1 by { rewrite(Context::Left(id, 0, Color::Black, RbTree::Node(sid, sp, Color::Black, RbTree::Empty, RbTree::Empty), Context::Top) == c.model); assumption(); }
                    apply(ctx_consistent_left_sibling(id, 0, Color::Black, RbTree::Node(sid, sp, Color::Black, RbTree::Empty, RbTree::Empty), Context::Top, RbTree::Empty, 0));
                    apply(rb_parent_consistent_node_fixes_parent(sid, sp, Color::Black, RbTree::Empty, RbTree::Empty, id));
                    have sp == id by { assumption(); }
                    have c.model == Context::Left(id, 0, Color::Black, RbTree::Node(sid, id, Color::Black, RbTree::Empty, RbTree::Empty), Context::Top) by { rewrite(c.model == Context::Left(id, 0, Color::Black, RbTree::Node(sid, sp, Color::Black, RbTree::Empty, RbTree::Empty), Context::Top)); rewrite(sp == id); normalize(); }
                    have ctx_rb(Context::Left(id, 0, Color::Black, RbTree::Node(sid, id, Color::Black, RbTree::Empty, RbTree::Empty), Context::Top), Nat::Succ(black_height(RbTree::Empty)), Color::Black) == 1 by { rewrite(Context::Left(id, 0, Color::Black, RbTree::Node(sid, id, Color::Black, RbTree::Empty, RbTree::Empty), Context::Top) == c.model); assumption(); }
                    have rb_parent_consistent(plug(Context::Left(id, 0, Color::Black, RbTree::Node(sid, id, Color::Black, RbTree::Empty, RbTree::Empty), Context::Top), RbTree::Empty), 0) == 1 by { rewrite(Context::Left(id, 0, Color::Black, RbTree::Node(sid, id, Color::Black, RbTree::Empty, RbTree::Empty), Context::Top) == c.model); assumption(); }
                    have is_rb(RbTree::Empty) == 1 by { unfold(is_rb(RbTree::Empty)); normalize(); }
                    have rb_root_black(RbTree::Empty) == 1 by { unfold(rb_root_black(RbTree::Empty)); normalize(); }
                    apply(ctx_erase_case2_left_black_step(0, id, sid, RbTree::Empty, RbTree::Empty, RbTree::Empty, Context::Top));
                    apply(is_rb_root_from_parts(RbTree::Node(id, 0, Color::Black, RbTree::Empty, RbTree::Node(sid, id, Color::Red, RbTree::Empty, RbTree::Empty))));
                    let { sibling: s, up: u } = unfold(c);
                    let { left: sl, right: sr } = unfold(s);
                    unfold(sl); unfold(sr); unfold(u);
                    have root->rb_node == id by { simp(); }
                    have parent->rb_left == 0 by { simp(); }
                    have parent->rb_right == sid by { simp(); }
                    have sid->rb_left == 0 by { simp(); }
                    have sid->rb_right == 0 by { simp(); }
                    have (sid->__rb_parent_color & 1) == 1 by {
                        rewrite((sid->__rb_parent_color & 1) == color_bit(Color::Black)); unfold(color_bit(Color::Black)); normalize();
                    }
                    have (id->__rb_parent_color & 1) == 1 by {
                        rewrite((id->__rb_parent_color & 1) == color_bit(Color::Black)); unfold(color_bit(Color::Black)); normalize();
                    }
                    have id->__rb_parent_color == 1 by {
                        rewrite(id->__rb_parent_color == address(0) + (id->__rb_parent_color & 1));
                        rewrite((id->__rb_parent_color & 1) == 1); normalize();
                    }
                    execute_until(loop(0));
                    # The color flip, black-parent branch, and two cursor assignments.
                    step(); # Enter the first loop iteration.
                    step(); step(); # Read the sibling and select the empty-left-child case.
                    step(); step(); # Skip the red-sibling rotation.
                    step(); step(); step(); step(); # Both sibling children are null.
                    step(); # Recolor the sibling red.
                    step(); # Select the black-parent branch.
                    step(); step(); # Move to the root and decode its null parent.
                    have parent == 0 by { simp(); }
                    have node == id by { simp(); }
                    have id->__rb_parent_color == 1 by { simp(); }
                    have (sid->__rb_parent_color & 1) == 0 by { simp(); }
                    have sid->rb_left == 0 by { simp(); }
                    have sid->rb_right == 0 by { simp(); }
                    let sl = fold(rb_at(sid->rb_left), { model: RbTree::Empty });
                    let sr = fold(rb_at(sid->rb_right), { model: RbTree::Empty });
                    have (sid->__rb_parent_color & 1) == color_bit(Color::Red) by {
                        unfold(color_bit(Color::Red)); simp();
                    }
                    let s = fold(rb_at(sid), { model: RbTree::Node(sid, id, Color::Red, RbTree::Empty, RbTree::Empty) }, { left: sl, right: sr });
                    let t = fold(rb_at(id->rb_left), { model: RbTree::Empty });
                    have rb_parent_is(RbTree::Empty, id) == 1 by { unfold(rb_parent_is(RbTree::Empty, id)); normalize(); }
                    have rb_parent_is(s.model, id) == 1 by {
                        rewrite(s.model == RbTree::Node(sid, id, Color::Red, RbTree::Empty, RbTree::Empty));
                        unfold(rb_parent_is(RbTree::Node(sid, id, Color::Red, RbTree::Empty, RbTree::Empty), id)); normalize();
                    }
                    let sub = fold(rb_at(id), { model: RbTree::Node(id, 0, Color::Black, RbTree::Empty, RbTree::Node(sid, id, Color::Red, RbTree::Empty, RbTree::Empty)) }, { left: t, right: s });
                    let whole = fold(rb_root_at(root), { model: RbTree::Node(id, 0, Color::Black, RbTree::Empty, RbTree::Node(sid, id, Color::Red, RbTree::Empty, RbTree::Empty)) }, { tree: sub });
                    have whole.model == erase_black_root_left_result(old(c.model)) by {
                        rewrite(whole.model == RbTree::Node(id, 0, Color::Black, RbTree::Empty, RbTree::Node(sid, id, Color::Red, RbTree::Empty, RbTree::Empty))); rewrite(old(c.model) == Context::Left(id, 0, Color::Black, RbTree::Node(sid, id, Color::Black, RbTree::Empty, RbTree::Empty), Context::Top));
                        unfold(erase_black_root_left_result(Context::Left(id, 0, Color::Black, RbTree::Node(sid, id, Color::Black, RbTree::Empty, RbTree::Empty), Context::Top)));
                        unfold(rb_recolor(RbTree::Node(sid, id, Color::Black, RbTree::Empty, RbTree::Empty), Color::Red)); normalize();
                    }
                    have is_rb_root(whole.model) == 1 by { rewrite(whole.model == RbTree::Node(id, 0, Color::Black, RbTree::Empty, RbTree::Node(sid, id, Color::Red, RbTree::Empty, RbTree::Empty))); assumption(); }
                    have rb_parent_consistent(whole.model, 0) == 1 by {
                        rewrite(whole.model == RbTree::Node(id, 0, Color::Black, RbTree::Empty, RbTree::Node(sid, id, Color::Red, RbTree::Empty, RbTree::Empty)));
                        have plug(Context::Top, RbTree::Node(id, 0, Color::Black, RbTree::Empty, RbTree::Node(sid, id, Color::Red, RbTree::Empty, RbTree::Empty))) == RbTree::Node(id, 0, Color::Black, RbTree::Empty, RbTree::Node(sid, id, Color::Red, RbTree::Empty, RbTree::Empty)) by { unfold(plug(Context::Top, RbTree::Node(id, 0, Color::Black, RbTree::Empty, RbTree::Node(sid, id, Color::Red, RbTree::Empty, RbTree::Empty)))); normalize(); }
                        rewrite(RbTree::Node(id, 0, Color::Black, RbTree::Empty, RbTree::Node(sid, id, Color::Red, RbTree::Empty, RbTree::Empty)) == plug(Context::Top, RbTree::Node(id, 0, Color::Black, RbTree::Empty, RbTree::Node(sid, id, Color::Red, RbTree::Empty, RbTree::Empty)))); assumption();
                    }
                    have rb_inorder(whole.model) == rb_inorder(plug(old(c.model), RbTree::Empty)) by {
                        rewrite(whole.model == RbTree::Node(id, 0, Color::Black, RbTree::Empty, RbTree::Node(sid, id, Color::Red, RbTree::Empty, RbTree::Empty))); rewrite(old(c.model) == Context::Left(id, 0, Color::Black, RbTree::Node(sid, id, Color::Black, RbTree::Empty, RbTree::Empty), Context::Top));
                        have plug(Context::Top, RbTree::Node(id, 0, Color::Black, RbTree::Empty, RbTree::Node(sid, id, Color::Red, RbTree::Empty, RbTree::Empty))) == RbTree::Node(id, 0, Color::Black, RbTree::Empty, RbTree::Node(sid, id, Color::Red, RbTree::Empty, RbTree::Empty)) by { unfold(plug(Context::Top, RbTree::Node(id, 0, Color::Black, RbTree::Empty, RbTree::Node(sid, id, Color::Red, RbTree::Empty, RbTree::Empty)))); normalize(); }
                        rewrite(RbTree::Node(id, 0, Color::Black, RbTree::Empty, RbTree::Node(sid, id, Color::Red, RbTree::Empty, RbTree::Empty)) == plug(Context::Top, RbTree::Node(id, 0, Color::Black, RbTree::Empty, RbTree::Node(sid, id, Color::Red, RbTree::Empty, RbTree::Empty)))); assumption();
                    }
                    execute(); simp();
                },
            }
        },
    }
}
