// Erase-color cases 1, 3, and 4 for an empty right deficit and a red sibling.
// Its black near child has a red inner leaf. Under any outer context, the proof
// returns the exact balanced root with consistent parents and unchanged in-order nodes.
verifying "rb_erase_color.c";
import "../rbtree-model/rbtree_spine_resources.click";

void __rb_change_child(struct rb_node* old, struct rb_node* new,
                       struct rb_node* parent, struct rb_root* root) {
    consumes before: ctx_at(old, root);
    owns old->__rb_parent_color;
    requires old != 0;
    requires ctx_node_is(before.model, parent) == 1;
    produces after: ctx_at(new, root);
    ensures after.model == old(before.model);
    ensures old->__rb_parent_color == old(old->__rb_parent_color);
} by {
    have old != 0 by { assumption(); }
    match before.model {
        Context::Top => {
            have parent == 0 by {
                have ctx_node_is(Context::Top, parent) == 1 by {
                    rewrite(Context::Top == before.model); assumption();
                }
                if parent == 0 { assumption(); } else {
                    have ctx_node_is(Context::Top, parent) != 1 by {
                        unfold(ctx_node_is(Context::Top, parent)); normalize() using { not(parent == 0); };
                    }
                    contradiction(ctx_node_is(Context::Top, parent) == 1);
                }
            }
            unfold(before);
            execute();
            let after = fold(ctx_at(new, root), { model: Context::Top });
            simp();
        },
        Context::Left(identity, grandparent, color, sibling_model, outer_model) => {
            have parent == identity by {
                have ctx_node_is(Context::Left(identity, grandparent, color, sibling_model, outer_model), parent) == 1 by {
                    rewrite(Context::Left(identity, grandparent, color, sibling_model, outer_model) == before.model); assumption();
                }
                if parent == identity { assumption(); } else {
                    have ctx_node_is(Context::Left(identity, grandparent, color, sibling_model, outer_model), parent) != 1 by {
                        unfold(ctx_node_is(Context::Left(identity, grandparent, color, sibling_model, outer_model), parent)); normalize() using { not(parent == identity); };
                    }
                    contradiction(ctx_node_is(Context::Left(identity, grandparent, color, sibling_model, outer_model), parent) == 1);
                }
            }
            let { sibling: sibling, up: outer } = unfold(before);
            execute();
            let after = fold(ctx_at(new, root), {
                model: Context::Left(identity, grandparent, color, sibling_model, outer_model)
            }, { sibling: sibling, up: outer });
            simp();
        },
        Context::Right(identity, grandparent, color, sibling_model, outer_model) => {
            have parent == identity by {
                have ctx_node_is(Context::Right(identity, grandparent, color, sibling_model, outer_model), parent) == 1 by {
                    rewrite(Context::Right(identity, grandparent, color, sibling_model, outer_model) == before.model); assumption();
                }
                if parent == identity { assumption(); } else {
                    have ctx_node_is(Context::Right(identity, grandparent, color, sibling_model, outer_model), parent) != 1 by {
                        unfold(ctx_node_is(Context::Right(identity, grandparent, color, sibling_model, outer_model), parent)); normalize() using { not(parent == identity); };
                    }
                    contradiction(ctx_node_is(Context::Right(identity, grandparent, color, sibling_model, outer_model), parent) == 1);
                }
            }
            let { sibling: sibling, up: outer } = unfold(before);
            match sibling.model {
                RbTree::Empty => {
                    unfold(sibling);
                    have identity->rb_left == 0 by { simp(); }
                    have parent->rb_left == 0 by { simp(); }
                    have old != 0 by { assumption(); }
                    have parent->rb_left != old by {
                        if parent->rb_left == old {
                            have old == 0 by { normalize() using { parent->rb_left == old; parent->rb_left == 0; } }
                            contradiction(old != 0);
                        } else { assumption(); }
                    }
                    execute();
                    let sibling = fold(rb_at(parent->rb_left), { model: RbTree::Empty });
                    let after = fold(ctx_at(new, root), {
                        model: Context::Right(identity, grandparent, color, sibling_model, outer_model)
                    }, { sibling: sibling, up: outer });
                    simp();
                },
                RbTree::Node(sid, sp, sc, sl, sr) => {
                    let { left: left, right: right } = unfold(sibling);
                    execute();
                    let sibling = fold(rb_at(parent->rb_left), {
                        model: RbTree::Node(sid, sp, sc, sl, sr)
                    }, { left: left, right: right });
                    let after = fold(ctx_at(new, root), {
                        model: Context::Right(identity, grandparent, color, sibling_model, outer_model)
                    }, { sibling: sibling, up: outer });
                    simp();
                },
            }
        },
    }
}

function ctx_parent_word(ctx: Context, word: uint64) -> int32 {
    match ctx {
        Context::Top => if word == 0 { 1 } else { if word == 1 { 1 } else { 0 } },
        Context::Left(id, above, pc, sibling, up) => if word == address(id) { 1 } else { if word == address(id) + 1 { 1 } else { 0 } },
        Context::Right(id, above, pc, sibling, up) => if word == address(id) { 1 } else { if word == address(id) + 1 { 1 } else { 0 } },
    }
}

void __rb_rotate_set_parents(struct rb_node* old, struct rb_node* new,
                             struct rb_root* root, int32 color) {
    consumes c: ctx_at(old, root);
    owns old->__rb_parent_color;
    owns new->__rb_parent_color;
    requires old != 0;
    requires new != 0;
    requires aligned(new, 8);
    requires 0 <= color;
    requires color <= 1;
    requires ctx_parent_word(c.model, old->__rb_parent_color) == 1;
    produces after: ctx_at(new, root);
    ensures after.model == old(c.model);
    ensures new->__rb_parent_color == old(old->__rb_parent_color);
    ensures old->__rb_parent_color == address(new) + color;
} by {
    match c.model {
        Context::Top => {
            unfold(c);
            let d = fold(ctx_at(old, root), { model: Context::Top });
            have ctx_parent_word(d.model, old->__rb_parent_color) == 1 by { rewrite(d.model == Context::Top); rewrite(Context::Top == old(c.model)); assumption(); }
            have (old->__rb_parent_color & ~3) == 0 by {
                if old->__rb_parent_color == 0 {
                    rewrite(old->__rb_parent_color == 0); normalize();
                } else {
                    have old->__rb_parent_color == 1 by {
                        if old->__rb_parent_color == 1 { assumption(); } else {
                            have ctx_parent_word(d.model, old->__rb_parent_color) == 0 by {
                                rewrite(d.model == Context::Top); unfold(ctx_parent_word(Context::Top, old->__rb_parent_color));
                                normalize() using { not(old->__rb_parent_color == 0); not(old->__rb_parent_color == 1); }
                            }
                            have not(ctx_parent_word(d.model, old->__rb_parent_color) == 1) by { rewrite(ctx_parent_word(d.model, old->__rb_parent_color) == 0); normalize(); }
                            contradiction(ctx_parent_word(d.model, old->__rb_parent_color) == 1);
                        }
                    }
                    rewrite(old->__rb_parent_color == 1); normalize();
                }
            }
            step(); step();
            have parent == 0 by { simp(); }
            have ctx_node_is(d.model, parent) == 1 by { rewrite(d.model == Context::Top); rewrite(parent == 0); unfold(ctx_node_is(Context::Top, 0)); normalize(); }
            step(); step();
            have old->__rb_parent_color == (address(new) | color) by { simp(); }
            have old->__rb_parent_color == address(new) + color by {
                rewrite(old->__rb_parent_color == (address(new) | color));
                if color == 0 { rewrite(color == 0); normalize(); } else {
                    have color == 1 by { arithmetic() using { 0 <= color; color <= 1; not(color == 0); } }
                    rewrite(color == 1);
                    arithmetic() using { aligned(new, 8); }
                }
            }
            mark words;
            have at(words, old->__rb_parent_color) == address(new) + color by { assumption(); }
            let { after: after } = step(__rb_change_child(old, new, parent, root), { before: d });
            have old->__rb_parent_color == address(new) + color by {
                have old->__rb_parent_color == at(words, old->__rb_parent_color) by { simp(); }
                rewrite(old->__rb_parent_color == at(words, old->__rb_parent_color)); assumption();
            }
            execute(); simp();
        },
        Context::Left(id, above, pc, sibling, up) => {
            let { sibling: s, up: u } = unfold(c);
            let d = fold(ctx_at(old, root), { model: Context::Left(id, above, pc, sibling, up) }, { sibling: s, up: u });
            have ctx_parent_word(d.model, old->__rb_parent_color) == 1 by { rewrite(d.model == Context::Left(id, above, pc, sibling, up)); rewrite(Context::Left(id, above, pc, sibling, up) == old(c.model)); assumption(); }
            have (old->__rb_parent_color & ~3) == address(id) by {
                if old->__rb_parent_color == address(id) {
                    arithmetic() using { old->__rb_parent_color == address(id); aligned(id, 8); }
                } else {
                    have old->__rb_parent_color == address(id) + 1 by {
                        if old->__rb_parent_color == address(id) + 1 { assumption(); } else {
                            have ctx_parent_word(d.model, old->__rb_parent_color) == 0 by {
                                rewrite(d.model == Context::Left(id, above, pc, sibling, up)); unfold(ctx_parent_word(Context::Left(id, above, pc, sibling, up), old->__rb_parent_color));
                                normalize() using { not(old->__rb_parent_color == address(id)); not(old->__rb_parent_color == address(id) + 1); }
                            }
                            have not(ctx_parent_word(d.model, old->__rb_parent_color) == 1) by { rewrite(ctx_parent_word(d.model, old->__rb_parent_color) == 0); normalize(); }
                            contradiction(ctx_parent_word(d.model, old->__rb_parent_color) == 1);
                        }
                    }
                    arithmetic() using { old->__rb_parent_color == address(id) + 1; aligned(id, 8); }
                }
            }
            step(); step();
            have parent == id by { simp(); }
            have ctx_node_is(d.model, parent) == 1 by { rewrite(d.model == Context::Left(id, above, pc, sibling, up)); rewrite(parent == id); unfold(ctx_node_is(Context::Left(id, above, pc, sibling, up), id)); normalize(); }
            step(); step();
            have old->__rb_parent_color == (address(new) | color) by { simp(); }
            have old->__rb_parent_color == address(new) + color by {
                rewrite(old->__rb_parent_color == (address(new) | color));
                if color == 0 { rewrite(color == 0); normalize(); } else {
                    have color == 1 by { arithmetic() using { 0 <= color; color <= 1; not(color == 0); } }
                    rewrite(color == 1);
                    arithmetic() using { aligned(new, 8); }
                }
            }
            mark words;
            have at(words, old->__rb_parent_color) == address(new) + color by { assumption(); }
            let { after: after } = step(__rb_change_child(old, new, parent, root), { before: d });
            have old->__rb_parent_color == address(new) + color by {
                have old->__rb_parent_color == at(words, old->__rb_parent_color) by { simp(); }
                rewrite(old->__rb_parent_color == at(words, old->__rb_parent_color)); assumption();
            }
            execute(); simp();
        },
        Context::Right(id, above, pc, sibling, up) => {
            let { sibling: s, up: u } = unfold(c);
            let d = fold(ctx_at(old, root), { model: Context::Right(id, above, pc, sibling, up) }, { sibling: s, up: u });
            have ctx_parent_word(d.model, old->__rb_parent_color) == 1 by { rewrite(d.model == Context::Right(id, above, pc, sibling, up)); rewrite(Context::Right(id, above, pc, sibling, up) == old(c.model)); assumption(); }
            have (old->__rb_parent_color & ~3) == address(id) by {
                if old->__rb_parent_color == address(id) {
                    arithmetic() using { old->__rb_parent_color == address(id); aligned(id, 8); }
                } else {
                    have old->__rb_parent_color == address(id) + 1 by {
                        if old->__rb_parent_color == address(id) + 1 { assumption(); } else {
                            have ctx_parent_word(d.model, old->__rb_parent_color) == 0 by {
                                rewrite(d.model == Context::Right(id, above, pc, sibling, up)); unfold(ctx_parent_word(Context::Right(id, above, pc, sibling, up), old->__rb_parent_color));
                                normalize() using { not(old->__rb_parent_color == address(id)); not(old->__rb_parent_color == address(id) + 1); }
                            }
                            have not(ctx_parent_word(d.model, old->__rb_parent_color) == 1) by { rewrite(ctx_parent_word(d.model, old->__rb_parent_color) == 0); normalize(); }
                            contradiction(ctx_parent_word(d.model, old->__rb_parent_color) == 1);
                        }
                    }
                    arithmetic() using { old->__rb_parent_color == address(id) + 1; aligned(id, 8); }
                }
            }
            step(); step();
            have parent == id by { simp(); }
            have ctx_node_is(d.model, parent) == 1 by { rewrite(d.model == Context::Right(id, above, pc, sibling, up)); rewrite(parent == id); unfold(ctx_node_is(Context::Right(id, above, pc, sibling, up), id)); normalize(); }
            step(); step();
            have old->__rb_parent_color == (address(new) | color) by { simp(); }
            have old->__rb_parent_color == address(new) + color by {
                rewrite(old->__rb_parent_color == (address(new) | color));
                if color == 0 { rewrite(color == 0); normalize(); } else {
                    have color == 1 by { arithmetic() using { 0 <= color; color <= 1; not(color == 0); } }
                    rewrite(color == 1);
                    arithmetic() using { aligned(new, 8); }
                }
            }
            mark words;
            have at(words, old->__rb_parent_color) == address(new) + color by { assumption(); }
            let { after: after } = step(__rb_change_child(old, new, parent, root), { before: d });
            have old->__rb_parent_color == address(new) + color by {
                have old->__rb_parent_color == at(words, old->__rb_parent_color) by { simp(); }
                rewrite(old->__rb_parent_color == at(words, old->__rb_parent_color)); assumption();
            }
            execute(); simp();
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



theorem color_bit_nonzero_is_one(color: Color) {
    requires not(color_bit(color) == 0);
    ensures color_bit(color) == 1 by {
        induct(color) as ih {
            Color::Red => {
                have color_bit(Color::Red) == 0 by { unfold(color_bit(Color::Red)); normalize(); }
                contradiction(color_bit(Color::Red) == 0);
            }
            Color::Black => { unfold(color_bit(Color::Black)); normalize(); }
        }
    }
}

theorem ctx_parent_word_from_color(ctx: Context, parent: struct rb_node*, word: uint64, color: Color) {
    requires ctx_node_is(ctx, parent) == 1;
    requires word == address(parent) + color_bit(color);
    ensures ctx_parent_word(ctx, word) == 1 by {
        induct(ctx) as ih {
Context::Top => {
 have parent == 0 by { apply(ctx_node_is_top_null(parent)); assumption(); }
 if color_bit(color) == 0 {
have word == 0 by { rewrite(word == address(parent) + color_bit(color)); rewrite(parent == 0); rewrite(color_bit(color) == 0); normalize(); }
 have ctx_parent_word(Context::Top, 0) == 1 by { unfold(ctx_parent_word(Context::Top, 0)); normalize(); }
 rewrite(word == 0); assumption();
} else {
 apply(color_bit_nonzero_is_one(color));
have word == 1 by { rewrite(word == address(parent) + color_bit(color)); rewrite(parent == 0); rewrite(color_bit(color) == 1); normalize(); }
 rewrite(word == 1); unfold(ctx_parent_word(Context::Top, 1)); normalize();
}
}
Context::Left(id, above, pc, sibling, up) => {
 have parent == id by { apply(ctx_node_is_left_identity(id, above, pc, sibling, up, parent)); assumption(); }
 if color_bit(color) == 0 {
have word == address(id) by { rewrite(word == address(parent) + color_bit(color)); rewrite(parent == id); rewrite(color_bit(color) == 0); normalize(); }
 rewrite(word == address(id)); unfold(ctx_parent_word(Context::Left(id, above, pc, sibling, up), address(id))); normalize();
} else {
 apply(color_bit_nonzero_is_one(color));
have word == address(id) + 1 by { rewrite(word == address(parent) + color_bit(color)); rewrite(parent == id); rewrite(color_bit(color) == 1); normalize(); }
 rewrite(word == address(id) + 1); unfold(ctx_parent_word(Context::Left(id, above, pc, sibling, up), address(id) + 1)); normalize();
}
}
Context::Right(id, above, pc, sibling, up) => {
 have parent == id by { apply(ctx_node_is_right_identity(id, above, pc, sibling, up, parent)); assumption(); }
 if color_bit(color) == 0 {
have word == address(id) by { rewrite(word == address(parent) + color_bit(color)); rewrite(parent == id); rewrite(color_bit(color) == 0); normalize(); }
 rewrite(word == address(id)); unfold(ctx_parent_word(Context::Right(id, above, pc, sibling, up), address(id))); normalize();
} else {
 apply(color_bit_nonzero_is_one(color));
have word == address(id) + 1 by { rewrite(word == address(parent) + color_bit(color)); rewrite(parent == id); rewrite(color_bit(color) == 1); normalize(); }
 rewrite(word == address(id) + 1); unfold(ctx_parent_word(Context::Right(id, above, pc, sibling, up), address(id) + 1)); normalize();
}
}
}
}
}

function erase_right_red_sibling_inner(ctx: Context, parent: struct rb_node*) -> int32 {
match ctx { Context::Top => 0, Context::Left(id, above, pc, sm, um) => 0,
Context::Right(id, above, pc, sm, um) => if id == parent { if pc == Color::Black { match sm { RbTree::Empty => 0, RbTree::Node(sid, sp, sc, far_model, near_model) => if sc == Color::Red { match near_model { RbTree::Empty => 0, RbTree::Node(nid, np, nc, nrm, nlm) => if nc == Color::Black { if nrm == RbTree::Empty { match nlm { RbTree::Empty => 0, RbTree::Node(rid, rp, rc, rrm, rlm) => if rc == Color::Red { if rlm == RbTree::Empty { if rrm == RbTree::Empty { 1 } else { 0 } } else { 0 } } else { 0 }, } } else { 0 } } else { 0 }, } } else { 0 }, } } else { 0 } } else { 0 }, }
}
function erase_right_red_sibling_inner_result(ctx: Context) -> RbTree {
match ctx { Context::Top => RbTree::Empty, Context::Left(id, above, pc, sm, um) => RbTree::Empty,
Context::Right(id, above, pc, sm, um) => match sm { RbTree::Empty => RbTree::Empty, RbTree::Node(sid, sp, sc, far_model, near_model) => match near_model {
RbTree::Empty => RbTree::Empty, RbTree::Node(nid, np, nc, nrm, nlm) => match nlm { RbTree::Empty => RbTree::Empty, RbTree::Node(rid, rp, rc, rrm, rlm) => plug(um, RbTree::Node(sid, above, Color::Black, far_model, RbTree::Node(rid, sid, Color::Red, RbTree::Node(nid, rid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(id, rid, Color::Black, RbTree::Empty, RbTree::Empty)))), },
}, }, }
}
contract void AugmentRotate(struct rb_node* old, struct rb_node* new) { requires new != 0; ensures 1 == 1; }
void ____rb_erase_color(struct rb_node* parent, struct rb_root* root,
 void (*augment_rotate)(struct rb_node* old, struct rb_node* new)) {
 consumes c: ctx_at(0, root);
 requires erase_right_red_sibling_inner(c.model, parent) == 1;
 requires ctx_rb(c.model, Nat::Succ(black_height(RbTree::Empty)), Color::Black) == 1;
 requires rb_parent_consistent(plug(c.model, RbTree::Empty), 0) == 1;
 requires AugmentRotate(augment_rotate);
 produces whole: rb_root_at(root);
 ensures whole.model == erase_right_red_sibling_inner_result(old(c.model));
 ensures is_rb_root(whole.model) == 1;
 ensures rb_parent_consistent(whole.model, 0) == 1;
 ensures rb_inorder(whole.model) == rb_inorder(plug(old(c.model), RbTree::Empty));
} by { match c.model { Context::Top => {
have erase_right_red_sibling_inner(c.model, parent) == 0 by { rewrite(c.model == Context::Top); unfold(erase_right_red_sibling_inner(Context::Top, parent)); normalize() using {  } }
have not(erase_right_red_sibling_inner(c.model, parent) == 1) by { rewrite(erase_right_red_sibling_inner(c.model, parent) == 0); normalize(); }
contradiction(erase_right_red_sibling_inner(c.model, parent) == 1);
},
Context::Left(id, above, pc, sm, um) => {
have erase_right_red_sibling_inner(c.model, parent) == 0 by { rewrite(c.model == Context::Left(id, above, pc, sm, um)); unfold(erase_right_red_sibling_inner(Context::Left(id, above, pc, sm, um), parent)); normalize() using {  } }
have not(erase_right_red_sibling_inner(c.model, parent) == 1) by { rewrite(erase_right_red_sibling_inner(c.model, parent) == 0); normalize(); }
contradiction(erase_right_red_sibling_inner(c.model, parent) == 1);
},
Context::Right(id, above, pc, sm, um) => {
have id == parent by { if id == parent { assumption(); } else {
have erase_right_red_sibling_inner(c.model, parent) == 0 by { rewrite(c.model == Context::Right(id, above, pc, sm, um)); unfold(erase_right_red_sibling_inner(Context::Right(id, above, pc, sm, um), parent)); normalize() using { not(id == parent); } }
have not(erase_right_red_sibling_inner(c.model, parent) == 1) by { rewrite(erase_right_red_sibling_inner(c.model, parent) == 0); normalize(); }
contradiction(erase_right_red_sibling_inner(c.model, parent) == 1);
} }
have pc == Color::Black by { if pc == Color::Black { assumption(); } else {
have erase_right_red_sibling_inner(c.model, parent) == 0 by { rewrite(c.model == Context::Right(id, above, pc, sm, um)); unfold(erase_right_red_sibling_inner(Context::Right(id, above, pc, sm, um), parent)); normalize() using { id == parent; not(pc == Color::Black); } }
have not(erase_right_red_sibling_inner(c.model, parent) == 1) by { rewrite(erase_right_red_sibling_inner(c.model, parent) == 0); normalize(); }
contradiction(erase_right_red_sibling_inner(c.model, parent) == 1);
} }
match sm { RbTree::Empty => {
have erase_right_red_sibling_inner(c.model, parent) == 0 by { rewrite(c.model == Context::Right(id, above, pc, sm, um)); rewrite(sm == RbTree::Empty); unfold(erase_right_red_sibling_inner(Context::Right(id, above, pc, RbTree::Empty, um), parent)); normalize() using { id == parent; pc == Color::Black; } }
have not(erase_right_red_sibling_inner(c.model, parent) == 1) by { rewrite(erase_right_red_sibling_inner(c.model, parent) == 0); normalize(); }
contradiction(erase_right_red_sibling_inner(c.model, parent) == 1);
},
RbTree::Node(sid, sp, sc, far_model, near_model) => {
have sc == Color::Red by { if sc == Color::Red { assumption(); } else {
have erase_right_red_sibling_inner(c.model, parent) == 0 by { rewrite(c.model == Context::Right(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, sp, sc, far_model, near_model)); unfold(erase_right_red_sibling_inner(Context::Right(id, above, pc, RbTree::Node(sid, sp, sc, far_model, near_model), um), parent)); normalize() using { id == parent; pc == Color::Black; not(sc == Color::Red); } }
have not(erase_right_red_sibling_inner(c.model, parent) == 1) by { rewrite(erase_right_red_sibling_inner(c.model, parent) == 0); normalize(); }
contradiction(erase_right_red_sibling_inner(c.model, parent) == 1);
} }
match near_model { RbTree::Empty => {
have erase_right_red_sibling_inner(c.model, parent) == 0 by { rewrite(c.model == Context::Right(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, sp, sc, far_model, near_model)); rewrite(near_model == RbTree::Empty); unfold(erase_right_red_sibling_inner(Context::Right(id, above, pc, RbTree::Node(sid, sp, sc, far_model, RbTree::Empty), um), parent)); normalize() using { id == parent; pc == Color::Black; sc == Color::Red; } }
have not(erase_right_red_sibling_inner(c.model, parent) == 1) by { rewrite(erase_right_red_sibling_inner(c.model, parent) == 0); normalize(); }
contradiction(erase_right_red_sibling_inner(c.model, parent) == 1);
},
RbTree::Node(nid, np, nc, nrm, nlm) => {
have nc == Color::Black by { if nc == Color::Black { assumption(); } else {
have erase_right_red_sibling_inner(c.model, parent) == 0 by { rewrite(c.model == Context::Right(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, sp, sc, far_model, near_model)); rewrite(near_model == RbTree::Node(nid, np, nc, nrm, nlm)); unfold(erase_right_red_sibling_inner(Context::Right(id, above, pc, RbTree::Node(sid, sp, sc, far_model, RbTree::Node(nid, np, nc, nrm, nlm)), um), parent)); normalize() using { id == parent; pc == Color::Black; sc == Color::Red; not(nc == Color::Black); } }
have not(erase_right_red_sibling_inner(c.model, parent) == 1) by { rewrite(erase_right_red_sibling_inner(c.model, parent) == 0); normalize(); }
contradiction(erase_right_red_sibling_inner(c.model, parent) == 1);
} }
have nrm == RbTree::Empty by { if nrm == RbTree::Empty { assumption(); } else {
have erase_right_red_sibling_inner(c.model, parent) == 0 by { rewrite(c.model == Context::Right(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, sp, sc, far_model, near_model)); rewrite(near_model == RbTree::Node(nid, np, nc, nrm, nlm)); unfold(erase_right_red_sibling_inner(Context::Right(id, above, pc, RbTree::Node(sid, sp, sc, far_model, RbTree::Node(nid, np, nc, nrm, nlm)), um), parent)); normalize() using { id == parent; pc == Color::Black; sc == Color::Red; nc == Color::Black; not(nrm == RbTree::Empty); } }
have not(erase_right_red_sibling_inner(c.model, parent) == 1) by { rewrite(erase_right_red_sibling_inner(c.model, parent) == 0); normalize(); }
contradiction(erase_right_red_sibling_inner(c.model, parent) == 1);
} }
match nlm { RbTree::Empty => {
have erase_right_red_sibling_inner(c.model, parent) == 0 by { rewrite(c.model == Context::Right(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, sp, sc, far_model, near_model)); rewrite(near_model == RbTree::Node(nid, np, nc, nrm, nlm)); rewrite(nlm == RbTree::Empty); unfold(erase_right_red_sibling_inner(Context::Right(id, above, pc, RbTree::Node(sid, sp, sc, far_model, RbTree::Node(nid, np, nc, nrm, RbTree::Empty)), um), parent)); normalize() using { id == parent; pc == Color::Black; sc == Color::Red; nc == Color::Black; nrm == RbTree::Empty; } }
have not(erase_right_red_sibling_inner(c.model, parent) == 1) by { rewrite(erase_right_red_sibling_inner(c.model, parent) == 0); normalize(); }
contradiction(erase_right_red_sibling_inner(c.model, parent) == 1);
},
RbTree::Node(rid, rp, rc, rrm, rlm) => {
have rc == Color::Red by { if rc == Color::Red { assumption(); } else {
have erase_right_red_sibling_inner(c.model, parent) == 0 by { rewrite(c.model == Context::Right(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, sp, sc, far_model, near_model)); rewrite(near_model == RbTree::Node(nid, np, nc, nrm, nlm)); rewrite(nlm == RbTree::Node(rid, rp, rc, rrm, rlm)); unfold(erase_right_red_sibling_inner(Context::Right(id, above, pc, RbTree::Node(sid, sp, sc, far_model, RbTree::Node(nid, np, nc, nrm, RbTree::Node(rid, rp, rc, rrm, rlm))), um), parent)); normalize() using { id == parent; pc == Color::Black; sc == Color::Red; nc == Color::Black; nrm == RbTree::Empty; not(rc == Color::Red); } }
have not(erase_right_red_sibling_inner(c.model, parent) == 1) by { rewrite(erase_right_red_sibling_inner(c.model, parent) == 0); normalize(); }
contradiction(erase_right_red_sibling_inner(c.model, parent) == 1);
} }
have rlm == RbTree::Empty by { if rlm == RbTree::Empty { assumption(); } else {
have erase_right_red_sibling_inner(c.model, parent) == 0 by { rewrite(c.model == Context::Right(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, sp, sc, far_model, near_model)); rewrite(near_model == RbTree::Node(nid, np, nc, nrm, nlm)); rewrite(nlm == RbTree::Node(rid, rp, rc, rrm, rlm)); unfold(erase_right_red_sibling_inner(Context::Right(id, above, pc, RbTree::Node(sid, sp, sc, far_model, RbTree::Node(nid, np, nc, nrm, RbTree::Node(rid, rp, rc, rrm, rlm))), um), parent)); normalize() using { id == parent; pc == Color::Black; sc == Color::Red; nc == Color::Black; nrm == RbTree::Empty; rc == Color::Red; not(rlm == RbTree::Empty); } }
have not(erase_right_red_sibling_inner(c.model, parent) == 1) by { rewrite(erase_right_red_sibling_inner(c.model, parent) == 0); normalize(); }
contradiction(erase_right_red_sibling_inner(c.model, parent) == 1);
} }
have rrm == RbTree::Empty by { if rrm == RbTree::Empty { assumption(); } else {
have erase_right_red_sibling_inner(c.model, parent) == 0 by { rewrite(c.model == Context::Right(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, sp, sc, far_model, near_model)); rewrite(near_model == RbTree::Node(nid, np, nc, nrm, nlm)); rewrite(nlm == RbTree::Node(rid, rp, rc, rrm, rlm)); unfold(erase_right_red_sibling_inner(Context::Right(id, above, pc, RbTree::Node(sid, sp, sc, far_model, RbTree::Node(nid, np, nc, nrm, RbTree::Node(rid, rp, rc, rrm, rlm))), um), parent)); normalize() using { id == parent; pc == Color::Black; sc == Color::Red; nc == Color::Black; nrm == RbTree::Empty; rc == Color::Red; rlm == RbTree::Empty; not(rrm == RbTree::Empty); } }
have not(erase_right_red_sibling_inner(c.model, parent) == 1) by { rewrite(erase_right_red_sibling_inner(c.model, parent) == 0); normalize(); }
contradiction(erase_right_red_sibling_inner(c.model, parent) == 1);
} }
apply(plug_parent_consistent_ctx(c.model, RbTree::Empty, 0));
have ctx_consistent(Context::Right(id, above, pc, sm, um), RbTree::Empty, 0) == 1 by { rewrite(Context::Right(id, above, pc, sm, um) == c.model); assumption(); }
apply(ctx_consistent_right_sibling(id, above, pc, sm, um, RbTree::Empty, 0));
have rb_parent_consistent(RbTree::Node(sid, sp, sc, far_model, near_model), id) == 1 by { rewrite(RbTree::Node(sid, sp, sc, far_model, near_model) == sm); assumption(); }
apply(rb_parent_consistent_node_fixes_parent(sid, sp, sc, far_model, near_model, id));
have sp == parent by { simp(); }
apply(rb_parent_consistent_node_right(sid, sp, sc, far_model, near_model, id));
have rb_parent_consistent(RbTree::Node(nid, np, nc, nrm, nlm), sid) == 1 by { rewrite(RbTree::Node(nid, np, nc, nrm, nlm) == near_model); assumption(); }
apply(rb_parent_consistent_node_fixes_parent(nid, np, nc, nrm, nlm, sid));
have np == sid by { assumption(); }
apply(rb_parent_consistent_node_right(nid, np, nc, nrm, nlm, sid));
have rb_parent_consistent(RbTree::Node(rid, rp, rc, rrm, rlm), nid) == 1 by { rewrite(RbTree::Node(rid, rp, rc, rrm, rlm) == nlm); assumption(); }
apply(rb_parent_consistent_node_fixes_parent(rid, rp, rc, rrm, rlm, nid));
have rp == nid by { assumption(); }
have c.model == Context::Right(parent, above, Color::Black, RbTree::Node(sid, parent, Color::Red, far_model, RbTree::Node(nid, sid, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty))), um) by { rewrite(c.model == Context::Right(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, sp, sc, far_model, near_model)); rewrite(near_model == RbTree::Node(nid, np, nc, nrm, nlm)); rewrite(nlm == RbTree::Node(rid, rp, rc, rrm, rlm)); rewrite(id == parent); rewrite(pc == Color::Black); rewrite(sc == Color::Red); rewrite(nc == Color::Black); rewrite(nrm == RbTree::Empty); rewrite(rc == Color::Red); rewrite(rlm == RbTree::Empty); rewrite(rrm == RbTree::Empty); rewrite(sp == parent); rewrite(np == sid); rewrite(rp == nid); normalize(); }
let { sibling: s, up: u } = unfold(c);
let { right: sl, left: sr } = unfold(s);
let { right: nl, left: nr } = unfold(sl);
let { right: rl, left: rr } = unfold(nl);
unfold(nr); unfold(rl); unfold(rr);
have old(c.model) == Context::Right(parent, above, Color::Black, RbTree::Node(sid, parent, Color::Red, far_model, RbTree::Node(nid, sid, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty))), um) by { rewrite(old(c.model) == Context::Right(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, sp, sc, far_model, near_model)); rewrite(near_model == RbTree::Node(nid, np, nc, nrm, nlm)); rewrite(nlm == RbTree::Node(rid, rp, rc, rrm, rlm)); rewrite(id == parent); rewrite(pc == Color::Black); rewrite(sc == Color::Red); rewrite(nc == Color::Black); rewrite(nrm == RbTree::Empty); rewrite(rc == Color::Red); rewrite(rlm == RbTree::Empty); rewrite(rrm == RbTree::Empty); rewrite(sp == parent); rewrite(np == sid); rewrite(rp == nid); normalize(); }
have is_rb(RbTree::Empty) == 1 by { unfold(is_rb(RbTree::Empty)); normalize(); }
have rb_root_black(RbTree::Empty) == 1 by { unfold(rb_root_black(RbTree::Empty)); normalize(); }
have ctx_rb(Context::Right(parent, above, Color::Black, RbTree::Node(sid, parent, Color::Red, far_model, RbTree::Node(nid, sid, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty))), um), Nat::Succ(black_height(RbTree::Empty)), Color::Black) == 1 by { rewrite(Context::Right(parent, above, Color::Black, RbTree::Node(sid, parent, Color::Red, far_model, RbTree::Node(nid, sid, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty))), um) == old(c.model)); simp(); }
have rb_parent_consistent(plug(Context::Right(parent, above, Color::Black, RbTree::Node(sid, parent, Color::Red, far_model, RbTree::Node(nid, sid, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty))), um), RbTree::Empty), 0) == 1 by { rewrite(Context::Right(parent, above, Color::Black, RbTree::Node(sid, parent, Color::Red, far_model, RbTree::Node(nid, sid, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty))), um) == old(c.model)); simp(); }
apply(ctx_erase_case1_right_step(above, parent, sid, RbTree::Empty, far_model, RbTree::Node(nid, sid, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty)), um));
have rb_reparent(RbTree::Node(nid, sid, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty)), parent) == RbTree::Node(nid, parent, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty)) by { unfold(rb_reparent(RbTree::Node(nid, sid, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty)), parent)); normalize(); }
have ctx_rb(Context::Right(parent, sid, Color::Red, RbTree::Node(nid, parent, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty)), Context::Right(sid, above, Color::Black, far_model, um)), Nat::Succ(black_height(RbTree::Empty)), Color::Black) == 1 by { rewrite(RbTree::Node(nid, parent, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty)) == rb_reparent(RbTree::Node(nid, sid, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty)), parent)); assumption(); }
have rb_parent_consistent(plug(Context::Right(parent, sid, Color::Red, RbTree::Node(nid, parent, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty)), Context::Right(sid, above, Color::Black, far_model, um)), RbTree::Empty), 0) == 1 by { rewrite(RbTree::Node(nid, parent, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty)) == rb_reparent(RbTree::Node(nid, sid, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty)), parent)); assumption(); }
apply(ctx_erase_case3_right_exit(sid, parent, Color::Red, nid, rid, RbTree::Empty, RbTree::Empty, RbTree::Empty, RbTree::Empty, Context::Right(sid, above, Color::Black, far_model, um)));
have rb_reparent(RbTree::Empty, parent) == RbTree::Empty by { unfold(rb_reparent(RbTree::Empty, parent)); normalize(); }
have rb_reparent(RbTree::Empty, nid) == RbTree::Empty by { unfold(rb_reparent(RbTree::Empty, nid)); normalize(); }
have RbTree::Node(rid, sid, Color::Red, RbTree::Node(nid, rid, Color::Black, RbTree::Empty, rb_reparent(RbTree::Empty, nid)), RbTree::Node(parent, rid, Color::Black, rb_reparent(RbTree::Empty, parent), RbTree::Empty)) == RbTree::Node(rid, sid, Color::Red, RbTree::Node(nid, rid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(parent, rid, Color::Black, RbTree::Empty, RbTree::Empty)) by { rewrite(rb_reparent(RbTree::Empty, parent) == RbTree::Empty); rewrite(rb_reparent(RbTree::Empty, nid) == RbTree::Empty); normalize(); }
have plug(Context::Right(sid, above, Color::Black, far_model, um), RbTree::Node(rid, sid, Color::Red, RbTree::Node(nid, rid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(parent, rid, Color::Black, RbTree::Empty, RbTree::Empty))) == plug(um, RbTree::Node(sid, above, Color::Black, far_model, RbTree::Node(rid, sid, Color::Red, RbTree::Node(nid, rid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(parent, rid, Color::Black, RbTree::Empty, RbTree::Empty)))) by { unfold(plug(Context::Right(sid, above, Color::Black, far_model, um), RbTree::Node(rid, sid, Color::Red, RbTree::Node(nid, rid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(parent, rid, Color::Black, RbTree::Empty, RbTree::Empty)))); normalize(); }
have is_rb_root(plug(um, RbTree::Node(sid, above, Color::Black, far_model, RbTree::Node(rid, sid, Color::Red, RbTree::Node(nid, rid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(parent, rid, Color::Black, RbTree::Empty, RbTree::Empty))))) == 1 by { rewrite(plug(um, RbTree::Node(sid, above, Color::Black, far_model, RbTree::Node(rid, sid, Color::Red, RbTree::Node(nid, rid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(parent, rid, Color::Black, RbTree::Empty, RbTree::Empty)))) == plug(Context::Right(sid, above, Color::Black, far_model, um), RbTree::Node(rid, sid, Color::Red, RbTree::Node(nid, rid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(parent, rid, Color::Black, RbTree::Empty, RbTree::Empty)))); rewrite(RbTree::Node(rid, sid, Color::Red, RbTree::Node(nid, rid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(parent, rid, Color::Black, RbTree::Empty, RbTree::Empty)) == RbTree::Node(rid, sid, Color::Red, RbTree::Node(nid, rid, Color::Black, RbTree::Empty, rb_reparent(RbTree::Empty, nid)), RbTree::Node(parent, rid, Color::Black, rb_reparent(RbTree::Empty, parent), RbTree::Empty))); assumption(); }
have rb_parent_consistent(plug(um, RbTree::Node(sid, above, Color::Black, far_model, RbTree::Node(rid, sid, Color::Red, RbTree::Node(nid, rid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(parent, rid, Color::Black, RbTree::Empty, RbTree::Empty)))), 0) == 1 by { rewrite(plug(um, RbTree::Node(sid, above, Color::Black, far_model, RbTree::Node(rid, sid, Color::Red, RbTree::Node(nid, rid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(parent, rid, Color::Black, RbTree::Empty, RbTree::Empty)))) == plug(Context::Right(sid, above, Color::Black, far_model, um), RbTree::Node(rid, sid, Color::Red, RbTree::Node(nid, rid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(parent, rid, Color::Black, RbTree::Empty, RbTree::Empty)))); rewrite(RbTree::Node(rid, sid, Color::Red, RbTree::Node(nid, rid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(parent, rid, Color::Black, RbTree::Empty, RbTree::Empty)) == RbTree::Node(rid, sid, Color::Red, RbTree::Node(nid, rid, Color::Black, RbTree::Empty, rb_reparent(RbTree::Empty, nid)), RbTree::Node(parent, rid, Color::Black, rb_reparent(RbTree::Empty, parent), RbTree::Empty))); assumption(); }
have rb_inorder(plug(um, RbTree::Node(sid, above, Color::Black, far_model, RbTree::Node(rid, sid, Color::Red, RbTree::Node(nid, rid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(parent, rid, Color::Black, RbTree::Empty, RbTree::Empty))))) == rb_inorder(plug(Context::Right(parent, above, Color::Black, RbTree::Node(sid, parent, Color::Red, far_model, RbTree::Node(nid, sid, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty))), um), RbTree::Empty)) by {
 rewrite(plug(um, RbTree::Node(sid, above, Color::Black, far_model, RbTree::Node(rid, sid, Color::Red, RbTree::Node(nid, rid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(parent, rid, Color::Black, RbTree::Empty, RbTree::Empty)))) == plug(Context::Right(sid, above, Color::Black, far_model, um), RbTree::Node(rid, sid, Color::Red, RbTree::Node(nid, rid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(parent, rid, Color::Black, RbTree::Empty, RbTree::Empty))));
 have rb_inorder(plug(Context::Right(sid, above, Color::Black, far_model, um), RbTree::Node(rid, sid, Color::Red, RbTree::Node(nid, rid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(parent, rid, Color::Black, RbTree::Empty, RbTree::Empty)))) == rb_inorder(plug(Context::Right(parent, sid, Color::Red, RbTree::Node(nid, parent, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty)), Context::Right(sid, above, Color::Black, far_model, um)), RbTree::Empty)) by { rewrite(RbTree::Node(rid, sid, Color::Red, RbTree::Node(nid, rid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(parent, rid, Color::Black, RbTree::Empty, RbTree::Empty)) == RbTree::Node(rid, sid, Color::Red, RbTree::Node(nid, rid, Color::Black, RbTree::Empty, rb_reparent(RbTree::Empty, nid)), RbTree::Node(parent, rid, Color::Black, rb_reparent(RbTree::Empty, parent), RbTree::Empty))); assumption(); }
 rewrite(rb_inorder(plug(Context::Right(sid, above, Color::Black, far_model, um), RbTree::Node(rid, sid, Color::Red, RbTree::Node(nid, rid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(parent, rid, Color::Black, RbTree::Empty, RbTree::Empty)))) == rb_inorder(plug(Context::Right(parent, sid, Color::Red, RbTree::Node(nid, parent, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty)), Context::Right(sid, above, Color::Black, far_model, um)), RbTree::Empty)));
 rewrite(RbTree::Node(nid, parent, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty)) == rb_reparent(RbTree::Node(nid, sid, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty)), parent)); assumption();
}
have parent->rb_right == 0 by { simp(); }
have parent->rb_left == sid by { simp(); }
have sid == parent->rb_left by { simp(); }
have aligned(sid, 8) by { rewrite(sid == parent->rb_left); assumption(); }
have aligned(parent, 8) by { simp(); }
have sid->rb_right == nid by { simp(); }
have nid == sid->rb_right by { simp(); }
have aligned(nid, 8) by { rewrite(nid == sid->rb_right); simp(); }
have nid->rb_left == 0 by { simp(); }
have nid->rb_right == rid by { simp(); }
have rid == nid->rb_right by { simp(); }
have rid != 0 by { rewrite(rid == nid->rb_right); assumption(); }
have aligned(rid, 8) by { rewrite(rid == nid->rb_right); simp(); }
have rid->rb_right == 0 by { simp(); }
have rid->rb_left == 0 by { simp(); }
have (rid->__rb_parent_color & 1) == 0 by { rewrite((rid->__rb_parent_color & 1) == color_bit(Color::Red)); unfold(color_bit(Color::Red)); normalize(); }
have (sid->__rb_parent_color & 1) == 0 by { rewrite((sid->__rb_parent_color & 1) == color_bit(Color::Red)); unfold(color_bit(Color::Red)); normalize(); }
have parent->__rb_parent_color == address(above) + 1 by { rewrite(parent->__rb_parent_color == address(above) + (parent->__rb_parent_color & 1)); rewrite((parent->__rb_parent_color & 1) == color_bit(Color::Black)); unfold(color_bit(Color::Black)); normalize(); }
have color_bit(Color::Black) == 1 by { unfold(color_bit(Color::Black)); normalize(); }
have parent->__rb_parent_color == address(above) + color_bit(Color::Black) by { rewrite(color_bit(Color::Black) == 1); assumption(); }
apply(ctx_parent_word_from_color(u.model, above, parent->__rb_parent_color, Color::Black));
have rb_parent_is(far_model, sid) == 1 by { rewrite(sid == parent->rb_left); assumption(); }
have nid == parent->rb_left->rb_right by { normalize() using { sid == parent->rb_left; nid == sid->rb_right; } }
have rid == parent->rb_left->rb_right->rb_right by { normalize() using { sid == parent->rb_left; nid == sid->rb_right; rid == nid->rb_right; } }
have separate(memory(parent->__rb_parent_color), memory(parent->rb_left->rb_right->rb_right)) by { assumption(); }
have separate(memory(parent->__rb_parent_color), memory(nid->rb_right)) by { transport(separate(memory(parent->__rb_parent_color), memory(parent->rb_left->rb_right->rb_right)), separate(memory(parent->__rb_parent_color), memory(nid->rb_right))) using { separate(memory(parent->__rb_parent_color), memory(parent->rb_left->rb_right->rb_right)); nid == parent->rb_left->rb_right; }; }
have separate(memory(parent->__rb_parent_color), memory(parent->rb_left->rb_right->__rb_parent_color)) by { assumption(); }
have separate(memory(parent->__rb_parent_color), memory(nid->__rb_parent_color)) by { transport(separate(memory(parent->__rb_parent_color), memory(parent->rb_left->rb_right->__rb_parent_color)), separate(memory(parent->__rb_parent_color), memory(nid->__rb_parent_color))) using { separate(memory(parent->__rb_parent_color), memory(parent->rb_left->rb_right->__rb_parent_color)); nid == parent->rb_left->rb_right; }; }
have separate(memory(parent->__rb_parent_color), memory(parent->rb_left->rb_right->rb_right->rb_right)) by { assumption(); }
have separate(memory(parent->__rb_parent_color), memory(rid->rb_right)) by { transport(separate(memory(parent->__rb_parent_color), memory(parent->rb_left->rb_right->rb_right->rb_right)), separate(memory(parent->__rb_parent_color), memory(rid->rb_right))) using { separate(memory(parent->__rb_parent_color), memory(parent->rb_left->rb_right->rb_right->rb_right)); rid == parent->rb_left->rb_right->rb_right; }; }
have separate(memory(parent->__rb_parent_color), memory(parent->rb_left->rb_right->rb_right->rb_left)) by { assumption(); }
have separate(memory(parent->__rb_parent_color), memory(rid->rb_left)) by { transport(separate(memory(parent->__rb_parent_color), memory(parent->rb_left->rb_right->rb_right->rb_left)), separate(memory(parent->__rb_parent_color), memory(rid->rb_left))) using { separate(memory(parent->__rb_parent_color), memory(parent->rb_left->rb_right->rb_right->rb_left)); rid == parent->rb_left->rb_right->rb_right; }; }
have separate(memory(parent->rb_left->rb_right->rb_right->rb_right), memory(parent->rb_left)) by { assumption(); }
have separate(memory(rid->rb_right), memory(parent->rb_left)) by { transport(separate(memory(parent->rb_left->rb_right->rb_right->rb_right), memory(parent->rb_left)), separate(memory(rid->rb_right), memory(parent->rb_left))) using { separate(memory(parent->rb_left->rb_right->rb_right->rb_right), memory(parent->rb_left)); rid == parent->rb_left->rb_right->rb_right; nid == parent->rb_left->rb_right; }; }
have separate(memory(parent->rb_left->rb_right->rb_right->rb_right), memory(parent->rb_left->rb_right->rb_right)) by { assumption(); }
have separate(memory(rid->rb_right), memory(nid->rb_right)) by { transport(separate(memory(parent->rb_left->rb_right->rb_right->rb_right), memory(parent->rb_left->rb_right->rb_right)), separate(memory(rid->rb_right), memory(nid->rb_right))) using { separate(memory(parent->rb_left->rb_right->rb_right->rb_right), memory(parent->rb_left->rb_right->rb_right)); rid == parent->rb_left->rb_right->rb_right; nid == parent->rb_left->rb_right; }; }
have separate(memory(parent->rb_right), memory(parent->rb_left->rb_right->rb_right)) by { assumption(); }
have separate(memory(parent->rb_right), memory(nid->rb_right)) by { transport(separate(memory(parent->rb_right), memory(parent->rb_left->rb_right->rb_right)), separate(memory(parent->rb_right), memory(nid->rb_right))) using { separate(memory(parent->rb_right), memory(parent->rb_left->rb_right->rb_right)); nid == parent->rb_left->rb_right; }; }
have separate(memory(parent->rb_right), memory(parent->rb_left->rb_right->__rb_parent_color)) by { assumption(); }
have separate(memory(parent->rb_right), memory(nid->__rb_parent_color)) by { transport(separate(memory(parent->rb_right), memory(parent->rb_left->rb_right->__rb_parent_color)), separate(memory(parent->rb_right), memory(nid->__rb_parent_color))) using { separate(memory(parent->rb_right), memory(parent->rb_left->rb_right->__rb_parent_color)); nid == parent->rb_left->rb_right; }; }
have separate(memory(parent->rb_right), memory(parent->rb_left->rb_right->rb_right->rb_right)) by { assumption(); }
have separate(memory(parent->rb_right), memory(rid->rb_right)) by { transport(separate(memory(parent->rb_right), memory(parent->rb_left->rb_right->rb_right->rb_right)), separate(memory(parent->rb_right), memory(rid->rb_right))) using { separate(memory(parent->rb_right), memory(parent->rb_left->rb_right->rb_right->rb_right)); rid == parent->rb_left->rb_right->rb_right; }; }
have separate(memory(parent->rb_right), memory(parent->rb_left->rb_right->rb_right->rb_left)) by { assumption(); }
have separate(memory(parent->rb_right), memory(rid->rb_left)) by { transport(separate(memory(parent->rb_right), memory(parent->rb_left->rb_right->rb_right->rb_left)), separate(memory(parent->rb_right), memory(rid->rb_left))) using { separate(memory(parent->rb_right), memory(parent->rb_left->rb_right->rb_right->rb_left)); rid == parent->rb_left->rb_right->rb_right; }; }
have separate(memory(parent->rb_left->rb_right->rb_right->rb_right), memory(parent->rb_left->rb_right->__rb_parent_color)) by { assumption(); }
have separate(memory(rid->rb_right), memory(nid->__rb_parent_color)) by { transport(separate(memory(parent->rb_left->rb_right->rb_right->rb_right), memory(parent->rb_left->rb_right->__rb_parent_color)), separate(memory(rid->rb_right), memory(nid->__rb_parent_color))) using { separate(memory(parent->rb_left->rb_right->rb_right->rb_right), memory(parent->rb_left->rb_right->__rb_parent_color)); rid == parent->rb_left->rb_right->rb_right; nid == parent->rb_left->rb_right; }; }
have separate(memory(parent->rb_left->rb_right->rb_right->rb_left), memory(parent->rb_left)) by { assumption(); }
have separate(memory(rid->rb_left), memory(parent->rb_left)) by { transport(separate(memory(parent->rb_left->rb_right->rb_right->rb_left), memory(parent->rb_left)), separate(memory(rid->rb_left), memory(parent->rb_left))) using { separate(memory(parent->rb_left->rb_right->rb_right->rb_left), memory(parent->rb_left)); rid == parent->rb_left->rb_right->rb_right; nid == parent->rb_left->rb_right; }; }
have separate(memory(parent->rb_left->rb_right->rb_right->rb_left), memory(parent->rb_left->rb_right->__rb_parent_color)) by { assumption(); }
have separate(memory(rid->rb_left), memory(nid->__rb_parent_color)) by { transport(separate(memory(parent->rb_left->rb_right->rb_right->rb_left), memory(parent->rb_left->rb_right->__rb_parent_color)), separate(memory(rid->rb_left), memory(nid->__rb_parent_color))) using { separate(memory(parent->rb_left->rb_right->rb_right->rb_left), memory(parent->rb_left->rb_right->__rb_parent_color)); rid == parent->rb_left->rb_right->rb_right; nid == parent->rb_left->rb_right; }; }
have separate(memory(parent->rb_left->rb_right->rb_right), memory(parent->rb_left)) by { assumption(); }
have separate(memory(nid->rb_right), memory(parent->rb_left)) by { transport(separate(memory(parent->rb_left->rb_right->rb_right), memory(parent->rb_left)), separate(memory(nid->rb_right), memory(parent->rb_left))) using { separate(memory(parent->rb_left->rb_right->rb_right), memory(parent->rb_left)); nid == parent->rb_left->rb_right; rid == parent->rb_left->rb_right->rb_right; }; }
have separate(memory(parent->rb_left->rb_right->rb_right), memory(parent->rb_left->rb_right->rb_right->rb_right)) by { assumption(); }
have separate(memory(nid->rb_right), memory(rid->rb_right)) by { transport(separate(memory(parent->rb_left->rb_right->rb_right), memory(parent->rb_left->rb_right->rb_right->rb_right)), separate(memory(nid->rb_right), memory(rid->rb_right))) using { separate(memory(parent->rb_left->rb_right->rb_right), memory(parent->rb_left->rb_right->rb_right->rb_right)); nid == parent->rb_left->rb_right; rid == parent->rb_left->rb_right->rb_right; }; }
have separate(memory(parent->rb_left->rb_right->rb_right), memory(parent->rb_left->rb_right->rb_right->rb_left)) by { assumption(); }
have separate(memory(nid->rb_right), memory(rid->rb_left)) by { transport(separate(memory(parent->rb_left->rb_right->rb_right), memory(parent->rb_left->rb_right->rb_right->rb_left)), separate(memory(nid->rb_right), memory(rid->rb_left))) using { separate(memory(parent->rb_left->rb_right->rb_right), memory(parent->rb_left->rb_right->rb_right->rb_left)); nid == parent->rb_left->rb_right; rid == parent->rb_left->rb_right->rb_right; }; }
have separate(memory(parent->rb_left->rb_right->rb_left), memory(parent->rb_left)) by { assumption(); }
have separate(memory(nid->rb_left), memory(parent->rb_left)) by { transport(separate(memory(parent->rb_left->rb_right->rb_left), memory(parent->rb_left)), separate(memory(nid->rb_left), memory(parent->rb_left))) using { separate(memory(parent->rb_left->rb_right->rb_left), memory(parent->rb_left)); nid == parent->rb_left->rb_right; rid == parent->rb_left->rb_right->rb_right; }; }
have separate(memory(parent->rb_left->rb_right->rb_left), memory(parent->rb_left->rb_right->rb_right->rb_right)) by { assumption(); }
have separate(memory(nid->rb_left), memory(rid->rb_right)) by { transport(separate(memory(parent->rb_left->rb_right->rb_left), memory(parent->rb_left->rb_right->rb_right->rb_right)), separate(memory(nid->rb_left), memory(rid->rb_right))) using { separate(memory(parent->rb_left->rb_right->rb_left), memory(parent->rb_left->rb_right->rb_right->rb_right)); nid == parent->rb_left->rb_right; rid == parent->rb_left->rb_right->rb_right; }; }
have separate(memory(parent->rb_left->rb_right->rb_left), memory(parent->rb_left->rb_right->rb_right->rb_left)) by { assumption(); }
have separate(memory(nid->rb_left), memory(rid->rb_left)) by { transport(separate(memory(parent->rb_left->rb_right->rb_left), memory(parent->rb_left->rb_right->rb_right->rb_left)), separate(memory(nid->rb_left), memory(rid->rb_left))) using { separate(memory(parent->rb_left->rb_right->rb_left), memory(parent->rb_left->rb_right->rb_right->rb_left)); nid == parent->rb_left->rb_right; rid == parent->rb_left->rb_right->rb_right; }; }
mark inputs;
execute_until(loop(0));
step(); // Enter the mirrored arm and load the left sibling.
step();
step();
step();
step();
step();
step();
step();
step();
have sibling == sid by { simp(); }
have tmp1 == nid by { simp(); }
have parent->rb_left == nid by { simp(); }
have nid->__rb_parent_color == (address(parent) | 1) by { simp(); }
mark first_rotation;
let { after: u } = step(__rb_rotate_set_parents(parent, sibling, root, 0), { c: u });
have sibling == sid by { simp(); }
have tmp1 == nid by { simp(); }
have sid->rb_right == parent by { normalize() using { sibling == sid; tmp1 == nid; } }
have sid->rb_left == at(inputs, parent->rb_left->rb_left) by { normalize() using { at(inputs, parent->rb_left) == sid; sibling == sid; tmp1 == nid; } }
have sid->__rb_parent_color == address(above) + 1 by { simp(); }
have (sid->__rb_parent_color & 1) == 1 by { rewrite(sid->__rb_parent_color == address(above) + 1); arithmetic() using { aligned(above, 8); } }
have sid->__rb_parent_color == address(above) + color_bit(Color::Black) by { rewrite(color_bit(Color::Black) == 1); assumption(); }
have u.model == um by { simp(); }
have ctx_node_is(u.model, above) == 1 by { rewrite(u.model == um); simp(); }
apply(ctx_parent_word_from_color(u.model, above, sid->__rb_parent_color, Color::Black));
have sr.model == far_model by { assumption(); }
let rotation_ctx = fold(ctx_at(parent, root), { model: Context::Right(sid, above, Color::Black, far_model, um) }, { sibling: sr, up: u });
have parent->__rb_parent_color == address(sid) by { simp(); }
have parent->__rb_parent_color == address(sid) + color_bit(Color::Red) by { unfold(color_bit(Color::Red)); normalize() using { parent->__rb_parent_color == address(sid); } }
have ctx_node_is(rotation_ctx.model, sid) == 1 by { rewrite(rotation_ctx.model == Context::Right(sid, above, Color::Black, far_model, um)); unfold(ctx_node_is(Context::Right(sid, above, Color::Black, far_model, um), sid)); normalize(); }
apply(ctx_parent_word_from_color(rotation_ctx.model, sid, parent->__rb_parent_color, Color::Red));
have nid->rb_left == 0 by { simp(); }
have nid->rb_right == rid by { simp(); }
have rid->__rb_parent_color == at(first_rotation, rid->__rb_parent_color) by { normalize() using { sibling == sid; tmp1 == nid; } }
have (rid->__rb_parent_color & 1) == 0 by { rewrite(rid->__rb_parent_color == at(first_rotation, rid->__rb_parent_color)); simp(); }
mark far_read;
step();
step();
have sibling == nid by { simp(); }
have sibling->rb_left == 0 by { simp(); }
step();
have tmp1 == 0 by { simp(); }
step();
step();
have tmp2 == rid by { simp(); }
have tmp2 != 0 by { rewrite(tmp2 == rid); assumption(); }
have rid->__rb_parent_color == at(far_read, rid->__rb_parent_color) by { normalize() using { tmp2 == rid; sibling == nid; at(first_rotation, sibling) == sid; at(first_rotation, tmp1) == nid; } }
have (rid->__rb_parent_color & 1) == 0 by { rewrite(rid->__rb_parent_color == at(far_read, rid->__rb_parent_color)); assumption(); }
have tmp2->__rb_parent_color == rid->__rb_parent_color by { normalize() using { tmp2 == rid; } }
have (tmp2->__rb_parent_color & 1) == 0 by { rewrite(tmp2->__rb_parent_color == rid->__rb_parent_color); assumption(); }
have rid->rb_left == 0 by { simp(); }
have tmp2->rb_left == 0 by { transport(rid->rb_left == 0, tmp2->rb_left == 0) using { tmp2 == rid; rid->rb_left == 0; }; }
have rid->rb_right == 0 by { simp(); }
have parent->rb_right == 0 by { simp(); }
have parent->__rb_parent_color == address(sid) by { normalize() using { at(far_read, parent->__rb_parent_color) == address(sid); } }
have nid->rb_left == 0 by { normalize() using { at(far_read, nid->rb_left) == 0; } }
have separate(memory(nid->rb_left), memory(sibling->rb_right)) by { transport(separate(memory(nid->rb_left), memory(nid->rb_right)), separate(memory(nid->rb_left), memory(sibling->rb_right))) using { separate(memory(nid->rb_left), memory(nid->rb_right)); sibling == nid; }; }
mark inner_rotation;
step();
step();
step();
have tmp1 == 0 by { simp(); }
step();
have parent->rb_right == 0 by { transport(at(inner_rotation, parent->rb_right) == 0, parent->rb_right == 0) using { at(inner_rotation, parent->rb_right) == 0; separate(memory(parent->rb_right), memory(nid->rb_right)); sibling == nid; tmp2 == rid; }; }
have rid->rb_right == 0 by { transport(at(inner_rotation, rid->rb_right) == 0, rid->rb_right == 0) using { at(inner_rotation, rid->rb_right) == 0; separate(memory(rid->rb_right), memory(nid->rb_right)); sibling == nid; tmp2 == rid; }; }
have separate(memory(rid->rb_right), memory(tmp2->rb_left)) by { transport(separate(memory(rid->rb_right), memory(rid->rb_left)), separate(memory(rid->rb_right), memory(tmp2->rb_left))) using { separate(memory(rid->rb_right), memory(rid->rb_left)); tmp2 == rid; }; }
have separate(memory(parent->rb_right), memory(tmp2->rb_left)) by { transport(separate(memory(parent->rb_right), memory(rid->rb_left)), separate(memory(parent->rb_right), memory(tmp2->rb_left))) using { separate(memory(parent->rb_right), memory(rid->rb_left)); tmp2 == rid; }; }
have parent->__rb_parent_color == address(sid) by { transport(at(inner_rotation, parent->__rb_parent_color) == address(sid), parent->__rb_parent_color == address(sid)) using { at(inner_rotation, parent->__rb_parent_color) == address(sid); separate(memory(parent->__rb_parent_color), memory(nid->rb_right)); sibling == nid; tmp2 == rid; }; }
have separate(memory(parent->__rb_parent_color), memory(tmp2->rb_left)) by { transport(separate(memory(parent->__rb_parent_color), memory(rid->rb_left)), separate(memory(parent->__rb_parent_color), memory(tmp2->rb_left))) using { separate(memory(parent->__rb_parent_color), memory(rid->rb_left)); tmp2 == rid; }; }
have sibling->rb_right == 0 by { simp(); }
have nid->rb_right == 0 by { transport(sibling->rb_right == 0, nid->rb_right == 0) using { sibling->rb_right == 0; sibling == nid; }; }
have nid->rb_left == 0 by { transport(at(inner_rotation, nid->rb_left) == 0, nid->rb_left == 0) using { at(inner_rotation, nid->rb_left) == 0; separate(memory(nid->rb_left), memory(sibling->rb_right)); sibling == nid; }; }
have separate(memory(nid->rb_right), memory(tmp2->rb_left)) by { transport(separate(memory(nid->rb_right), memory(rid->rb_left)), separate(memory(nid->rb_right), memory(tmp2->rb_left))) using { separate(memory(nid->rb_right), memory(rid->rb_left)); tmp2 == rid; }; }
have separate(memory(nid->rb_left), memory(tmp2->rb_left)) by { transport(separate(memory(nid->rb_left), memory(rid->rb_left)), separate(memory(nid->rb_left), memory(tmp2->rb_left))) using { separate(memory(nid->rb_left), memory(rid->rb_left)); tmp2 == rid; }; }
mark after_detach;

step();
have rid->rb_right == 0 by { transport(at(after_detach, rid->rb_right) == 0, rid->rb_right == 0) using { at(after_detach, rid->rb_right) == 0; separate(memory(rid->rb_right), memory(tmp2->rb_left)); tmp2 == rid; }; }
have parent->rb_right == 0 by { transport(at(after_detach, parent->rb_right) == 0, parent->rb_right == 0) using { at(after_detach, parent->rb_right) == 0; separate(memory(parent->rb_right), memory(tmp2->rb_left)); tmp2 == rid; }; }
have tmp2->rb_left == sibling by { simp(); }
have rid->rb_left == nid by { transport(tmp2->rb_left == sibling, rid->rb_left == nid) using { tmp2->rb_left == sibling; tmp2 == rid; sibling == nid; }; }
have parent->__rb_parent_color == address(sid) by { transport(at(after_detach, parent->__rb_parent_color) == address(sid), parent->__rb_parent_color == address(sid)) using { at(after_detach, parent->__rb_parent_color) == address(sid); separate(memory(parent->__rb_parent_color), memory(tmp2->rb_left)); tmp2 == rid; }; }
have nid->rb_right == 0 by { transport(at(after_detach, nid->rb_right) == 0, nid->rb_right == 0) using { at(after_detach, nid->rb_right) == 0; separate(memory(nid->rb_right), memory(tmp2->rb_left)); tmp2 == rid; sibling == nid; }; }
have nid->rb_left == 0 by { transport(at(after_detach, nid->rb_left) == 0, nid->rb_left == 0) using { at(after_detach, nid->rb_left) == 0; separate(memory(nid->rb_left), memory(tmp2->rb_left)); tmp2 == rid; sibling == nid; }; }
mark after_attach;

step();
have rid->rb_right == 0 by { transport(at(after_attach, rid->rb_right) == 0, rid->rb_right == 0) using { at(after_attach, rid->rb_right) == 0; separate(memory(rid->rb_right), memory(parent->rb_left)); }; }
have parent->rb_right == 0 by { transport(at(after_attach, parent->rb_right) == 0, parent->rb_right == 0) using { at(after_attach, parent->rb_right) == 0; separate(memory(parent->rb_right), memory(parent->rb_left)); }; }
have parent->__rb_parent_color == address(sid) by { transport(at(after_attach, parent->__rb_parent_color) == address(sid), parent->__rb_parent_color == address(sid)) using { at(after_attach, parent->__rb_parent_color) == address(sid); separate(memory(parent->__rb_parent_color), memory(parent->rb_left)); }; }
have nid->rb_right == 0 by { transport(at(after_attach, nid->rb_right) == 0, nid->rb_right == 0) using { at(after_attach, nid->rb_right) == 0; separate(memory(nid->rb_right), memory(parent->rb_left)); tmp2 == rid; sibling == nid; }; }
have nid->rb_left == 0 by { transport(at(after_attach, nid->rb_left) == 0, nid->rb_left == 0) using { at(after_attach, nid->rb_left) == 0; separate(memory(nid->rb_left), memory(parent->rb_left)); tmp2 == rid; sibling == nid; }; }
mark before_callback;

step();
step();
step();
step();
step();
have sibling == rid by { simp(); }
have tmp1 == nid by { simp(); }
have tmp2 == rid by { simp(); }
have rid->rb_right == 0 by { transport(at(before_callback, rid->rb_right) == 0, rid->rb_right == 0) using { at(before_callback, rid->rb_right) == 0; separate(memory(rid->rb_right), memory(parent->rb_left)); separate(memory(rid->rb_right), memory(nid->rb_right)); separate(memory(rid->rb_right), memory(rid->rb_left)); at(inner_rotation, sibling) == nid; at(inner_rotation, tmp2) == rid; sibling == rid; tmp1 == nid; tmp2 == rid; }; }
have sibling->rb_right == 0 by { transport(rid->rb_right == 0, sibling->rb_right == 0) using { rid->rb_right == 0; sibling == rid; }; }
have parent->rb_right == 0 by { normalize() using { at(before_callback, parent->rb_right) == 0; } }
have separate(memory(parent->rb_right), memory(sibling->rb_right)) by { transport(separate(memory(parent->rb_right), memory(rid->rb_right)), separate(memory(parent->rb_right), memory(sibling->rb_right))) using { separate(memory(parent->rb_right), memory(rid->rb_right)); sibling == rid; }; }
have separate(memory(parent->rb_right), memory(tmp1->__rb_parent_color)) by { transport(separate(memory(parent->rb_right), memory(nid->__rb_parent_color)), separate(memory(parent->rb_right), memory(tmp1->__rb_parent_color))) using { separate(memory(parent->rb_right), memory(nid->__rb_parent_color)); tmp1 == nid; }; }
have separate(memory(parent->__rb_parent_color), memory(sibling->rb_right)) by { transport(separate(memory(parent->__rb_parent_color), memory(rid->rb_right)), separate(memory(parent->__rb_parent_color), memory(sibling->rb_right))) using { separate(memory(parent->__rb_parent_color), memory(rid->rb_right)); sibling == rid; }; }
have separate(memory(parent->__rb_parent_color), memory(tmp1->__rb_parent_color)) by { transport(separate(memory(parent->__rb_parent_color), memory(nid->__rb_parent_color)), separate(memory(parent->__rb_parent_color), memory(tmp1->__rb_parent_color))) using { separate(memory(parent->__rb_parent_color), memory(nid->__rb_parent_color)); tmp1 == nid; }; }
have separate(memory(rid->rb_right), memory(tmp1->__rb_parent_color)) by { transport(separate(memory(rid->rb_right), memory(nid->__rb_parent_color)), separate(memory(rid->rb_right), memory(tmp1->__rb_parent_color))) using { separate(memory(rid->rb_right), memory(nid->__rb_parent_color)); tmp1 == nid; }; }
have separate(memory(rid->rb_left), memory(tmp1->__rb_parent_color)) by { transport(separate(memory(rid->rb_left), memory(nid->__rb_parent_color)), separate(memory(rid->rb_left), memory(tmp1->__rb_parent_color))) using { separate(memory(rid->rb_left), memory(nid->__rb_parent_color)); tmp1 == nid; }; }
have parent->__rb_parent_color == address(sid) by { normalize() using { at(before_callback, parent->__rb_parent_color) == address(sid); } }
have nid->rb_right == 0 by { normalize() using { at(before_callback, nid->rb_right) == 0; } }
have separate(memory(nid->rb_right), memory(sibling->rb_right)) by { transport(separate(memory(nid->rb_right), memory(rid->rb_right)), separate(memory(nid->rb_right), memory(sibling->rb_right))) using { separate(memory(nid->rb_right), memory(rid->rb_right)); sibling == rid; }; }
have separate(memory(nid->rb_right), memory(tmp1->__rb_parent_color)) by { transport(separate(memory(nid->rb_right), memory(nid->__rb_parent_color)), separate(memory(nid->rb_right), memory(tmp1->__rb_parent_color))) using { separate(memory(nid->rb_right), memory(nid->__rb_parent_color)); tmp1 == nid; }; }
have nid->rb_left == 0 by { normalize() using { at(before_callback, nid->rb_left) == 0; } }
have separate(memory(nid->rb_left), memory(sibling->rb_right)) by { transport(separate(memory(nid->rb_left), memory(rid->rb_right)), separate(memory(nid->rb_left), memory(sibling->rb_right))) using { separate(memory(nid->rb_left), memory(rid->rb_right)); sibling == rid; }; }
have separate(memory(nid->rb_left), memory(tmp1->__rb_parent_color)) by { transport(separate(memory(nid->rb_left), memory(nid->__rb_parent_color)), separate(memory(nid->rb_left), memory(tmp1->__rb_parent_color))) using { separate(memory(nid->rb_left), memory(nid->__rb_parent_color)); tmp1 == nid; }; }
mark case4;
step();
step();
step();
step();
have sibling == rid by { simp(); }
have tmp1 == nid by { simp(); }
have tmp2 == 0 by { simp(); }
have parent->rb_right == 0 by { transport(at(case4, parent->rb_right) == 0, parent->rb_right == 0) using { at(case4, parent->rb_right) == 0; separate(memory(parent->rb_right), memory(sibling->rb_right)); separate(memory(parent->rb_right), memory(tmp1->__rb_parent_color)); separate(memory(parent->rb_right), memory(nid->rb_right)); separate(memory(parent->rb_right), memory(nid->__rb_parent_color)); separate(memory(parent->rb_right), memory(rid->rb_right)); separate(memory(parent->rb_right), memory(rid->rb_left)); sibling == rid; tmp1 == nid; at(inner_rotation, sibling) == nid; at(inner_rotation, tmp2) == rid; }; }
have parent->rb_left == 0 by { simp(); }
have sibling->rb_right == parent by { simp(); }
have rid->rb_right == parent by { transport(sibling->rb_right == parent, rid->rb_right == parent) using { sibling->rb_right == parent; sibling == rid; separate(memory(rid->rb_right), memory(tmp1->__rb_parent_color)); tmp1 == nid; }; }
have rid->rb_left == nid by { transport(at(after_attach, rid->rb_left) == nid, rid->rb_left == nid) using { at(after_attach, rid->rb_left) == nid; separate(memory(rid->rb_left), memory(parent->rb_left)); separate(memory(rid->rb_left), memory(rid->rb_right)); separate(memory(rid->rb_left), memory(tmp1->__rb_parent_color)); sibling == rid; tmp1 == nid; }; }
have tmp1->__rb_parent_color == (address(sibling) | 1) by { assumption(); }
have nid->__rb_parent_color == (address(rid) | 1) by { simp() using { tmp1->__rb_parent_color == (address(sibling) | 1); tmp1 == nid; sibling == rid; } }
step();
step();
have parent->__rb_parent_color == address(sid) by { transport(at(case4, parent->__rb_parent_color) == address(sid), parent->__rb_parent_color == address(sid)) using { at(case4, parent->__rb_parent_color) == address(sid); separate(memory(parent->__rb_parent_color), memory(sibling->rb_right)); separate(memory(parent->__rb_parent_color), memory(tmp1->__rb_parent_color)); sibling == rid; tmp1 == nid; at(inner_rotation, sibling) == nid; at(inner_rotation, tmp2) == rid; separate(memory(parent->__rb_parent_color), memory(nid->rb_right)); separate(memory(parent->__rb_parent_color), memory(nid->__rb_parent_color)); separate(memory(parent->__rb_parent_color), memory(rid->rb_right)); separate(memory(parent->__rb_parent_color), memory(rid->rb_left)); separate(memory(parent->__rb_parent_color), memory(parent->rb_left)); }; }
have parent->__rb_parent_color == address(sid) + color_bit(Color::Red) by { unfold(color_bit(Color::Red)); normalize() using { parent->__rb_parent_color == address(sid); } }
apply(ctx_parent_word_from_color(rotation_ctx.model, sid, parent->__rb_parent_color, Color::Red));
have nid->rb_right == 0 by { transport(at(case4, nid->rb_right) == 0, nid->rb_right == 0) using { at(case4, nid->rb_right) == 0; separate(memory(nid->rb_right), memory(parent->rb_left)); separate(memory(nid->rb_right), memory(sibling->rb_right)); separate(memory(nid->rb_right), memory(tmp1->__rb_parent_color)); sibling == rid; tmp1 == nid; }; }
have nid->rb_left == 0 by { transport(at(case4, nid->rb_left) == 0, nid->rb_left == 0) using { at(case4, nid->rb_left) == 0; separate(memory(nid->rb_left), memory(parent->rb_left)); separate(memory(nid->rb_left), memory(sibling->rb_right)); separate(memory(nid->rb_left), memory(tmp1->__rb_parent_color)); sibling == rid; tmp1 == nid; }; }
mark second_rotation;
let { after: rotation_ctx } = step(__rb_rotate_set_parents(parent, sibling, root, 1), { c: rotation_ctx });
step();
have parent->__rb_parent_color == address(rid) + 1 by { simp(); }
have (parent->__rb_parent_color & 1) == 1 by { rewrite(parent->__rb_parent_color == address(rid) + 1); arithmetic() using { aligned(rid, 8); } }
have sibling->__rb_parent_color == address(sid) by { simp(); }
have rid->__rb_parent_color == sibling->__rb_parent_color by { normalize() using { sibling == rid; } }
have rid->__rb_parent_color == address(sid) by { rewrite(rid->__rb_parent_color == sibling->__rb_parent_color); assumption(); }
have (rid->__rb_parent_color & 1) == 0 by { rewrite(rid->__rb_parent_color == address(sid)); arithmetic() using { aligned(sid, 8); } }
have nid->__rb_parent_color == at(second_rotation, nid->__rb_parent_color) by { normalize() using { sibling == rid; tmp1 == nid; } }
have nid->__rb_parent_color == (address(rid) | 1) by { rewrite(nid->__rb_parent_color == at(second_rotation, nid->__rb_parent_color)); simp(); }
have nid->__rb_parent_color == address(rid) + 1 by { rewrite(nid->__rb_parent_color == (address(rid) | 1)); arithmetic() using { aligned(rid, 8); } }
have (nid->__rb_parent_color & 1) == 1 by { rewrite(nid->__rb_parent_color == address(rid) + 1); arithmetic() using { aligned(rid, 8); } }
have parent->rb_right == 0 by { normalize() using { at(second_rotation, parent->rb_right) == 0; sibling == rid; tmp1 == nid; } }
have parent->rb_left == 0 by { normalize() using { at(second_rotation, parent->rb_left) == 0; sibling == rid; tmp1 == nid; } }
have nid->rb_right == 0 by { normalize() using { at(second_rotation, nid->rb_right) == 0; sibling == rid; tmp1 == nid; } }
have nid->rb_left == 0 by { normalize() using { at(second_rotation, nid->rb_left) == 0; sibling == rid; tmp1 == nid; } }
have rb_parent_is(RbTree::Empty, parent) == 1 by { unfold(rb_parent_is(RbTree::Empty, parent)); normalize(); }
have rb_parent_is(RbTree::Empty, nid) == 1 by { unfold(rb_parent_is(RbTree::Empty, nid)); normalize(); }
have parent->__rb_parent_color == address(rid) + (parent->__rb_parent_color & 1) by { rewrite((parent->__rb_parent_color & 1) == 1); assumption(); }
have nid->__rb_parent_color == address(rid) + (nid->__rb_parent_color & 1) by { rewrite((nid->__rb_parent_color & 1) == 1); assumption(); }
have rid->__rb_parent_color == address(sid) + (rid->__rb_parent_color & 1) by { rewrite((rid->__rb_parent_color & 1) == 0); normalize() using { rid->__rb_parent_color == address(sid); } }
let pl = fold(rb_at(parent->rb_right), { model: RbTree::Empty });
let pr = fold(rb_at(parent->rb_left), { model: RbTree::Empty });
let parent_tree = fold(rb_at(parent), { model: RbTree::Node(parent, rid, Color::Black, RbTree::Empty, RbTree::Empty) }, { right: pl, left: pr });
let rl = fold(rb_at(nid->rb_right), { model: RbTree::Empty });
let rr = fold(rb_at(nid->rb_left), { model: RbTree::Empty });
let red_tree = fold(rb_at(nid), { model: RbTree::Node(nid, rid, Color::Black, RbTree::Empty, RbTree::Empty) }, { right: rl, left: rr });
apply(rb_parent_is_node_of(parent, rid, Color::Black, RbTree::Empty, RbTree::Empty));
apply(rb_parent_is_node_of(nid, rid, Color::Black, RbTree::Empty, RbTree::Empty));
have rid->rb_right == parent by { normalize() using { at(second_rotation, rid->rb_right) == parent; sibling == rid; tmp1 == nid; } }
have rid->rb_left == nid by { normalize() using { at(second_rotation, rid->rb_left) == nid; sibling == rid; tmp1 == nid; } }
let sub = fold(rb_at(rid), { model: RbTree::Node(rid, sid, Color::Red, RbTree::Node(nid, rid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(parent, rid, Color::Black, RbTree::Empty, RbTree::Empty)) }, { right: parent_tree, left: red_tree });
have rotation_ctx.model == Context::Right(sid, above, Color::Black, far_model, um) by { simp(); }
have rb_tree_parent_consistent(plug(rotation_ctx.model, sub.model)) == 1 by { unfold(rb_tree_parent_consistent(plug(rotation_ctx.model, sub.model))); rewrite(rotation_ctx.model == Context::Right(sid, above, Color::Black, far_model, um)); rewrite(sub.model == RbTree::Node(rid, sid, Color::Red, RbTree::Node(nid, rid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(parent, rid, Color::Black, RbTree::Empty, RbTree::Empty))); rewrite(plug(Context::Right(sid, above, Color::Black, far_model, um), RbTree::Node(rid, sid, Color::Red, RbTree::Node(nid, rid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(parent, rid, Color::Black, RbTree::Empty, RbTree::Empty))) == plug(um, RbTree::Node(sid, above, Color::Black, far_model, RbTree::Node(rid, sid, Color::Red, RbTree::Node(nid, rid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(parent, rid, Color::Black, RbTree::Empty, RbTree::Empty))))); assumption(); }
mark closing_root;
let { whole: whole } = refold_to_root(rid, root, { c: rotation_ctx, t: sub });
have whole.model == plug(um, RbTree::Node(sid, above, Color::Black, far_model, RbTree::Node(rid, sid, Color::Red, RbTree::Node(nid, rid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(parent, rid, Color::Black, RbTree::Empty, RbTree::Empty)))) by { rewrite(whole.model == plug(at(closing_root, rotation_ctx.model), RbTree::Node(rid, sid, Color::Red, RbTree::Node(nid, rid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(parent, rid, Color::Black, RbTree::Empty, RbTree::Empty)))); rewrite(at(closing_root, rotation_ctx.model) == Context::Right(sid, above, Color::Black, far_model, um)); rewrite(plug(Context::Right(sid, above, Color::Black, far_model, um), RbTree::Node(rid, sid, Color::Red, RbTree::Node(nid, rid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(parent, rid, Color::Black, RbTree::Empty, RbTree::Empty))) == plug(um, RbTree::Node(sid, above, Color::Black, far_model, RbTree::Node(rid, sid, Color::Red, RbTree::Node(nid, rid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(parent, rid, Color::Black, RbTree::Empty, RbTree::Empty))))); normalize(); }
have whole.model == erase_right_red_sibling_inner_result(old(c.model)) by { rewrite(whole.model == plug(um, RbTree::Node(sid, above, Color::Black, far_model, RbTree::Node(rid, sid, Color::Red, RbTree::Node(nid, rid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(parent, rid, Color::Black, RbTree::Empty, RbTree::Empty))))); rewrite(old(c.model) == Context::Right(parent, above, Color::Black, RbTree::Node(sid, parent, Color::Red, far_model, RbTree::Node(nid, sid, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty))), um)); unfold(erase_right_red_sibling_inner_result(Context::Right(parent, above, Color::Black, RbTree::Node(sid, parent, Color::Red, far_model, RbTree::Node(nid, sid, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty))), um))); normalize(); }
have is_rb_root(whole.model) == 1 by { rewrite(whole.model == plug(um, RbTree::Node(sid, above, Color::Black, far_model, RbTree::Node(rid, sid, Color::Red, RbTree::Node(nid, rid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(parent, rid, Color::Black, RbTree::Empty, RbTree::Empty))))); assumption(); }
have rb_parent_consistent(whole.model, 0) == 1 by { rewrite(whole.model == plug(um, RbTree::Node(sid, above, Color::Black, far_model, RbTree::Node(rid, sid, Color::Red, RbTree::Node(nid, rid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(parent, rid, Color::Black, RbTree::Empty, RbTree::Empty))))); assumption(); }
have rb_inorder(whole.model) == rb_inorder(plug(old(c.model), RbTree::Empty)) by { rewrite(whole.model == plug(um, RbTree::Node(sid, above, Color::Black, far_model, RbTree::Node(rid, sid, Color::Red, RbTree::Node(nid, rid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(parent, rid, Color::Black, RbTree::Empty, RbTree::Empty))))); rewrite(old(c.model) == Context::Right(parent, above, Color::Black, RbTree::Node(sid, parent, Color::Red, far_model, RbTree::Node(nid, sid, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty))), um)); assumption(); }
execute(); simp();
},
}
},
}
},
}
},
}
}
