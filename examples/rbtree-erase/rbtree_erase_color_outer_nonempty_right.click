// Erase-color case 4 for an empty right deficit, nonempty near child, and red far child.
// The near subtree retains its color and children when reparented.
// The parent may have either color and sit under any outer context. The proof
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
    have old != 0 by assumption();
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
                    have identity->rb_left == 0;
                    have parent->rb_left == 0;
                    have old != 0 by assumption();
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
            have parent == 0;
            have ctx_node_is(d.model, parent) == 1 by { rewrite(d.model == Context::Top); rewrite(parent == 0); unfold(ctx_node_is(Context::Top, 0)); normalize(); }
            step(); step();
            have old->__rb_parent_color == (address(new) | color);
            have old->__rb_parent_color == address(new) + color by {
                rewrite(old->__rb_parent_color == (address(new) | color));
                if color == 0 { rewrite(color == 0); normalize(); } else {
                    have color == 1 by { arithmetic() using { 0 <= color; color <= 1; not(color == 0); } }
                    rewrite(color == 1);
                    arithmetic() using { aligned(new, 8); }
                }
            }
            mark words;
            have at(words, old->__rb_parent_color) == address(new) + color by assumption();
            let { after: after } = step(__rb_change_child(old, new, parent, root), { before: d });
            have old->__rb_parent_color == address(new) + color by {
                have old->__rb_parent_color == at(words, old->__rb_parent_color);
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
            have parent == id;
            have ctx_node_is(d.model, parent) == 1 by { rewrite(d.model == Context::Left(id, above, pc, sibling, up)); rewrite(parent == id); unfold(ctx_node_is(Context::Left(id, above, pc, sibling, up), id)); normalize(); }
            step(); step();
            have old->__rb_parent_color == (address(new) | color);
            have old->__rb_parent_color == address(new) + color by {
                rewrite(old->__rb_parent_color == (address(new) | color));
                if color == 0 { rewrite(color == 0); normalize(); } else {
                    have color == 1 by { arithmetic() using { 0 <= color; color <= 1; not(color == 0); } }
                    rewrite(color == 1);
                    arithmetic() using { aligned(new, 8); }
                }
            }
            mark words;
            have at(words, old->__rb_parent_color) == address(new) + color by assumption();
            let { after: after } = step(__rb_change_child(old, new, parent, root), { before: d });
            have old->__rb_parent_color == address(new) + color by {
                have old->__rb_parent_color == at(words, old->__rb_parent_color);
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
            have parent == id;
            have ctx_node_is(d.model, parent) == 1 by { rewrite(d.model == Context::Right(id, above, pc, sibling, up)); rewrite(parent == id); unfold(ctx_node_is(Context::Right(id, above, pc, sibling, up), id)); normalize(); }
            step(); step();
            have old->__rb_parent_color == (address(new) | color);
            have old->__rb_parent_color == address(new) + color by {
                rewrite(old->__rb_parent_color == (address(new) | color));
                if color == 0 { rewrite(color == 0); normalize(); } else {
                    have color == 1 by { arithmetic() using { 0 <= color; color <= 1; not(color == 0); } }
                    rewrite(color == 1);
                    arithmetic() using { aligned(new, 8); }
                }
            }
            mark words;
            have at(words, old->__rb_parent_color) == address(new) + color by assumption();
            let { after: after } = step(__rb_change_child(old, new, parent, root), { before: d });
            have old->__rb_parent_color == address(new) + color by {
                have old->__rb_parent_color == at(words, old->__rb_parent_color);
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

void rb_set_parent(struct rb_node* rb, struct rb_node* p) {
    consumes before: rb_at(rb);
    requires rb != 0;
    requires aligned(p, 8);
    produces after: rb_at(rb);
    ensures after.model == rb_reparent(old(before.model), p);
} by {
    match before.model {
        RbTree::Empty => {
            unfold(before);
            contradiction(rb != 0);
        },
        RbTree::Node(node, parent, color, lm, rm) => {
            let { left: left, right: right } = unfold(before);
            match color {
                Color::Red => {
                    have (rb->__rb_parent_color & 1) == 0 by {
                        rewrite((rb->__rb_parent_color & 1) == color_bit(color));
                        rewrite(color == Color::Red); unfold(color_bit(Color::Red)); normalize();
                    }
                    execute();
                    have rb->__rb_parent_color == (address(p) | 0);
                    have rb->__rb_parent_color == address(p) + 0 by {
                        rewrite(rb->__rb_parent_color == (address(p) | 0)); normalize();
                    }
                    have (rb->__rb_parent_color & 1) == 0 by {
                        rewrite(rb->__rb_parent_color == address(p) + 0); arithmetic() using { aligned(p, 8); }
                    }
                    have color_bit(color) == 0 by { rewrite(color == Color::Red); unfold(color_bit(Color::Red)); normalize(); }
                    let after = fold(rb_at(rb), { model: RbTree::Node(node, p, color, lm, rm) }, { left: left, right: right });
                    have after.model == rb_reparent(old(before.model), p) by {
                        rewrite(old(before.model) == RbTree::Node(node, parent, color, lm, rm));
                        unfold(rb_reparent(RbTree::Node(node, parent, color, lm, rm), p)); simp();
                    }
                    simp();
                },
                Color::Black => {
                    have (rb->__rb_parent_color & 1) == 1 by {
                        rewrite((rb->__rb_parent_color & 1) == color_bit(color));
                        rewrite(color == Color::Black); unfold(color_bit(Color::Black)); normalize();
                    }
                    execute();
                    have rb->__rb_parent_color == (1 | address(p));
                    have rb->__rb_parent_color == address(p) + 1 by {
                        rewrite(rb->__rb_parent_color == (1 | address(p))); arithmetic() using { aligned(p, 8); }
                    }
                    have (rb->__rb_parent_color & 1) == 1 by {
                        rewrite(rb->__rb_parent_color == address(p) + 1); arithmetic() using { aligned(p, 8); }
                    }
                    have color_bit(color) == 1 by { rewrite(color == Color::Black); unfold(color_bit(Color::Black)); normalize(); }
                    let after = fold(rb_at(rb), { model: RbTree::Node(node, p, color, lm, rm) }, { left: left, right: right });
                    have after.model == rb_reparent(old(before.model), p) by {
                        rewrite(old(before.model) == RbTree::Node(node, parent, color, lm, rm));
                        unfold(rb_reparent(RbTree::Node(node, parent, color, lm, rm), p)); simp();
                    }
                    simp();
                },
            }
        },
    }
}

function erase_right_outer_nonempty(ctx: Context, parent: struct rb_node*) -> int32 {
    match ctx {
        Context::Top => 0,
        Context::Left(id, above, pc, sm, um) => 0,
        Context::Right(id, above, pc, sm, um) => if id == parent {
            match sm {
                RbTree::Empty => 0,
                RbTree::Node(sid, sp, sc, far_model, near_model) => if sc == Color::Black {
                    match near_model {
                        RbTree::Empty => 0,
                        RbTree::Node(nid, np, nc, nrm, nlm) => match far_model {
                            RbTree::Empty => 0,
                            RbTree::Node(rid, rp, rc, far_left_model, far_right_model) => if rc == Color::Red { 1 } else { 0 },
                        },
                    }
                } else { 0 },
            }
        } else { 0 },
    }
}
function erase_right_outer_nonempty_result(ctx: Context) -> RbTree {
    match ctx {
        Context::Top => RbTree::Empty,
        Context::Left(id, above, pc, sm, um) => RbTree::Empty,
        Context::Right(id, above, pc, sm, um) => match sm {
            RbTree::Empty => RbTree::Empty,
            RbTree::Node(sid, sp, sc, far_model, near_model) => match far_model {
                RbTree::Empty => RbTree::Empty,
                RbTree::Node(rid, rp, rc, far_left_model, far_right_model) => plug(um, RbTree::Node(sid, above, pc, RbTree::Node(rid, sid, Color::Black, far_left_model, far_right_model), RbTree::Node(id, sid, Color::Black, rb_reparent(near_model, id), RbTree::Empty))),
            },
        },
    }
}
contract void AugmentRotate(struct rb_node* old, struct rb_node* new) {
    requires new != 0; ensures 1 == 1;
}
void ____rb_erase_color(struct rb_node* parent, struct rb_root* root,
void (*augment_rotate)(struct rb_node* old, struct rb_node* new)) {
    consumes c: ctx_at(0, root);
    requires erase_right_outer_nonempty(c.model, parent) == 1;
    requires ctx_rb(c.model, Nat::Succ(black_height(RbTree::Empty)), Color::Black) == 1;
    requires rb_parent_consistent(plug(c.model, RbTree::Empty), 0) == 1;
    requires AugmentRotate(augment_rotate);
    produces whole: rb_root_at(root);
    ensures whole.model == erase_right_outer_nonempty_result(old(c.model));
    ensures is_rb_root(whole.model) == 1;
    ensures rb_parent_consistent(whole.model, 0) == 1;
    ensures rb_inorder(whole.model) == rb_inorder(plug(old(c.model), RbTree::Empty));
} by {
    match c.model {
        Context::Top => {
            have erase_right_outer_nonempty(c.model, parent) == 0 by {
                rewrite(c.model == Context::Top); unfold(erase_right_outer_nonempty(Context::Top, parent)); normalize() using {  }
            }
            have not(erase_right_outer_nonempty(c.model, parent) == 1) by { rewrite(erase_right_outer_nonempty(c.model, parent) == 0); normalize(); }
            contradiction(erase_right_outer_nonempty(c.model, parent) == 1);
        },
        Context::Left(id, above, pc, sm, um) => {
            have erase_right_outer_nonempty(c.model, parent) == 0 by {
                rewrite(c.model == Context::Left(id, above, pc, sm, um)); unfold(erase_right_outer_nonempty(Context::Left(id, above, pc, sm, um), parent)); normalize() using {  }
            }
            have not(erase_right_outer_nonempty(c.model, parent) == 1) by { rewrite(erase_right_outer_nonempty(c.model, parent) == 0); normalize(); }
            contradiction(erase_right_outer_nonempty(c.model, parent) == 1);
        },
        Context::Right(id, above, pc, sm, um) => {
            have id == parent by { if id == parent { assumption(); } else {
                    have erase_right_outer_nonempty(c.model, parent) == 0 by {
                        rewrite(c.model == Context::Right(id, above, pc, sm, um)); unfold(erase_right_outer_nonempty(Context::Right(id, above, pc, sm, um), parent)); normalize() using { not(id == parent); }
                    }
                    have not(erase_right_outer_nonempty(c.model, parent) == 1) by { rewrite(erase_right_outer_nonempty(c.model, parent) == 0); normalize(); }
                    contradiction(erase_right_outer_nonempty(c.model, parent) == 1);
                } }
            match sm {
                RbTree::Empty => {
                    have erase_right_outer_nonempty(c.model, parent) == 0 by {
                        rewrite(c.model == Context::Right(id, above, pc, sm, um)); rewrite(sm == RbTree::Empty); unfold(erase_right_outer_nonempty(Context::Right(id, above, pc, RbTree::Empty, um), parent)); normalize() using { id == parent; }
                    }
                    have not(erase_right_outer_nonempty(c.model, parent) == 1) by { rewrite(erase_right_outer_nonempty(c.model, parent) == 0); normalize(); }
                    contradiction(erase_right_outer_nonempty(c.model, parent) == 1);
                },
                RbTree::Node(sid, sp, sc, far_model, near_model) => {
                    have sc == Color::Black by { if sc == Color::Black { assumption(); } else {
                            have erase_right_outer_nonempty(c.model, parent) == 0 by {
                                rewrite(c.model == Context::Right(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, sp, sc, far_model, near_model)); unfold(erase_right_outer_nonempty(Context::Right(id, above, pc, RbTree::Node(sid, sp, sc, far_model, near_model), um), parent)); normalize() using { id == parent; not(sc == Color::Black); }
                            }
                            have not(erase_right_outer_nonempty(c.model, parent) == 1) by { rewrite(erase_right_outer_nonempty(c.model, parent) == 0); normalize(); }
                            contradiction(erase_right_outer_nonempty(c.model, parent) == 1);
                        } }
                    match near_model {
                        RbTree::Empty => {
                            have erase_right_outer_nonempty(c.model, parent) == 0 by {
                                rewrite(c.model == Context::Right(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, sp, sc, far_model, near_model)); rewrite(near_model == RbTree::Empty); unfold(erase_right_outer_nonempty(Context::Right(id, above, pc, RbTree::Node(sid, sp, sc, far_model, RbTree::Empty), um), parent)); normalize() using { id == parent; sc == Color::Black; }
                            }
                            have not(erase_right_outer_nonempty(c.model, parent) == 1) by { rewrite(erase_right_outer_nonempty(c.model, parent) == 0); normalize(); }
                            contradiction(erase_right_outer_nonempty(c.model, parent) == 1);
                        },
                        RbTree::Node(nid, np, nc, nrm, nlm) => {
                            match far_model {
                                RbTree::Empty => {
                                    have erase_right_outer_nonempty(c.model, parent) == 0 by {
                                        rewrite(c.model == Context::Right(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, sp, sc, far_model, near_model)); rewrite(near_model == RbTree::Node(nid, np, nc, nrm, nlm)); rewrite(far_model == RbTree::Empty); unfold(erase_right_outer_nonempty(Context::Right(id, above, pc, RbTree::Node(sid, sp, sc, RbTree::Empty, RbTree::Node(nid, np, nc, nrm, nlm)), um), parent)); normalize() using { id == parent; sc == Color::Black; }
                                    }
                                    have not(erase_right_outer_nonempty(c.model, parent) == 1) by { rewrite(erase_right_outer_nonempty(c.model, parent) == 0); normalize(); }
                                    contradiction(erase_right_outer_nonempty(c.model, parent) == 1);
                                },
                                RbTree::Node(rid, rp, rc, far_left_model, far_right_model) => {
                                    have rc == Color::Red by { if rc == Color::Red { assumption(); } else {
                                            have erase_right_outer_nonempty(c.model, parent) == 0 by {
                                                rewrite(c.model == Context::Right(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, sp, sc, far_model, near_model)); rewrite(near_model == RbTree::Node(nid, np, nc, nrm, nlm)); rewrite(far_model == RbTree::Node(rid, rp, rc, far_left_model, far_right_model)); unfold(erase_right_outer_nonempty(Context::Right(id, above, pc, RbTree::Node(sid, sp, sc, RbTree::Node(rid, rp, rc, far_left_model, far_right_model), RbTree::Node(nid, np, nc, nrm, nlm)), um), parent)); normalize() using { id == parent; sc == Color::Black; not(rc == Color::Red); }
                                            }
                                            have not(erase_right_outer_nonempty(c.model, parent) == 1) by { rewrite(erase_right_outer_nonempty(c.model, parent) == 0); normalize(); }
                                            contradiction(erase_right_outer_nonempty(c.model, parent) == 1);
                                        } }
                                    apply(plug_parent_consistent_ctx(c.model, RbTree::Empty, 0));
                                    have ctx_consistent(Context::Right(id, above, pc, sm, um), RbTree::Empty, 0) == 1 by { rewrite(Context::Right(id, above, pc, sm, um) == c.model); assumption(); }
                                    apply(ctx_consistent_right_sibling(id, above, pc, sm, um, RbTree::Empty, 0));
                                    have rb_parent_consistent(RbTree::Node(sid, sp, sc, far_model, near_model), id) == 1 by { rewrite(RbTree::Node(sid, sp, sc, far_model, near_model) == sm); assumption(); }
                                    apply(rb_parent_consistent_node_fixes_parent(sid, sp, sc, far_model, near_model, id));
                                    have sp == parent;
                                    apply(rb_parent_consistent_node_right(sid, sp, sc, far_model, near_model, id));
                                    have rb_parent_consistent(RbTree::Node(nid, np, nc, nrm, nlm), sid) == 1 by { rewrite(RbTree::Node(nid, np, nc, nrm, nlm) == near_model); assumption(); }
                                    apply(rb_parent_consistent_node_fixes_parent(nid, np, nc, nrm, nlm, sid));
                                    have np == sid by assumption();
                                    apply(rb_parent_consistent_node_left(sid, sp, sc, far_model, near_model, id));
                                    have rb_parent_consistent(RbTree::Node(rid, rp, rc, far_left_model, far_right_model), sid) == 1 by { rewrite(RbTree::Node(rid, rp, rc, far_left_model, far_right_model) == far_model); assumption(); }
                                    apply(rb_parent_consistent_node_fixes_parent(rid, rp, rc, far_left_model, far_right_model, sid));
                                    have rp == sid by assumption();
                                    have c.model == Context::Right(parent, above, pc, RbTree::Node(sid, parent, Color::Black, RbTree::Node(rid, sid, Color::Red, far_left_model, far_right_model), RbTree::Node(nid, sid, nc, nrm, nlm)), um) by { rewrite(c.model == Context::Right(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, sp, sc, far_model, near_model)); rewrite(near_model == RbTree::Node(nid, np, nc, nrm, nlm)); rewrite(far_model == RbTree::Node(rid, rp, rc, far_left_model, far_right_model)); rewrite(id == parent); rewrite(sc == Color::Black); rewrite(rc == Color::Red); rewrite(sp == parent); rewrite(np == sid); rewrite(rp == sid); normalize(); }
                                    let { sibling: s, up: u } = unfold(c);
                                    let { right: near_tree, left: far_tree } = unfold(s);
                                    let { right: nl, left: nr } = unfold(near_tree);
                                    let { right: far_right, left: far_left } = unfold(far_tree);
                                    have old(c.model) == Context::Right(parent, above, pc, RbTree::Node(sid, parent, Color::Black, RbTree::Node(rid, sid, Color::Red, far_left_model, far_right_model), RbTree::Node(nid, sid, nc, nrm, nlm)), um) by { rewrite(old(c.model) == Context::Right(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, sp, sc, far_model, near_model)); rewrite(near_model == RbTree::Node(nid, np, nc, nrm, nlm)); rewrite(far_model == RbTree::Node(rid, rp, rc, far_left_model, far_right_model)); rewrite(id == parent); rewrite(sc == Color::Black); rewrite(rc == Color::Red); rewrite(sp == parent); rewrite(np == sid); rewrite(rp == sid); normalize(); }
                                    have is_rb(RbTree::Empty) == 1 by { unfold(is_rb(RbTree::Empty)); normalize(); }
                                    have rb_root_black(RbTree::Empty) == 1 by { unfold(rb_root_black(RbTree::Empty)); normalize(); }
                                    have ctx_rb(Context::Right(parent, above, pc, RbTree::Node(sid, parent, Color::Black, RbTree::Node(rid, sid, Color::Red, far_left_model, far_right_model), RbTree::Node(nid, sid, nc, nrm, nlm)), um), Nat::Succ(black_height(RbTree::Empty)), Color::Black) == 1 by { rewrite(Context::Right(parent, above, pc, RbTree::Node(sid, parent, Color::Black, RbTree::Node(rid, sid, Color::Red, far_left_model, far_right_model), RbTree::Node(nid, sid, nc, nrm, nlm)), um) == old(c.model)); simp(); }
                                    have rb_parent_consistent(plug(Context::Right(parent, above, pc, RbTree::Node(sid, parent, Color::Black, RbTree::Node(rid, sid, Color::Red, far_left_model, far_right_model), RbTree::Node(nid, sid, nc, nrm, nlm)), um), RbTree::Empty), 0) == 1 by { rewrite(Context::Right(parent, above, pc, RbTree::Node(sid, parent, Color::Black, RbTree::Node(rid, sid, Color::Red, far_left_model, far_right_model), RbTree::Node(nid, sid, nc, nrm, nlm)), um) == old(c.model)); simp(); }
                                    apply(ctx_erase_case4_right_exit(above, parent, pc, sid, rid, RbTree::Empty, RbTree::Node(nid, sid, nc, nrm, nlm), far_left_model, far_right_model, um));
                                    have parent->rb_right == 0;
                                    have parent->rb_left == sid;
                                    have sid == parent->rb_left;
                                    have aligned(sid, 8) by { rewrite(sid == parent->rb_left); assumption(); }
                                    have aligned(parent, 8);
                                    have sid->rb_right == nid;
                                    have sid->rb_left == rid;
                                    have nid == sid->rb_right;
                                    have rid == sid->rb_left;
                                    have aligned(rid, 8) by { rewrite(rid == sid->rb_left); assumption(); }
                                    have (sid->__rb_parent_color & 1) == 1 by { rewrite((sid->__rb_parent_color & 1) == color_bit(Color::Black)); unfold(color_bit(Color::Black)); normalize(); }
                                    have (rid->__rb_parent_color & 1) == 0 by { rewrite((rid->__rb_parent_color & 1) == color_bit(Color::Red)); unfold(color_bit(Color::Red)); normalize(); }
                                    have parent->__rb_parent_color == address(above) + color_bit(pc) by { rewrite(parent->__rb_parent_color == address(above) + (parent->__rb_parent_color & 1)); rewrite((parent->__rb_parent_color & 1) == color_bit(pc)); normalize(); }
                                    apply(ctx_parent_word_from_color(u.model, above, parent->__rb_parent_color, pc));
                                    let near = fold(rb_at(nid), { model: RbTree::Node(nid, sid, nc, nrm, nlm) }, { right: nl, left: nr });
                                    have parent->rb_left->rb_right == nid;
                                    mark inputs;
                                    execute_until(loop(0));
                                    step(); # Enter the mirrored arm and load the left sibling.
                                    step();
                                    step();
                                    step();
                                    step();
                                    step();
                                    step();
                                    step();
                                    step();
                                    step();
                                    step();
                                    step();
                                    step();
                                    step();
                                    have tmp1 == rid;
                                    have tmp2 == nid;
                                    have sibling == sid;
                                    have rid->__rb_parent_color == (address(sid) | 1);
                                    mark near_update;
                                    let { after: near } = step(rb_set_parent(tmp2, parent), { before: near });
                                    have near.model == rb_reparent(RbTree::Node(nid, sid, nc, nrm, nlm), parent);
                                    have rid->__rb_parent_color == at(near_update, rid->__rb_parent_color) by { normalize() using { tmp1 == rid; tmp2 == nid; } }
                                    have u.model == um;
                                    have parent->__rb_parent_color == at(inputs, parent->__rb_parent_color) by { normalize() using { tmp2 == nid; } }
                                    have parent->__rb_parent_color == address(above) + color_bit(pc) by { rewrite(parent->__rb_parent_color == at(inputs, parent->__rb_parent_color)); simp(); }
                                    apply(ctx_parent_word_from_color(u.model, above, parent->__rb_parent_color, pc));
                                    have rid->__rb_parent_color == (address(sid) | 1) by { rewrite(rid->__rb_parent_color == at(near_update, rid->__rb_parent_color)); simp(); }
                                    have parent->rb_left == nid by { normalize() using { at(inputs, parent->rb_left->rb_right) == nid; sibling == sid; tmp1 == rid; tmp2 == nid; } }
                                    have parent->rb_right == 0;
                                    mark rotation;
                                    let { after: u } = step(__rb_rotate_set_parents(parent, sibling, root, 1), { c: u });
                                    have parent->rb_left == nid by { normalize() using { at(inputs, parent->rb_left->rb_right) == nid; sibling == sid; tmp1 == rid; tmp2 == nid; } }
                                    have parent->rb_right == 0 by { normalize() using { at(rotation, parent->rb_right) == 0; } }
                                    have rid->__rb_parent_color == at(rotation, rid->__rb_parent_color) by { normalize() using { tmp1 == rid; } }
                                    step();
                                    have sid->__rb_parent_color == at(rotation, parent->__rb_parent_color);
                                    have sid->__rb_parent_color == address(above) + color_bit(pc) by { rewrite(sid->__rb_parent_color == at(rotation, parent->__rb_parent_color)); simp(); }
                                    have (sid->__rb_parent_color & 1) == color_bit(pc) by {
                                        rewrite(sid->__rb_parent_color == address(above) + color_bit(pc));
                                        if color_bit(pc) == 0 { rewrite(color_bit(pc) == 0); arithmetic() using { aligned(above, 8); } } else { apply(color_bit_nonzero_is_one(pc)); rewrite(color_bit(pc) == 1); arithmetic() using { aligned(above, 8); } }
                                    }
                                    have parent->__rb_parent_color == address(sid) + 1;
                                    have rid->__rb_parent_color == at(rotation, rid->__rb_parent_color) by { normalize() using { tmp1 == rid; } }
                                    have rid->__rb_parent_color == (address(sid) | 1) by { rewrite(rid->__rb_parent_color == at(rotation, rid->__rb_parent_color)); simp(); }
                                    have rid->__rb_parent_color == address(sid) + 1 by { rewrite(rid->__rb_parent_color == (address(sid) | 1)); arithmetic() using { aligned(sid, 8); } }
                                    have (parent->__rb_parent_color & 1) == 1 by { rewrite(parent->__rb_parent_color == address(sid) + 1); arithmetic() using { aligned(sid, 8); } }
                                    have parent->rb_right == 0;
                                    have parent->rb_left == nid by { normalize() using { at(rotation, parent->rb_left) == nid; tmp2 == nid; sibling == sid; tmp1 == rid; } }
                                    have rb_parent_is(RbTree::Empty, parent) == 1 by { unfold(rb_parent_is(RbTree::Empty, parent)); normalize(); }
                                    have rb_parent_is(rb_reparent(RbTree::Node(nid, sid, nc, nrm, nlm), parent), parent) == 1 by { unfold(rb_reparent(RbTree::Node(nid, sid, nc, nrm, nlm), parent)); unfold(rb_parent_is(RbTree::Node(nid, parent, nc, nrm, nlm), parent)); normalize(); }
                                    let parent_right = fold(rb_at(parent->rb_right), { model: RbTree::Empty });
                                    let parent_tree = fold(rb_at(parent), { model: RbTree::Node(parent, sid, Color::Black, rb_reparent(RbTree::Node(nid, sid, nc, nrm, nlm), parent), RbTree::Empty) }, { right: parent_right, left: near });
                                    apply(rb_parent_is_node_of(parent, sid, Color::Black, rb_reparent(RbTree::Node(nid, sid, nc, nrm, nlm), parent), RbTree::Empty));
                                    have (rid->__rb_parent_color & 1) == 1 by { rewrite(rid->__rb_parent_color == address(sid) + 1); arithmetic() using { aligned(sid, 8); } }
                                    let rid_tree = fold(rb_at(rid), { model: RbTree::Node(rid, sid, Color::Black, far_left_model, far_right_model) }, { right: far_right, left: far_left });
                                    apply(rb_parent_is_node_of(rid, sid, Color::Black, far_left_model, far_right_model));
                                    have sid->rb_right == parent by { normalize() using { sibling == sid; tmp1 == rid; tmp2 == nid; } }
                                    have sid->rb_left == rid;
                                    let sub = fold(rb_at(sid), { model: RbTree::Node(sid, above, pc, RbTree::Node(rid, sid, Color::Black, far_left_model, far_right_model), RbTree::Node(parent, sid, Color::Black, rb_reparent(RbTree::Node(nid, sid, nc, nrm, nlm), parent), RbTree::Empty)) }, { right: parent_tree, left: rid_tree });
                                    have rb_tree_parent_consistent(plug(u.model, sub.model)) == 1 by { unfold(rb_tree_parent_consistent(plug(u.model, sub.model))); rewrite(u.model == um); rewrite(sub.model == RbTree::Node(sid, above, pc, RbTree::Node(rid, sid, Color::Black, far_left_model, far_right_model), RbTree::Node(parent, sid, Color::Black, rb_reparent(RbTree::Node(nid, sid, nc, nrm, nlm), parent), RbTree::Empty))); assumption(); }
                                    mark closing_root;
                                    let { whole: whole } = refold_to_root(sid, root, { c: u, t: sub });
                                    have whole.model == plug(um, RbTree::Node(sid, above, pc, RbTree::Node(rid, sid, Color::Black, far_left_model, far_right_model), RbTree::Node(parent, sid, Color::Black, rb_reparent(RbTree::Node(nid, sid, nc, nrm, nlm), parent), RbTree::Empty))) by { rewrite(whole.model == plug(at(closing_root, u.model), RbTree::Node(sid, above, pc, RbTree::Node(rid, sid, Color::Black, far_left_model, far_right_model), RbTree::Node(parent, sid, Color::Black, rb_reparent(RbTree::Node(nid, sid, nc, nrm, nlm), parent), RbTree::Empty)))); rewrite(at(closing_root, u.model) == um); normalize(); }
                                    have whole.model == erase_right_outer_nonempty_result(old(c.model)) by { rewrite(whole.model == plug(um, RbTree::Node(sid, above, pc, RbTree::Node(rid, sid, Color::Black, far_left_model, far_right_model), RbTree::Node(parent, sid, Color::Black, rb_reparent(RbTree::Node(nid, sid, nc, nrm, nlm), parent), RbTree::Empty)))); rewrite(old(c.model) == Context::Right(parent, above, pc, RbTree::Node(sid, parent, Color::Black, RbTree::Node(rid, sid, Color::Red, far_left_model, far_right_model), RbTree::Node(nid, sid, nc, nrm, nlm)), um)); unfold(erase_right_outer_nonempty_result(Context::Right(parent, above, pc, RbTree::Node(sid, parent, Color::Black, RbTree::Node(rid, sid, Color::Red, far_left_model, far_right_model), RbTree::Node(nid, sid, nc, nrm, nlm)), um))); normalize(); }
                                    have is_rb_root(whole.model) == 1 by { rewrite(whole.model == plug(um, RbTree::Node(sid, above, pc, RbTree::Node(rid, sid, Color::Black, far_left_model, far_right_model), RbTree::Node(parent, sid, Color::Black, rb_reparent(RbTree::Node(nid, sid, nc, nrm, nlm), parent), RbTree::Empty)))); assumption(); }
                                    have rb_parent_consistent(whole.model, 0) == 1 by { rewrite(whole.model == plug(um, RbTree::Node(sid, above, pc, RbTree::Node(rid, sid, Color::Black, far_left_model, far_right_model), RbTree::Node(parent, sid, Color::Black, rb_reparent(RbTree::Node(nid, sid, nc, nrm, nlm), parent), RbTree::Empty)))); assumption(); }
                                    have rb_inorder(whole.model) == rb_inorder(plug(old(c.model), RbTree::Empty)) by { rewrite(whole.model == plug(um, RbTree::Node(sid, above, pc, RbTree::Node(rid, sid, Color::Black, far_left_model, far_right_model), RbTree::Node(parent, sid, Color::Black, rb_reparent(RbTree::Node(nid, sid, nc, nrm, nlm), parent), RbTree::Empty)))); rewrite(old(c.model) == Context::Right(parent, above, pc, RbTree::Node(sid, parent, Color::Black, RbTree::Node(rid, sid, Color::Red, far_left_model, far_right_model), RbTree::Node(nid, sid, nc, nrm, nlm)), um)); assumption(); }
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
