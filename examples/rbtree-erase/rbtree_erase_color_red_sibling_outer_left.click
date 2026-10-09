// Erase-color cases 1 and 4 for an empty left deficit and a red sibling.
// Its black near child has an empty near child and a red far leaf.
// Both rotations preserve an opaque far subtree and return the exact balanced root.
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

function erase_left_red_sibling_outer(ctx: Context, parent: struct rb_node*) -> int32 {
    match ctx { Context::Top => 0, Context::Right(id, above, pc, sm, um) => 0,
        Context::Left(id, above, pc, sm, um) => if id == parent { if pc == Color::Black { match sm { RbTree::Empty => 0, RbTree::Node(sid, sp, sc, near_model, far_model) => if sc == Color::Red { match near_model { RbTree::Empty => 0, RbTree::Node(nid, np, nc, nlm, nrm) => if nc == Color::Black { if nlm == RbTree::Empty { match nrm { RbTree::Empty => 0, RbTree::Node(rid, rp, rc, rlm, rrm) => if rc == Color::Red { if rlm == RbTree::Empty { if rrm == RbTree::Empty { 1 } else { 0 } } else { 0 } } else { 0 }, } } else { 0 } } else { 0 }, } } else { 0 }, } } else { 0 } } else { 0 }, }
}
function erase_left_red_sibling_outer_result(ctx: Context) -> RbTree {
    match ctx { Context::Top => RbTree::Empty, Context::Right(id, above, pc, sm, um) => RbTree::Empty,
        Context::Left(id, above, pc, sm, um) => match sm { RbTree::Empty => RbTree::Empty, RbTree::Node(sid, sp, sc, near_model, far_model) => match near_model {
                RbTree::Empty => RbTree::Empty, RbTree::Node(nid, np, nc, nlm, nrm) => match nrm { RbTree::Empty => RbTree::Empty, RbTree::Node(rid, rp, rc, rlm, rrm) => plug(um, RbTree::Node(sid, above, Color::Black, RbTree::Node(nid, sid, Color::Red, RbTree::Node(id, nid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(rid, nid, Color::Black, RbTree::Empty, RbTree::Empty)), far_model)), },
            }, }, }
}
contract void AugmentRotate(struct rb_node* old, struct rb_node* new) { requires new != 0; ensures 1 == 1; }
void ____rb_erase_color(struct rb_node* parent, struct rb_root* root,
void (*augment_rotate)(struct rb_node* old, struct rb_node* new)) {
    consumes c: ctx_at(0, root);
    requires erase_left_red_sibling_outer(c.model, parent) == 1;
    requires ctx_rb(c.model, Nat::Succ(black_height(RbTree::Empty)), Color::Black) == 1;
    requires rb_parent_consistent(plug(c.model, RbTree::Empty), 0) == 1;
    requires AugmentRotate(augment_rotate);
    produces whole: rb_root_at(root);
    ensures whole.model == erase_left_red_sibling_outer_result(old(c.model));
    ensures is_rb_root(whole.model) == 1;
    ensures rb_parent_consistent(whole.model, 0) == 1;
    ensures rb_inorder(whole.model) == rb_inorder(plug(old(c.model), RbTree::Empty));
} by { match c.model { Context::Top => {
            have erase_left_red_sibling_outer(c.model, parent) == 0 by { rewrite(c.model == Context::Top); unfold(erase_left_red_sibling_outer(Context::Top, parent)); normalize() using {  } }
            have not(erase_left_red_sibling_outer(c.model, parent) == 1) by { rewrite(erase_left_red_sibling_outer(c.model, parent) == 0); normalize(); }
            contradiction(erase_left_red_sibling_outer(c.model, parent) == 1);
        },
        Context::Right(id, above, pc, sm, um) => {
            have erase_left_red_sibling_outer(c.model, parent) == 0 by { rewrite(c.model == Context::Right(id, above, pc, sm, um)); unfold(erase_left_red_sibling_outer(Context::Right(id, above, pc, sm, um), parent)); normalize() using {  } }
            have not(erase_left_red_sibling_outer(c.model, parent) == 1) by { rewrite(erase_left_red_sibling_outer(c.model, parent) == 0); normalize(); }
            contradiction(erase_left_red_sibling_outer(c.model, parent) == 1);
        },
        Context::Left(id, above, pc, sm, um) => {
            have id == parent by { if id == parent { assumption(); } else {
                    have erase_left_red_sibling_outer(c.model, parent) == 0 by { rewrite(c.model == Context::Left(id, above, pc, sm, um)); unfold(erase_left_red_sibling_outer(Context::Left(id, above, pc, sm, um), parent)); normalize() using { not(id == parent); } }
                    have not(erase_left_red_sibling_outer(c.model, parent) == 1) by { rewrite(erase_left_red_sibling_outer(c.model, parent) == 0); normalize(); }
                    contradiction(erase_left_red_sibling_outer(c.model, parent) == 1);
                } }
            have pc == Color::Black by { if pc == Color::Black { assumption(); } else {
                    have erase_left_red_sibling_outer(c.model, parent) == 0 by { rewrite(c.model == Context::Left(id, above, pc, sm, um)); unfold(erase_left_red_sibling_outer(Context::Left(id, above, pc, sm, um), parent)); normalize() using { id == parent; not(pc == Color::Black); } }
                    have not(erase_left_red_sibling_outer(c.model, parent) == 1) by { rewrite(erase_left_red_sibling_outer(c.model, parent) == 0); normalize(); }
                    contradiction(erase_left_red_sibling_outer(c.model, parent) == 1);
                } }
            match sm { RbTree::Empty => {
                    have erase_left_red_sibling_outer(c.model, parent) == 0 by { rewrite(c.model == Context::Left(id, above, pc, sm, um)); rewrite(sm == RbTree::Empty); unfold(erase_left_red_sibling_outer(Context::Left(id, above, pc, RbTree::Empty, um), parent)); normalize() using { id == parent; pc == Color::Black; } }
                    have not(erase_left_red_sibling_outer(c.model, parent) == 1) by { rewrite(erase_left_red_sibling_outer(c.model, parent) == 0); normalize(); }
                    contradiction(erase_left_red_sibling_outer(c.model, parent) == 1);
                },
                RbTree::Node(sid, sp, sc, near_model, far_model) => {
                    have sc == Color::Red by { if sc == Color::Red { assumption(); } else {
                            have erase_left_red_sibling_outer(c.model, parent) == 0 by { rewrite(c.model == Context::Left(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, sp, sc, near_model, far_model)); unfold(erase_left_red_sibling_outer(Context::Left(id, above, pc, RbTree::Node(sid, sp, sc, near_model, far_model), um), parent)); normalize() using { id == parent; pc == Color::Black; not(sc == Color::Red); } }
                            have not(erase_left_red_sibling_outer(c.model, parent) == 1) by { rewrite(erase_left_red_sibling_outer(c.model, parent) == 0); normalize(); }
                            contradiction(erase_left_red_sibling_outer(c.model, parent) == 1);
                        } }
                    match near_model { RbTree::Empty => {
                            have erase_left_red_sibling_outer(c.model, parent) == 0 by { rewrite(c.model == Context::Left(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, sp, sc, near_model, far_model)); rewrite(near_model == RbTree::Empty); unfold(erase_left_red_sibling_outer(Context::Left(id, above, pc, RbTree::Node(sid, sp, sc, RbTree::Empty, far_model), um), parent)); normalize() using { id == parent; pc == Color::Black; sc == Color::Red; } }
                            have not(erase_left_red_sibling_outer(c.model, parent) == 1) by { rewrite(erase_left_red_sibling_outer(c.model, parent) == 0); normalize(); }
                            contradiction(erase_left_red_sibling_outer(c.model, parent) == 1);
                        },
                        RbTree::Node(nid, np, nc, nlm, nrm) => {
                            have nc == Color::Black by { if nc == Color::Black { assumption(); } else {
                                    have erase_left_red_sibling_outer(c.model, parent) == 0 by { rewrite(c.model == Context::Left(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, sp, sc, near_model, far_model)); rewrite(near_model == RbTree::Node(nid, np, nc, nlm, nrm)); unfold(erase_left_red_sibling_outer(Context::Left(id, above, pc, RbTree::Node(sid, sp, sc, RbTree::Node(nid, np, nc, nlm, nrm), far_model), um), parent)); normalize() using { id == parent; pc == Color::Black; sc == Color::Red; not(nc == Color::Black); } }
                                    have not(erase_left_red_sibling_outer(c.model, parent) == 1) by { rewrite(erase_left_red_sibling_outer(c.model, parent) == 0); normalize(); }
                                    contradiction(erase_left_red_sibling_outer(c.model, parent) == 1);
                                } }
                            have nlm == RbTree::Empty by { if nlm == RbTree::Empty { assumption(); } else {
                                    have erase_left_red_sibling_outer(c.model, parent) == 0 by { rewrite(c.model == Context::Left(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, sp, sc, near_model, far_model)); rewrite(near_model == RbTree::Node(nid, np, nc, nlm, nrm)); unfold(erase_left_red_sibling_outer(Context::Left(id, above, pc, RbTree::Node(sid, sp, sc, RbTree::Node(nid, np, nc, nlm, nrm), far_model), um), parent)); normalize() using { id == parent; pc == Color::Black; sc == Color::Red; nc == Color::Black; not(nlm == RbTree::Empty); } }
                                    have not(erase_left_red_sibling_outer(c.model, parent) == 1) by { rewrite(erase_left_red_sibling_outer(c.model, parent) == 0); normalize(); }
                                    contradiction(erase_left_red_sibling_outer(c.model, parent) == 1);
                                } }
                            match nrm { RbTree::Empty => {
                                    have erase_left_red_sibling_outer(c.model, parent) == 0 by { rewrite(c.model == Context::Left(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, sp, sc, near_model, far_model)); rewrite(near_model == RbTree::Node(nid, np, nc, nlm, nrm)); rewrite(nrm == RbTree::Empty); unfold(erase_left_red_sibling_outer(Context::Left(id, above, pc, RbTree::Node(sid, sp, sc, RbTree::Node(nid, np, nc, nlm, RbTree::Empty), far_model), um), parent)); normalize() using { id == parent; pc == Color::Black; sc == Color::Red; nc == Color::Black; nlm == RbTree::Empty; } }
                                    have not(erase_left_red_sibling_outer(c.model, parent) == 1) by { rewrite(erase_left_red_sibling_outer(c.model, parent) == 0); normalize(); }
                                    contradiction(erase_left_red_sibling_outer(c.model, parent) == 1);
                                },
                                RbTree::Node(rid, rp, rc, rlm, rrm) => {
                                    have rc == Color::Red by { if rc == Color::Red { assumption(); } else {
                                            have erase_left_red_sibling_outer(c.model, parent) == 0 by { rewrite(c.model == Context::Left(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, sp, sc, near_model, far_model)); rewrite(near_model == RbTree::Node(nid, np, nc, nlm, nrm)); rewrite(nrm == RbTree::Node(rid, rp, rc, rlm, rrm)); unfold(erase_left_red_sibling_outer(Context::Left(id, above, pc, RbTree::Node(sid, sp, sc, RbTree::Node(nid, np, nc, nlm, RbTree::Node(rid, rp, rc, rlm, rrm)), far_model), um), parent)); normalize() using { id == parent; pc == Color::Black; sc == Color::Red; nc == Color::Black; nlm == RbTree::Empty; not(rc == Color::Red); } }
                                            have not(erase_left_red_sibling_outer(c.model, parent) == 1) by { rewrite(erase_left_red_sibling_outer(c.model, parent) == 0); normalize(); }
                                            contradiction(erase_left_red_sibling_outer(c.model, parent) == 1);
                                        } }
                                    have rlm == RbTree::Empty by { if rlm == RbTree::Empty { assumption(); } else {
                                            have erase_left_red_sibling_outer(c.model, parent) == 0 by { rewrite(c.model == Context::Left(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, sp, sc, near_model, far_model)); rewrite(near_model == RbTree::Node(nid, np, nc, nlm, nrm)); rewrite(nrm == RbTree::Node(rid, rp, rc, rlm, rrm)); unfold(erase_left_red_sibling_outer(Context::Left(id, above, pc, RbTree::Node(sid, sp, sc, RbTree::Node(nid, np, nc, nlm, RbTree::Node(rid, rp, rc, rlm, rrm)), far_model), um), parent)); normalize() using { id == parent; pc == Color::Black; sc == Color::Red; nc == Color::Black; nlm == RbTree::Empty; rc == Color::Red; not(rlm == RbTree::Empty); } }
                                            have not(erase_left_red_sibling_outer(c.model, parent) == 1) by { rewrite(erase_left_red_sibling_outer(c.model, parent) == 0); normalize(); }
                                            contradiction(erase_left_red_sibling_outer(c.model, parent) == 1);
                                        } }
                                    have rrm == RbTree::Empty by { if rrm == RbTree::Empty { assumption(); } else {
                                            have erase_left_red_sibling_outer(c.model, parent) == 0 by { rewrite(c.model == Context::Left(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, sp, sc, near_model, far_model)); rewrite(near_model == RbTree::Node(nid, np, nc, nlm, nrm)); rewrite(nrm == RbTree::Node(rid, rp, rc, rlm, rrm)); unfold(erase_left_red_sibling_outer(Context::Left(id, above, pc, RbTree::Node(sid, sp, sc, RbTree::Node(nid, np, nc, nlm, RbTree::Node(rid, rp, rc, rlm, rrm)), far_model), um), parent)); normalize() using { id == parent; pc == Color::Black; sc == Color::Red; nc == Color::Black; nlm == RbTree::Empty; rc == Color::Red; rlm == RbTree::Empty; not(rrm == RbTree::Empty); } }
                                            have not(erase_left_red_sibling_outer(c.model, parent) == 1) by { rewrite(erase_left_red_sibling_outer(c.model, parent) == 0); normalize(); }
                                            contradiction(erase_left_red_sibling_outer(c.model, parent) == 1);
                                        } }
                                    apply(plug_parent_consistent_ctx(c.model, RbTree::Empty, 0));
                                    have ctx_consistent(Context::Left(id, above, pc, sm, um), RbTree::Empty, 0) == 1 by { rewrite(Context::Left(id, above, pc, sm, um) == c.model); assumption(); }
                                    apply(ctx_consistent_left_sibling(id, above, pc, sm, um, RbTree::Empty, 0));
                                    have rb_parent_consistent(RbTree::Node(sid, sp, sc, near_model, far_model), id) == 1 by { rewrite(RbTree::Node(sid, sp, sc, near_model, far_model) == sm); assumption(); }
                                    apply(rb_parent_consistent_node_fixes_parent(sid, sp, sc, near_model, far_model, id));
                                    have sp == parent by { simp(); }
                                    apply(rb_parent_consistent_node_left(sid, sp, sc, near_model, far_model, id));
                                    have rb_parent_consistent(RbTree::Node(nid, np, nc, nlm, nrm), sid) == 1 by { rewrite(RbTree::Node(nid, np, nc, nlm, nrm) == near_model); assumption(); }
                                    apply(rb_parent_consistent_node_fixes_parent(nid, np, nc, nlm, nrm, sid));
                                    have np == sid by { assumption(); }
                                    apply(rb_parent_consistent_node_right(nid, np, nc, nlm, nrm, sid));
                                    have rb_parent_consistent(RbTree::Node(rid, rp, rc, rlm, rrm), nid) == 1 by { rewrite(RbTree::Node(rid, rp, rc, rlm, rrm) == nrm); assumption(); }
                                    apply(rb_parent_consistent_node_fixes_parent(rid, rp, rc, rlm, rrm, nid));
                                    have rp == nid by { assumption(); }
                                    have c.model == Context::Left(parent, above, Color::Black, RbTree::Node(sid, parent, Color::Red, RbTree::Node(nid, sid, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty)), far_model), um) by { rewrite(c.model == Context::Left(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, sp, sc, near_model, far_model)); rewrite(near_model == RbTree::Node(nid, np, nc, nlm, nrm)); rewrite(nrm == RbTree::Node(rid, rp, rc, rlm, rrm)); rewrite(id == parent); rewrite(pc == Color::Black); rewrite(sc == Color::Red); rewrite(nc == Color::Black); rewrite(nlm == RbTree::Empty); rewrite(rc == Color::Red); rewrite(rlm == RbTree::Empty); rewrite(rrm == RbTree::Empty); rewrite(sp == parent); rewrite(np == sid); rewrite(rp == nid); normalize(); }
                                    let { sibling: s, up: u } = unfold(c);
                                    let { left: sl, right: sr } = unfold(s);
                                    let { left: nl, right: nr } = unfold(sl);
                                    let { left: rl, right: rr } = unfold(nr);
                                    unfold(nl); unfold(rl); unfold(rr);
                                    have old(c.model) == Context::Left(parent, above, Color::Black, RbTree::Node(sid, parent, Color::Red, RbTree::Node(nid, sid, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty)), far_model), um) by { rewrite(old(c.model) == Context::Left(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, sp, sc, near_model, far_model)); rewrite(near_model == RbTree::Node(nid, np, nc, nlm, nrm)); rewrite(nrm == RbTree::Node(rid, rp, rc, rlm, rrm)); rewrite(id == parent); rewrite(pc == Color::Black); rewrite(sc == Color::Red); rewrite(nc == Color::Black); rewrite(nlm == RbTree::Empty); rewrite(rc == Color::Red); rewrite(rlm == RbTree::Empty); rewrite(rrm == RbTree::Empty); rewrite(sp == parent); rewrite(np == sid); rewrite(rp == nid); normalize(); }
                                    have is_rb(RbTree::Empty) == 1 by { unfold(is_rb(RbTree::Empty)); normalize(); }
                                    have rb_root_black(RbTree::Empty) == 1 by { unfold(rb_root_black(RbTree::Empty)); normalize(); }
                                    have ctx_rb(Context::Left(parent, above, Color::Black, RbTree::Node(sid, parent, Color::Red, RbTree::Node(nid, sid, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty)), far_model), um), Nat::Succ(black_height(RbTree::Empty)), Color::Black) == 1 by { rewrite(Context::Left(parent, above, Color::Black, RbTree::Node(sid, parent, Color::Red, RbTree::Node(nid, sid, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty)), far_model), um) == old(c.model)); simp(); }
                                    have rb_parent_consistent(plug(Context::Left(parent, above, Color::Black, RbTree::Node(sid, parent, Color::Red, RbTree::Node(nid, sid, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty)), far_model), um), RbTree::Empty), 0) == 1 by { rewrite(Context::Left(parent, above, Color::Black, RbTree::Node(sid, parent, Color::Red, RbTree::Node(nid, sid, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty)), far_model), um) == old(c.model)); simp(); }
                                    apply(ctx_erase_case1_left_step(above, parent, sid, RbTree::Empty, RbTree::Node(nid, sid, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty)), far_model, um));
                                    have rb_reparent(RbTree::Node(nid, sid, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty)), parent) == RbTree::Node(nid, parent, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty)) by { unfold(rb_reparent(RbTree::Node(nid, sid, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty)), parent)); normalize(); }
                                    have ctx_rb(Context::Left(parent, sid, Color::Red, RbTree::Node(nid, parent, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty)), Context::Left(sid, above, Color::Black, far_model, um)), Nat::Succ(black_height(RbTree::Empty)), Color::Black) == 1 by { rewrite(RbTree::Node(nid, parent, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty)) == rb_reparent(RbTree::Node(nid, sid, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty)), parent)); assumption(); }
                                    have rb_parent_consistent(plug(Context::Left(parent, sid, Color::Red, RbTree::Node(nid, parent, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty)), Context::Left(sid, above, Color::Black, far_model, um)), RbTree::Empty), 0) == 1 by { rewrite(RbTree::Node(nid, parent, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty)) == rb_reparent(RbTree::Node(nid, sid, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty)), parent)); assumption(); }
                                    apply(ctx_erase_case4_left_exit(sid, parent, Color::Red, nid, rid, RbTree::Empty, RbTree::Empty, RbTree::Empty, RbTree::Empty, Context::Left(sid, above, Color::Black, far_model, um)));
                                    have rb_reparent(RbTree::Empty, parent) == RbTree::Empty by { unfold(rb_reparent(RbTree::Empty, parent)); normalize(); }
                                    have RbTree::Node(parent, nid, Color::Black, RbTree::Empty, rb_reparent(RbTree::Empty, parent)) == RbTree::Node(parent, nid, Color::Black, RbTree::Empty, RbTree::Empty) by { rewrite(rb_reparent(RbTree::Empty, parent) == RbTree::Empty); normalize(); }
                                    have plug(Context::Left(sid, above, Color::Black, far_model, um), RbTree::Node(nid, sid, Color::Red, RbTree::Node(parent, nid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(rid, nid, Color::Black, RbTree::Empty, RbTree::Empty))) == plug(um, RbTree::Node(sid, above, Color::Black, RbTree::Node(nid, sid, Color::Red, RbTree::Node(parent, nid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(rid, nid, Color::Black, RbTree::Empty, RbTree::Empty)), far_model)) by { unfold(plug(Context::Left(sid, above, Color::Black, far_model, um), RbTree::Node(nid, sid, Color::Red, RbTree::Node(parent, nid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(rid, nid, Color::Black, RbTree::Empty, RbTree::Empty)))); normalize(); }
                                    have is_rb_root(plug(um, RbTree::Node(sid, above, Color::Black, RbTree::Node(nid, sid, Color::Red, RbTree::Node(parent, nid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(rid, nid, Color::Black, RbTree::Empty, RbTree::Empty)), far_model))) == 1 by { rewrite(plug(um, RbTree::Node(sid, above, Color::Black, RbTree::Node(nid, sid, Color::Red, RbTree::Node(parent, nid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(rid, nid, Color::Black, RbTree::Empty, RbTree::Empty)), far_model)) == plug(Context::Left(sid, above, Color::Black, far_model, um), RbTree::Node(nid, sid, Color::Red, RbTree::Node(parent, nid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(rid, nid, Color::Black, RbTree::Empty, RbTree::Empty)))); rewrite(RbTree::Node(parent, nid, Color::Black, RbTree::Empty, RbTree::Empty) == RbTree::Node(parent, nid, Color::Black, RbTree::Empty, rb_reparent(RbTree::Empty, parent))); assumption(); }
                                    have rb_parent_consistent(plug(um, RbTree::Node(sid, above, Color::Black, RbTree::Node(nid, sid, Color::Red, RbTree::Node(parent, nid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(rid, nid, Color::Black, RbTree::Empty, RbTree::Empty)), far_model)), 0) == 1 by { rewrite(plug(um, RbTree::Node(sid, above, Color::Black, RbTree::Node(nid, sid, Color::Red, RbTree::Node(parent, nid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(rid, nid, Color::Black, RbTree::Empty, RbTree::Empty)), far_model)) == plug(Context::Left(sid, above, Color::Black, far_model, um), RbTree::Node(nid, sid, Color::Red, RbTree::Node(parent, nid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(rid, nid, Color::Black, RbTree::Empty, RbTree::Empty)))); rewrite(RbTree::Node(parent, nid, Color::Black, RbTree::Empty, RbTree::Empty) == RbTree::Node(parent, nid, Color::Black, RbTree::Empty, rb_reparent(RbTree::Empty, parent))); assumption(); }
                                    have rb_inorder(plug(um, RbTree::Node(sid, above, Color::Black, RbTree::Node(nid, sid, Color::Red, RbTree::Node(parent, nid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(rid, nid, Color::Black, RbTree::Empty, RbTree::Empty)), far_model))) == rb_inorder(plug(Context::Left(parent, above, Color::Black, RbTree::Node(sid, parent, Color::Red, RbTree::Node(nid, sid, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty)), far_model), um), RbTree::Empty)) by {
                                        rewrite(plug(um, RbTree::Node(sid, above, Color::Black, RbTree::Node(nid, sid, Color::Red, RbTree::Node(parent, nid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(rid, nid, Color::Black, RbTree::Empty, RbTree::Empty)), far_model)) == plug(Context::Left(sid, above, Color::Black, far_model, um), RbTree::Node(nid, sid, Color::Red, RbTree::Node(parent, nid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(rid, nid, Color::Black, RbTree::Empty, RbTree::Empty))));
                                        have rb_inorder(plug(Context::Left(sid, above, Color::Black, far_model, um), RbTree::Node(nid, sid, Color::Red, RbTree::Node(parent, nid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(rid, nid, Color::Black, RbTree::Empty, RbTree::Empty)))) == rb_inorder(plug(Context::Left(parent, sid, Color::Red, RbTree::Node(nid, parent, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty)), Context::Left(sid, above, Color::Black, far_model, um)), RbTree::Empty)) by { rewrite(RbTree::Node(parent, nid, Color::Black, RbTree::Empty, RbTree::Empty) == RbTree::Node(parent, nid, Color::Black, RbTree::Empty, rb_reparent(RbTree::Empty, parent))); assumption(); }
                                        rewrite(rb_inorder(plug(Context::Left(sid, above, Color::Black, far_model, um), RbTree::Node(nid, sid, Color::Red, RbTree::Node(parent, nid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(rid, nid, Color::Black, RbTree::Empty, RbTree::Empty)))) == rb_inorder(plug(Context::Left(parent, sid, Color::Red, RbTree::Node(nid, parent, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty)), Context::Left(sid, above, Color::Black, far_model, um)), RbTree::Empty)));
                                        rewrite(RbTree::Node(nid, parent, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty)) == rb_reparent(RbTree::Node(nid, sid, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty)), parent)); assumption();
                                    }
                                    have parent->rb_left == 0 by { simp(); }
                                    have parent->rb_right == sid by { simp(); }
                                    have sid == parent->rb_right by { simp(); }
                                    have aligned(sid, 8) by { rewrite(sid == parent->rb_right); assumption(); }
                                    have aligned(parent, 8) by { simp(); }
                                    have sid->rb_left == nid by { simp(); }
                                    have nid == sid->rb_left by { simp(); }
                                    have aligned(nid, 8) by { rewrite(nid == sid->rb_left); simp(); }
                                    have nid->rb_left == 0 by { simp(); }
                                    have nid->rb_right == rid by { simp(); }
                                    have rid == nid->rb_right by { simp(); }
                                    have rid != 0 by { rewrite(rid == nid->rb_right); assumption(); }
                                    have rid->rb_left == 0 by { simp(); }
                                    have rid->rb_right == 0 by { simp(); }
                                    have (rid->__rb_parent_color & 1) == 0 by { rewrite((rid->__rb_parent_color & 1) == color_bit(Color::Red)); unfold(color_bit(Color::Red)); normalize(); }
                                    have (sid->__rb_parent_color & 1) == 0 by { rewrite((sid->__rb_parent_color & 1) == color_bit(Color::Red)); unfold(color_bit(Color::Red)); normalize(); }
                                    have parent->__rb_parent_color == address(above) + 1 by { rewrite(parent->__rb_parent_color == address(above) + (parent->__rb_parent_color & 1)); rewrite((parent->__rb_parent_color & 1) == color_bit(Color::Black)); unfold(color_bit(Color::Black)); normalize(); }
                                    have color_bit(Color::Black) == 1 by { unfold(color_bit(Color::Black)); normalize(); }
                                    have parent->__rb_parent_color == address(above) + color_bit(Color::Black) by { rewrite(color_bit(Color::Black) == 1); assumption(); }
                                    apply(ctx_parent_word_from_color(u.model, above, parent->__rb_parent_color, Color::Black));
                                    have rb_parent_is(far_model, sid) == 1 by { rewrite(sid == parent->rb_right); assumption(); }
                                    have nid == parent->rb_right->rb_left by { normalize() using { sid == parent->rb_right; nid == sid->rb_left; } }
                                    have rid == parent->rb_right->rb_left->rb_right by { normalize() using { sid == parent->rb_right; nid == sid->rb_left; rid == nid->rb_right; } }
                                    have separate(memory(parent->__rb_parent_color), memory(parent->rb_right->rb_left->rb_left)) by { simp(); }
                                    have separate(memory(parent->__rb_parent_color), memory(parent->rb_right->rb_left->rb_right->__rb_parent_color)) by { simp(); }
                                    have separate(memory(parent->__rb_parent_color), memory(nid->rb_left)) by { transport(separate(memory(parent->__rb_parent_color), memory(parent->rb_right->rb_left->rb_left)), separate(memory(parent->__rb_parent_color), memory(nid->rb_left))) using { separate(memory(parent->__rb_parent_color), memory(parent->rb_right->rb_left->rb_left)); nid == parent->rb_right->rb_left; }; }
                                    have separate(memory(parent->__rb_parent_color), memory(rid->__rb_parent_color)) by { transport(separate(memory(parent->__rb_parent_color), memory(parent->rb_right->rb_left->rb_right->__rb_parent_color)), separate(memory(parent->__rb_parent_color), memory(rid->__rb_parent_color))) using { separate(memory(parent->__rb_parent_color), memory(parent->rb_right->rb_left->rb_right->__rb_parent_color)); rid == parent->rb_right->rb_left->rb_right; }; }
                                    mark inputs;
                                    execute_until(loop(0));
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
                                    have parent->rb_right == nid by { simp(); }
                                    have nid->__rb_parent_color == (address(parent) | 1) by { simp(); }
                                    mark first_rotation;
                                    let { after: u } = step(__rb_rotate_set_parents(parent, sibling, root, 0), { c: u });
                                    have sibling == sid by { simp(); }
                                    have tmp1 == nid by { simp(); }
                                    have sid->rb_left == parent by { normalize() using { sibling == sid; tmp1 == nid; } }
                                    have sid->rb_right == at(inputs, parent->rb_right->rb_right) by { normalize() using { at(inputs, parent->rb_right) == sid; sibling == sid; tmp1 == nid; } }
                                    have sid->__rb_parent_color == address(above) + 1 by { simp(); }
                                    have (sid->__rb_parent_color & 1) == 1 by { rewrite(sid->__rb_parent_color == address(above) + 1); arithmetic() using { aligned(above, 8); } }
                                    have sid->__rb_parent_color == address(above) + color_bit(Color::Black) by { rewrite(color_bit(Color::Black) == 1); assumption(); }
                                    have u.model == um by { simp(); }
                                    have ctx_node_is(u.model, above) == 1 by { rewrite(u.model == um); simp(); }
                                    apply(ctx_parent_word_from_color(u.model, above, sid->__rb_parent_color, Color::Black));
                                    have sr.model == far_model by { assumption(); }
                                    let rotation_ctx = fold(ctx_at(parent, root), { model: Context::Left(sid, above, Color::Black, far_model, um) }, { sibling: sr, up: u });
                                    have parent->__rb_parent_color == address(sid) by { simp(); }
                                    have parent->__rb_parent_color == address(sid) + color_bit(Color::Red) by { unfold(color_bit(Color::Red)); normalize() using { parent->__rb_parent_color == address(sid); } }
                                    have ctx_node_is(rotation_ctx.model, sid) == 1 by { rewrite(rotation_ctx.model == Context::Left(sid, above, Color::Black, far_model, um)); unfold(ctx_node_is(Context::Left(sid, above, Color::Black, far_model, um), sid)); normalize(); }
                                    apply(ctx_parent_word_from_color(rotation_ctx.model, sid, parent->__rb_parent_color, Color::Red));
                                    have nid->rb_left == 0 by { simp(); }
                                    have nid->rb_right == rid by { simp(); }
                                    have rid->__rb_parent_color == at(first_rotation, rid->__rb_parent_color) by { normalize() using { sibling == sid; tmp1 == nid; } }
                                    have (rid->__rb_parent_color & 1) == 0 by { rewrite(rid->__rb_parent_color == at(first_rotation, rid->__rb_parent_color)); simp(); }
                                    mark far_read;
                                    step();
                                    step();
                                    have sibling == nid by { simp(); }
                                    have sibling->rb_right == rid by { simp(); }
                                    step();
                                    have tmp1 == rid by { simp(); }
                                    have tmp1 != 0 by { rewrite(tmp1 == rid); assumption(); }
                                    have rid->__rb_parent_color == at(far_read, rid->__rb_parent_color) by { normalize() using { tmp1 == rid; sibling == nid; at(first_rotation, sibling) == sid; at(first_rotation, tmp1) == nid; } }
                                    have (rid->__rb_parent_color & 1) == 0 by { rewrite(rid->__rb_parent_color == at(far_read, rid->__rb_parent_color)); assumption(); }
                                    have tmp1->__rb_parent_color == rid->__rb_parent_color by { normalize() using { tmp1 == rid; } }
                                    have (tmp1->__rb_parent_color & 1) == 0 by { rewrite(tmp1->__rb_parent_color == rid->__rb_parent_color); assumption(); }
                                    step();
                                    step();
                                    step();
                                    step();
                                    step();
                                    step();
                                    have sibling == nid by { simp(); }
                                    have tmp1 == rid by { simp(); }
                                    have tmp2 == 0 by { simp(); }
                                    have parent->rb_right == 0 by { simp(); }
                                    have parent->rb_left == 0 by { simp(); }
                                    have nid->rb_left == parent by { normalize() using { sibling == nid; tmp1 == rid; } }
                                    have rid->__rb_parent_color == (address(nid) | 1) by { simp(); }
                                    step(); // The near child is empty, so skip its parent update.
                                    step();
                                    have parent->__rb_parent_color == address(sid) by { transport(at(far_read, parent->__rb_parent_color) == address(sid), parent->__rb_parent_color == address(sid)) using { at(far_read, parent->__rb_parent_color) == address(sid); sibling == nid; tmp1 == rid; separate(memory(parent->__rb_parent_color), memory(nid->rb_left)); separate(memory(parent->__rb_parent_color), memory(rid->__rb_parent_color)); separate(memory(parent->__rb_parent_color), memory(parent->rb_right)); }; }
                                    have parent->__rb_parent_color == address(sid) + color_bit(Color::Red) by { unfold(color_bit(Color::Red)); normalize() using { parent->__rb_parent_color == address(sid); } }
                                    apply(ctx_parent_word_from_color(rotation_ctx.model, sid, parent->__rb_parent_color, Color::Red));
                                    mark second_rotation;
                                    let { after: rotation_ctx } = step(__rb_rotate_set_parents(parent, sibling, root, 1), { c: rotation_ctx });
                                    step();
                                    have parent->__rb_parent_color == address(nid) + 1 by { simp(); }
                                    have (parent->__rb_parent_color & 1) == 1 by { rewrite(parent->__rb_parent_color == address(nid) + 1); arithmetic() using { aligned(nid, 8); } }
                                    have nid->__rb_parent_color == address(sid) by { simp(); }
                                    have (nid->__rb_parent_color & 1) == 0 by { rewrite(nid->__rb_parent_color == address(sid)); arithmetic() using { aligned(sid, 8); } }
                                    have rid->__rb_parent_color == at(second_rotation, rid->__rb_parent_color) by { normalize() using { sibling == nid; tmp1 == rid; } }
                                    have rid->__rb_parent_color == (address(nid) | 1) by { rewrite(rid->__rb_parent_color == at(second_rotation, rid->__rb_parent_color)); simp(); }
                                    have rid->__rb_parent_color == address(nid) + 1 by { rewrite(rid->__rb_parent_color == (address(nid) | 1)); arithmetic() using { aligned(nid, 8); } }
                                    have (rid->__rb_parent_color & 1) == 1 by { rewrite(rid->__rb_parent_color == address(nid) + 1); arithmetic() using { aligned(nid, 8); } }
                                    have parent->rb_left == 0 by { normalize() using { at(second_rotation, parent->rb_left) == 0; sibling == nid; tmp1 == rid; } }
                                    have parent->rb_right == 0 by { normalize() using { at(second_rotation, parent->rb_right) == 0; sibling == nid; tmp1 == rid; } }
                                    have rid->rb_left == 0 by { simp(); }
                                    have rid->rb_right == 0 by { simp(); }
                                    have rb_parent_is(RbTree::Empty, parent) == 1 by { unfold(rb_parent_is(RbTree::Empty, parent)); normalize(); }
                                    have rb_parent_is(RbTree::Empty, rid) == 1 by { unfold(rb_parent_is(RbTree::Empty, rid)); normalize(); }
                                    let pl = fold(rb_at(parent->rb_left), { model: RbTree::Empty });
                                    let pr = fold(rb_at(parent->rb_right), { model: RbTree::Empty });
                                    let parent_tree = fold(rb_at(parent), { model: RbTree::Node(parent, nid, Color::Black, RbTree::Empty, RbTree::Empty) }, { left: pl, right: pr });
                                    let rl = fold(rb_at(rid->rb_left), { model: RbTree::Empty });
                                    let rr = fold(rb_at(rid->rb_right), { model: RbTree::Empty });
                                    let red_tree = fold(rb_at(rid), { model: RbTree::Node(rid, nid, Color::Black, RbTree::Empty, RbTree::Empty) }, { left: rl, right: rr });
                                    apply(rb_parent_is_node_of(parent, nid, Color::Black, RbTree::Empty, RbTree::Empty));
                                    apply(rb_parent_is_node_of(rid, nid, Color::Black, RbTree::Empty, RbTree::Empty));
                                    have nid->rb_left == parent by { normalize() using { sibling == nid; tmp1 == rid; } }
                                    have nid->rb_right == rid by { simp(); }
                                    let sub = fold(rb_at(nid), { model: RbTree::Node(nid, sid, Color::Red, RbTree::Node(parent, nid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(rid, nid, Color::Black, RbTree::Empty, RbTree::Empty)) }, { left: parent_tree, right: red_tree });
                                    have rotation_ctx.model == Context::Left(sid, above, Color::Black, far_model, um) by { simp(); }
                                    have rb_tree_parent_consistent(plug(rotation_ctx.model, sub.model)) == 1 by { unfold(rb_tree_parent_consistent(plug(rotation_ctx.model, sub.model))); rewrite(rotation_ctx.model == Context::Left(sid, above, Color::Black, far_model, um)); rewrite(sub.model == RbTree::Node(nid, sid, Color::Red, RbTree::Node(parent, nid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(rid, nid, Color::Black, RbTree::Empty, RbTree::Empty))); rewrite(plug(Context::Left(sid, above, Color::Black, far_model, um), RbTree::Node(nid, sid, Color::Red, RbTree::Node(parent, nid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(rid, nid, Color::Black, RbTree::Empty, RbTree::Empty))) == plug(um, RbTree::Node(sid, above, Color::Black, RbTree::Node(nid, sid, Color::Red, RbTree::Node(parent, nid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(rid, nid, Color::Black, RbTree::Empty, RbTree::Empty)), far_model))); assumption(); }
                                    mark closing_root;
                                    let { whole: whole } = refold_to_root(nid, root, { c: rotation_ctx, t: sub });
                                    have whole.model == plug(um, RbTree::Node(sid, above, Color::Black, RbTree::Node(nid, sid, Color::Red, RbTree::Node(parent, nid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(rid, nid, Color::Black, RbTree::Empty, RbTree::Empty)), far_model)) by { rewrite(whole.model == plug(at(closing_root, rotation_ctx.model), RbTree::Node(nid, sid, Color::Red, RbTree::Node(parent, nid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(rid, nid, Color::Black, RbTree::Empty, RbTree::Empty)))); rewrite(at(closing_root, rotation_ctx.model) == Context::Left(sid, above, Color::Black, far_model, um)); rewrite(plug(Context::Left(sid, above, Color::Black, far_model, um), RbTree::Node(nid, sid, Color::Red, RbTree::Node(parent, nid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(rid, nid, Color::Black, RbTree::Empty, RbTree::Empty))) == plug(um, RbTree::Node(sid, above, Color::Black, RbTree::Node(nid, sid, Color::Red, RbTree::Node(parent, nid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(rid, nid, Color::Black, RbTree::Empty, RbTree::Empty)), far_model))); normalize(); }
                                    have whole.model == erase_left_red_sibling_outer_result(old(c.model)) by { rewrite(whole.model == plug(um, RbTree::Node(sid, above, Color::Black, RbTree::Node(nid, sid, Color::Red, RbTree::Node(parent, nid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(rid, nid, Color::Black, RbTree::Empty, RbTree::Empty)), far_model))); rewrite(old(c.model) == Context::Left(parent, above, Color::Black, RbTree::Node(sid, parent, Color::Red, RbTree::Node(nid, sid, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty)), far_model), um)); unfold(erase_left_red_sibling_outer_result(Context::Left(parent, above, Color::Black, RbTree::Node(sid, parent, Color::Red, RbTree::Node(nid, sid, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty)), far_model), um))); normalize(); }
                                    have is_rb_root(whole.model) == 1 by { rewrite(whole.model == plug(um, RbTree::Node(sid, above, Color::Black, RbTree::Node(nid, sid, Color::Red, RbTree::Node(parent, nid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(rid, nid, Color::Black, RbTree::Empty, RbTree::Empty)), far_model))); assumption(); }
                                    have rb_parent_consistent(whole.model, 0) == 1 by { rewrite(whole.model == plug(um, RbTree::Node(sid, above, Color::Black, RbTree::Node(nid, sid, Color::Red, RbTree::Node(parent, nid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(rid, nid, Color::Black, RbTree::Empty, RbTree::Empty)), far_model))); assumption(); }
                                    have rb_inorder(whole.model) == rb_inorder(plug(old(c.model), RbTree::Empty)) by { rewrite(whole.model == plug(um, RbTree::Node(sid, above, Color::Black, RbTree::Node(nid, sid, Color::Red, RbTree::Node(parent, nid, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(rid, nid, Color::Black, RbTree::Empty, RbTree::Empty)), far_model))); rewrite(old(c.model) == Context::Left(parent, above, Color::Black, RbTree::Node(sid, parent, Color::Red, RbTree::Node(nid, sid, Color::Black, RbTree::Empty, RbTree::Node(rid, nid, Color::Red, RbTree::Empty, RbTree::Empty)), far_model), um)); assumption(); }
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
