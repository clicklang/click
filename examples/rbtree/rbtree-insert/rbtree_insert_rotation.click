// Contracts for insertion's existing parent and rotation helpers.
verifying "rb_insert_color.c";
import "../rbtree-model/rbtree_resources.click";

spec enum InsertParent { To(struct rb_node*), }
resource insert_red_tag(p: struct rb_node*) {
    field link: InsertParent;
    match link { InsertParent::To(parent) => {
            owns p->__rb_parent_color;
            fact aligned(parent, 8);
            fact p->__rb_parent_color == address(parent) + (p->__rb_parent_color & 1);
            fact ((p->__rb_parent_color & ~3) as (struct rb_node*)) == parent;
            fact (p->__rb_parent_color & 1) == 0;
        }, }
}
struct rb_node* rb_red_parent(struct rb_node* red) {
    consumes before: insert_red_tag(red);
    produces after: insert_red_tag(red);
    ensures after.link == old(before.link);
    // The cast retains the C object class needed at the insertion back edge.
    ensures result == old((red->__rb_parent_color & ~3) as (struct rb_node*));
    ensures InsertParent::To(result) == old(before.link);
} by {
    match before.link {
        InsertParent::To(up) => {
            unfold(before);
            have red->__rb_parent_color == address(up) by {
                rewrite(red->__rb_parent_color, address(up) + (red->__rb_parent_color & 1));
                rewrite((red->__rb_parent_color & 1), 0);
                close();
            }
            step_until(function.exit);
            let after = fold(insert_red_tag(red), { link: InsertParent::To(up) });
        },
    }
}

resource insert_saved_tag(p: struct rb_node*, up: struct rb_node*) {
    field word: uint64;
    owns p->__rb_parent_color;
    fact p->__rb_parent_color == word;
    fact ((p->__rb_parent_color & ~3) as (struct rb_node*)) == up;
}

void __rb_change_child(struct rb_node* old, struct rb_node* new,
    struct rb_node* parent, struct rb_root* root) {
    consumes before: ctx_at(old, root);
    owns saved: insert_saved_tag(old, new);
    requires old != 0;
    requires ctx_node_is(before.model, parent) == 1;
    produces after: ctx_at(new, root);
    ensures after.model == old(before.model);
    ensures saved.word == old(saved.word);
} by {
    match before.model {
        Context::Top => {
            have parent == 0;
            unfold(before);
            step_until(function.exit);
            let after = fold(ctx_at(new, root), { model: Context::Top });
            close();
        },
        Context::Left(identity, grandparent, color, sibling_model, outer_model) => {
            have parent == identity;
            let { sibling: sibling, up: outer } = unfold(before);
            mark before_child_change;
            have separate(memory(parent->rb_left), memory(identity->__rb_parent_color)) by {
                rewrite(parent, identity);
                close();
            }
            step_until(function.exit);
            have separate(statement(0).statement(0).statement(0).footprint, memory(identity->__rb_parent_color)) by {
                close();
            }
            have identity->__rb_parent_color == at(before_child_change, identity->__rb_parent_color) by {
                preserve(memory(identity->__rb_parent_color), statement(0).statement(0).statement(0));
            }
            have identity->__rb_parent_color == address(grandparent) + (identity->__rb_parent_color & 1) by {
                rewrite(identity->__rb_parent_color, at(before_child_change, identity->__rb_parent_color));
                close();
            }
            let after = fold(ctx_at(new, root), {
                    model: Context::Left(identity, grandparent, color, sibling_model, outer_model),
                    up: outer,
                    sibling: sibling
                });
            close();
        },
        Context::Right(identity, grandparent, color, sibling_model, outer_model) => {
            have parent == identity;
            let { sibling: sibling, up: outer } = unfold(before);
            match sibling.model {
                RbTree::Empty => {
                    unfold(sibling);
                    mark before_child_change;
                    have separate(memory(parent->rb_right), memory(identity->__rb_parent_color)) by {
                        rewrite(parent, identity);
                        close();
                    }
                    step_until(function.exit);
                    have separate(statement(0).statement(0).statement(1).footprint, memory(identity->__rb_parent_color)) by {
                        close();
                    }
                    have identity->__rb_parent_color == at(before_child_change, identity->__rb_parent_color) by {
                        preserve(memory(identity->__rb_parent_color), statement(0).statement(0).statement(1));
                    }
                    have identity->__rb_parent_color == address(grandparent) + (identity->__rb_parent_color & 1) by {
                        rewrite(identity->__rb_parent_color, at(before_child_change, identity->__rb_parent_color));
                        close();
                    }

                    have separate(memory(parent->rb_right), memory(identity->rb_left)) by { rewrite(parent, identity); close(); }
                    have separate(statement(0).statement(0).statement(1).footprint, memory(identity->rb_left)) by { close(); }
                    have identity->rb_left == at(before_child_change, identity->rb_left) by { preserve(memory(identity->rb_left), statement(0).statement(0).statement(1)); }
                    let sibling = fold(rb_at(0), { model: RbTree::Empty });
                    let after = fold(ctx_at(new, root), {
                            model: Context::Right(identity, grandparent, color, sibling_model, outer_model),
                            up: outer,
                            sibling: sibling
                        });
                    close();
                },
                RbTree::Node(sid, sp, sc, sl, sr) => {
                    unfold(saved);
                    let { left: left, right: right } = unfold(sibling);
                    have separate(memory(sid->__rb_parent_color), memory(old->__rb_parent_color)) by close();
                    have sid != old by close();
                    have address(sid) != address(old);
                    let saved = fold(insert_saved_tag(old, new), { word: old->__rb_parent_color });
                    have sid == identity->rb_left by close();
                    have sid->rb_left == identity->rb_left->rb_left by { rewrite(sid, identity->rb_left); close(); }
                    have sid->rb_right == identity->rb_left->rb_right by { rewrite(sid, identity->rb_left); close(); }
                    step();
                    step();
                    let sibling = fold(rb_at(sid), {
                            model: RbTree::Node(sid, sp, sc, sl, sr),
                            left: left, right: right
                        });
                    mark before_child_change;
                    have separate(memory(parent->rb_right), memory(identity->__rb_parent_color)) by {
                        rewrite(parent, identity);
                        close();
                    }
                    step_until(function.exit);
                    have separate(statement(0).statement(0).statement(1).footprint, memory(identity->__rb_parent_color)) by {
                        close();
                    }
                    have identity->__rb_parent_color == at(before_child_change, identity->__rb_parent_color) by {
                        preserve(memory(identity->__rb_parent_color), statement(0).statement(0).statement(1));
                    }
                    have identity->__rb_parent_color == address(grandparent) + (identity->__rb_parent_color & 1) by {
                        rewrite(identity->__rb_parent_color, at(before_child_change, identity->__rb_parent_color));
                        close();
                    }

                    have separate(memory(parent->rb_right), memory(identity->rb_left)) by { rewrite(parent, identity); close(); }
                    have separate(statement(0).statement(0).statement(1).footprint, memory(identity->rb_left)) by { close(); }
                    have identity->rb_left == at(before_child_change, identity->rb_left) by { preserve(memory(identity->rb_left), statement(0).statement(0).statement(1)); }
                    let after = fold(ctx_at(new, root), {
                            model: Context::Right(identity, grandparent, color, sibling_model, outer_model),
                            up: outer,
                            sibling: sibling
                        });
                    close();
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

theorem insert_black_context_word(ctx: Context, p: struct rb_node*) {
    requires ctx_node_is(ctx, p) == 1;
    ensures ctx_parent_word(ctx, address(p) + 1) == 1 by {
            let ih = induct(ctx);
        match ctx {
            Context::Top => {
                unfold(ctx_parent_word(Context::Top, address(p) + 1));
                have p == 0 by {
                    apply(ctx_node_is_identity(Context::Top, p));
                    unfold(ctx_identity(Context::Top));
                    rewrite(p, ctx_identity(Context::Top));
                    close();
                }
                rewrite(p, 0);
                close();
            },
            Context::Left(id, up, shade, sibling, outer) => {
                have p == id by {
                    apply(ctx_node_is_identity(Context::Left(id, up, shade, sibling, outer), p));
                    unfold(ctx_identity(Context::Left(id, up, shade, sibling, outer)));
                    rewrite(p, ctx_identity(Context::Left(id, up, shade, sibling, outer)));
                    close();
                }
                rewrite(p, id);
                unfold(ctx_parent_word(Context::Left(id, up, shade, sibling, outer), address(id) + 1));
                close();
            },
            Context::Right(id, up, shade, sibling, outer) => {
                have p == id by {
                    apply(ctx_node_is_identity(Context::Right(id, up, shade, sibling, outer), p));
                    unfold(ctx_identity(Context::Right(id, up, shade, sibling, outer)));
                    rewrite(p, ctx_identity(Context::Right(id, up, shade, sibling, outer)));
                    close();
                }
                rewrite(p, id);
                unfold(ctx_parent_word(Context::Right(id, up, shade, sibling, outer), address(id) + 1));
                close();
            },
        }
    }
}

theorem aligned_parent_word_from_bit(p: void*, bit: int32) {
    requires aligned(p, 8);
    requires 0 <= bit;
    requires bit <= 1;
    ensures (address(p) | bit) == address(p) + bit by {
        if bit == 0 { rewrite(bit, 0); close(); } else {
            have 1 <= bit by { close() using { 0 <= bit; not(bit == 0); }; }
            have bit == 1 by { close() using { 1 <= bit; bit <= 1; }; }
            rewrite(bit, 1);
            have (address(p) & 7u64) == 0u64 by close();
            apply(click::integer::uint64_mask_subset(address(p), 7u64, 1u64));
            apply(click::integer::uint64_or_disjoint(address(p), 1u64));
        }
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
    requires ((old->__rb_parent_color & ~3) as (struct rb_node *)) == ctx_identity(c.model);
    produces after: ctx_at(new, root);
    ensures after.model == old(c.model);
    ensures new->__rb_parent_color == old(old->__rb_parent_color);
    ensures old->__rb_parent_color == address(new) + color;
    ensures ((new->__rb_parent_color & ~3) as (struct rb_node *)) == ctx_identity(old(c.model));
    ensures ((old->__rb_parent_color & ~3) as (struct rb_node *)) == new;
} by {
    match c.model {
        Context::Top => {
            unfold(c);
            let d = fold(ctx_at(old, root), { model: Context::Top });
            have ctx_parent_word(d.model, old->__rb_parent_color) == 1;
            have (old->__rb_parent_color & ~3) == 0 by {
                if old->__rb_parent_color == 0 {
                    rewrite(old->__rb_parent_color, 0); close();
                } else {
                    have old->__rb_parent_color == 1 by {
                        if old->__rb_parent_color == 1 { close(); } else {
                            have not(ctx_parent_word(d.model, old->__rb_parent_color) == 1) by {
                                rewrite(d.model, Context::Top);
                                unfold(ctx_parent_word(Context::Top, old->__rb_parent_color));
                                have (if old->__rb_parent_color == 1 { 1 } else { 0 }) == 0 by close();
                                have (if old->__rb_parent_color == 0 { 1 } else { if old->__rb_parent_color == 1 { 1 } else { 0 } }) == 0 by {
                                    have (if old->__rb_parent_color == 0 { 1 } else { if old->__rb_parent_color == 1 { 1 } else { 0 } }) ==
                                        (if old->__rb_parent_color == 1 { 1 } else { 0 }) by close();
                                    rewrite(if old->__rb_parent_color == 0 { 1 } else { if old->__rb_parent_color == 1 { 1 } else { 0 } },
                                            if old->__rb_parent_color == 1 { 1 } else { 0 });
                                    close();
                                }
                                rewrite(if old->__rb_parent_color == 0 { 1 } else { if old->__rb_parent_color == 1 { 1 } else { 0 } }, 0);
                                close();
                            }
                            contradiction(ctx_parent_word(d.model, old->__rb_parent_color) == 1);
                        }
                    }
                    rewrite(old->__rb_parent_color, 1); close();
                }
            }
            step(); step(); step();
            have ctx_node_is(d.model, parent) == 1;
            step(); step();
            apply(aligned_parent_word_from_bit(new, color));
            have old->__rb_parent_color == address(new) + color by {
                rewrite(old->__rb_parent_color, (address(new) | color)); close();
            }
            mark words;
            let saved = fold(insert_saved_tag(old, new), { word: old->__rb_parent_color });
            let { after: after } = step(__rb_change_child, { before: d, saved: saved });
            unfold(saved);
            step_until(function.exit);
        },
        Context::Left(id, above, pc, sibling, up) => {
            unfold(ctx_identity(Context::Left(id, above, pc, sibling, up)));
            let { sibling: s, up: u } = unfold(c);
            let d = fold(ctx_at(old, root), { model: Context::Left(id, above, pc, sibling, up), sibling: s, up: u });
            have ctx_parent_word(d.model, old->__rb_parent_color) == 1;
            have (old->__rb_parent_color & ~3) == address(id) by {
                if old->__rb_parent_color == address(id) {
                    close() using { old->__rb_parent_color == address(id); aligned(id, 8); };
                } else {
                    have old->__rb_parent_color == address(id) + 1 by {
                        if old->__rb_parent_color == address(id) + 1 { close(); } else {
                            have ctx_parent_word(d.model, old->__rb_parent_color) == 0 by {
                                rewrite(d.model, Context::Left(id, above, pc, sibling, up)); unfold(ctx_parent_word(Context::Left(id, above, pc, sibling, up), old->__rb_parent_color));
                                close() using { not(old->__rb_parent_color == address(id)); not(old->__rb_parent_color == address(id) + 1); };
                            }
                            have not(ctx_parent_word(d.model, old->__rb_parent_color) == 1) by {
                                rewrite(ctx_parent_word(d.model, old->__rb_parent_color), 0);
                                close();
                            }
                            contradiction(ctx_parent_word(d.model, old->__rb_parent_color) == 1);
                        }
                    }
                    close() using { old->__rb_parent_color == address(id) + 1; aligned(id, 8); };
                }
            }
            step(); step(); step();
            have parent == id;
            have ctx_node_is(d.model, parent) == 1 by {
                rewrite(d.model, Context::Left(id, above, pc, sibling, up));
                rewrite(parent, id);
                unfold(ctx_node_is(Context::Left(id, above, pc, sibling, up), id));
                close();
            }
            step(); step();
            apply(aligned_parent_word_from_bit(new, color));
            have old->__rb_parent_color == address(new) + color by {
                rewrite(old->__rb_parent_color, (address(new) | color)); close();
            }
            mark words;
            let saved = fold(insert_saved_tag(old, new), { word: old->__rb_parent_color });
            let { after: after } = step(__rb_change_child, { before: d, saved: saved });
            unfold(saved);
            step_until(function.exit);
        },
        Context::Right(id, above, pc, sibling, up) => {
            unfold(ctx_identity(Context::Right(id, above, pc, sibling, up)));
            let { sibling: s, up: u } = unfold(c);
            let d = fold(ctx_at(old, root), { model: Context::Right(id, above, pc, sibling, up), sibling: s, up: u });
            have ctx_parent_word(d.model, old->__rb_parent_color) == 1;
            have (old->__rb_parent_color & ~3) == address(id) by {
                if old->__rb_parent_color == address(id) {
                    close() using { old->__rb_parent_color == address(id); aligned(id, 8); };
                } else {
                    have old->__rb_parent_color == address(id) + 1 by {
                        if old->__rb_parent_color == address(id) + 1 { close(); } else {
                            have ctx_parent_word(d.model, old->__rb_parent_color) == 0 by {
                                rewrite(d.model, Context::Right(id, above, pc, sibling, up)); unfold(ctx_parent_word(Context::Right(id, above, pc, sibling, up), old->__rb_parent_color));
                                close() using { not(old->__rb_parent_color == address(id)); not(old->__rb_parent_color == address(id) + 1); };
                            }
                            have not(ctx_parent_word(d.model, old->__rb_parent_color) == 1) by {
                                rewrite(ctx_parent_word(d.model, old->__rb_parent_color), 0);
                                close();
                            }
                            contradiction(ctx_parent_word(d.model, old->__rb_parent_color) == 1);
                        }
                    }
                    close() using { old->__rb_parent_color == address(id) + 1; aligned(id, 8); };
                }
            }
            step(); step(); step();
            have parent == id;
            have ctx_node_is(d.model, parent) == 1 by {
                rewrite(d.model, Context::Right(id, above, pc, sibling, up));
                rewrite(parent, id);
                unfold(ctx_node_is(Context::Right(id, above, pc, sibling, up), id));
                close();
            }
            step(); step();
            apply(aligned_parent_word_from_bit(new, color));
            have old->__rb_parent_color == address(new) + color by {
                rewrite(old->__rb_parent_color, (address(new) | color)); close();
            }
            mark words;
            let saved = fold(insert_saved_tag(old, new), { word: old->__rb_parent_color });
            let { after: after } = step(__rb_change_child, { before: d, saved: saved });
            unfold(saved);
            step_until(function.exit);
        },
    }
}

void rb_set_parent_color(struct rb_node* rb, struct rb_node* p, int32 color) {
    owns rb->__rb_parent_color;
    requires 0 <= color;
    requires color <= 1;
    requires aligned(p, 8);
    ensures rb->__rb_parent_color == (address(p) | color);
    ensures rb->__rb_parent_color == address(p) + color;
    ensures (rb->__rb_parent_color & 1) == color;
    ensures rb->__rb_parent_color == address(p) + (rb->__rb_parent_color & 1);
    ensures ((rb->__rb_parent_color & ~3) as (struct rb_node *)) == p;
} by {
    have aligned(p, 2) by {
        close() using { aligned(p, 8); };
    }
    have aligned(p, 4) by {
        close() using { aligned(p, 8); };
    }
    step();
    have rb->__rb_parent_color == (address(p) | color) by close();
    have ((rb->__rb_parent_color & ~3) as (struct rb_node *)) == p by close();
    apply(aligned_parent_word_from_bit(p, color));
    have rb->__rb_parent_color == address(p) + color by close();
    have (rb->__rb_parent_color & 1) == color by {
        if color == 0 {
            rewrite(color, 0);
            close();
        } else {
            have color == 1 by { close() using { 0 <= color; color <= 1; not(color == 0); }; }
            rewrite(color, 1);
            close();
        }
    }
    have rb->__rb_parent_color == address(p) + (rb->__rb_parent_color & 1) by close();
    step();
}
