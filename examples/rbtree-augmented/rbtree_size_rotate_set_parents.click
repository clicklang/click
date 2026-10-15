verifying "rb_insert_augmented.c" as insert;
verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_change_child.click";

function sized_context_parent_word(ctx: SizedContext, word: uint64) -> int32 {
    match ctx {
        SizedContext::Top => if word == 0 or word == 1 { 1 } else { 0 },
        SizedContext::Left(node, parent, color, count, sibling, up) =>
            if word == address(node) or word == address(node) + 1 { 1 } else { 0 },
        SizedContext::Right(node, parent, color, count, sibling, up) =>
            if word == address(node) or word == address(node) + 1 { 1 } else { 0 },
    }
}

void insert::__rb_rotate_set_parents(struct rb_node* old, struct rb_node* new,
                             struct rb_root* root, int32 color) {
    consumes c: sized_link_at(old, root, ((struct sized_node*)(void*)old)->size);
    owns old->__rb_parent_color;
    owns ((struct sized_node*)(void*)old)->size;
    owns new->__rb_parent_color;
    requires old != 0;
    requires new != 0;
    requires aligned(new, 8);
    requires 0 <= color;
    requires color <= 1;
    requires sized_context_parent_word(c.model, old->__rb_parent_color) == 1;
    requires sized_context_parent(c.model, 0) == 0 or new != sized_context_parent(c.model, 0);
    produces after: sized_link_at(new, root, ((struct sized_node*)(void*)old)->size);
    ensures after.model == old(c.model);
    ensures ((struct sized_node*)(void*)old)->size == old(((struct sized_node*)(void*)old)->size);
    ensures new->__rb_parent_color == old(old->__rb_parent_color);
    ensures old->__rb_parent_color == address(new) + color;
} by {
    match c.model {
        SizedContext::Top => {
            let { frames: frames } = unfold(c);
            unfold(frames);
            let frames = fold(sized_context_at(old, root->rb_node, 0, ((struct sized_node*)(void*)old)->size), { model: SizedContext::Top });
            let d = fold(sized_link_at(old, root, ((struct sized_node*)(void*)old)->size), { model: SizedContext::Top }, { frames: frames });
            have sized_context_parent_word(d.model, old->__rb_parent_color) == 1 by { rewrite(d.model == SizedContext::Top); rewrite(SizedContext::Top == old(c.model)); assumption(); }
            have (old->__rb_parent_color & ~3) == 0 by {
                if old->__rb_parent_color == 0 {
                    rewrite(old->__rb_parent_color == 0); normalize();
                } else {
                    have old->__rb_parent_color == 1 by {
                        if old->__rb_parent_color == 1 { assumption(); } else {
                            have sized_context_parent_word(d.model, old->__rb_parent_color) == 0 by {
                                rewrite(d.model == SizedContext::Top); unfold(sized_context_parent_word(SizedContext::Top, old->__rb_parent_color));
                                normalize() using { not(old->__rb_parent_color == 0); not(old->__rb_parent_color == 1); }
                            }
                            have not(sized_context_parent_word(d.model, old->__rb_parent_color) == 1) by { rewrite(sized_context_parent_word(d.model, old->__rb_parent_color) == 0); normalize(); }
                            contradiction(sized_context_parent_word(d.model, old->__rb_parent_color) == 1);
                        }
                    }
                    rewrite(old->__rb_parent_color == 1); normalize();
                }
            }
            step(); step();
            have parent == 0;
            have parent == sized_context_parent(d.model, 0) by { rewrite(d.model == SizedContext::Top); unfold(sized_context_parent(SizedContext::Top, 0)); normalize(); }
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
            have parent == 0 or new != parent by {
                rewrite(parent == sized_context_parent(d.model, 0));
                rewrite(d.model == old(c.model)); assumption();
            }
            mark words;
            have at(words, old->__rb_parent_color) == address(new) + color by assumption();
            let { after: after } = step(insert::__rb_change_child(old, new, parent, root), { before: d });
            have old->__rb_parent_color == address(new) + color by {
                have old->__rb_parent_color == at(words, old->__rb_parent_color);
                rewrite(old->__rb_parent_color == at(words, old->__rb_parent_color)); assumption();
            }
            execute(); simp();
        },
        SizedContext::Left(id, above, pc, count, sibling, up) => {
            let { frames: frames } = unfold(c);
            let { metadata: metadata, sibling: s, up: u } = unfold(frames);
            let frames = fold(sized_context_at(old, root->rb_node, 0, ((struct sized_node*)(void*)old)->size), { model: SizedContext::Left(id, above, pc, count, sibling, up) }, { metadata: metadata, sibling: s, up: u });
            let d = fold(sized_link_at(old, root, ((struct sized_node*)(void*)old)->size), { model: SizedContext::Left(id, above, pc, count, sibling, up) }, { frames: frames });
            have sized_context_parent_word(d.model, old->__rb_parent_color) == 1 by { rewrite(d.model == SizedContext::Left(id, above, pc, count, sibling, up)); rewrite(SizedContext::Left(id, above, pc, count, sibling, up) == old(c.model)); assumption(); }
            have (old->__rb_parent_color & ~3) == address(id) by {
                if old->__rb_parent_color == address(id) {
                    arithmetic() using { old->__rb_parent_color == address(id); aligned(id, 8); }
                } else {
                    have old->__rb_parent_color == address(id) + 1 by {
                        if old->__rb_parent_color == address(id) + 1 { assumption(); } else {
                            have sized_context_parent_word(d.model, old->__rb_parent_color) == 0 by {
                                rewrite(d.model == SizedContext::Left(id, above, pc, count, sibling, up)); unfold(sized_context_parent_word(SizedContext::Left(id, above, pc, count, sibling, up), old->__rb_parent_color));
                                normalize() using { not(old->__rb_parent_color == address(id)); not(old->__rb_parent_color == address(id) + 1); }
                            }
                            have not(sized_context_parent_word(d.model, old->__rb_parent_color) == 1) by { rewrite(sized_context_parent_word(d.model, old->__rb_parent_color) == 0); normalize(); }
                            contradiction(sized_context_parent_word(d.model, old->__rb_parent_color) == 1);
                        }
                    }
                    arithmetic() using { old->__rb_parent_color == address(id) + 1; aligned(id, 8); }
                }
            }
            step(); step();
            have parent == id;
            have parent == sized_context_parent(d.model, 0) by { rewrite(d.model == SizedContext::Left(id, above, pc, count, sibling, up)); unfold(sized_context_parent(SizedContext::Left(id, above, pc, count, sibling, up), 0)); normalize(); }
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
            have parent == 0 or new != parent by {
                rewrite(parent == sized_context_parent(d.model, 0));
                rewrite(d.model == old(c.model)); assumption();
            }
            mark words;
            have at(words, old->__rb_parent_color) == address(new) + color by assumption();
            let { after: after } = step(insert::__rb_change_child(old, new, parent, root), { before: d });
            have old->__rb_parent_color == address(new) + color by {
                have old->__rb_parent_color == at(words, old->__rb_parent_color);
                rewrite(old->__rb_parent_color == at(words, old->__rb_parent_color)); assumption();
            }
            execute(); simp();
        },
        SizedContext::Right(id, above, pc, count, sibling, up) => {
            let { frames: frames } = unfold(c);
            let { metadata: metadata, sibling: s, up: u } = unfold(frames);
            let frames = fold(sized_context_at(old, root->rb_node, 0, ((struct sized_node*)(void*)old)->size), { model: SizedContext::Right(id, above, pc, count, sibling, up) }, { metadata: metadata, sibling: s, up: u });
            let d = fold(sized_link_at(old, root, ((struct sized_node*)(void*)old)->size), { model: SizedContext::Right(id, above, pc, count, sibling, up) }, { frames: frames });
            have sized_context_parent_word(d.model, old->__rb_parent_color) == 1 by { rewrite(d.model == SizedContext::Right(id, above, pc, count, sibling, up)); rewrite(SizedContext::Right(id, above, pc, count, sibling, up) == old(c.model)); assumption(); }
            have (old->__rb_parent_color & ~3) == address(id) by {
                if old->__rb_parent_color == address(id) {
                    arithmetic() using { old->__rb_parent_color == address(id); aligned(id, 8); }
                } else {
                    have old->__rb_parent_color == address(id) + 1 by {
                        if old->__rb_parent_color == address(id) + 1 { assumption(); } else {
                            have sized_context_parent_word(d.model, old->__rb_parent_color) == 0 by {
                                rewrite(d.model == SizedContext::Right(id, above, pc, count, sibling, up)); unfold(sized_context_parent_word(SizedContext::Right(id, above, pc, count, sibling, up), old->__rb_parent_color));
                                normalize() using { not(old->__rb_parent_color == address(id)); not(old->__rb_parent_color == address(id) + 1); }
                            }
                            have not(sized_context_parent_word(d.model, old->__rb_parent_color) == 1) by { rewrite(sized_context_parent_word(d.model, old->__rb_parent_color) == 0); normalize(); }
                            contradiction(sized_context_parent_word(d.model, old->__rb_parent_color) == 1);
                        }
                    }
                    arithmetic() using { old->__rb_parent_color == address(id) + 1; aligned(id, 8); }
                }
            }
            step(); step();
            have parent == id;
            have parent == sized_context_parent(d.model, 0) by { rewrite(d.model == SizedContext::Right(id, above, pc, count, sibling, up)); unfold(sized_context_parent(SizedContext::Right(id, above, pc, count, sibling, up), 0)); normalize(); }
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
            have parent == 0 or new != parent by {
                rewrite(parent == sized_context_parent(d.model, 0));
                rewrite(d.model == old(c.model)); assumption();
            }
            mark words;
            have at(words, old->__rb_parent_color) == address(new) + color by assumption();
            let { after: after } = step(insert::__rb_change_child(old, new, parent, root), { before: d });
            have old->__rb_parent_color == address(new) + color by {
                have old->__rb_parent_color == at(words, old->__rb_parent_color);
                rewrite(old->__rb_parent_color == at(words, old->__rb_parent_color)); assumption();
            }
            execute(); simp();
        },
    }
}
