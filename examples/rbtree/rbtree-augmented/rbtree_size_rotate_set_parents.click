import click::separation;
verifying "rb_insert_augmented.c" as insert;
verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_link_distinct.click";

function sized_context_parent_word(ctx: SizedContext, word: uint64) -> int32 {
    match ctx {
        SizedContext::Top => if word == 0 or word == 1 { 1 } else { 0 },
        SizedContext::Left(node, parent, color, count, sibling, up) =>
            if word == address(node) or word == address(node) + 1 { 1 } else { 0 },
        SizedContext::Right(node, parent, color, count, sibling, up) =>
            if word == address(node) or word == address(node) + 1 { 1 } else { 0 },
    }
}

theorem sized_context_parent_word_black(ctx: SizedContext, parent: struct rb_node*, word: uint64) {
    requires parent == sized_context_parent(ctx, 0);
    requires word == address(parent) + 1;
    ensures sized_context_parent_word(ctx, word) == 1 by {
        match ctx {
            SizedContext::Top => {
                have parent == 0 by {
                    rewrite(parent, sized_context_parent(ctx, 0));
                    rewrite(ctx, SizedContext::Top);
                    unfold(sized_context_parent(SizedContext::Top, 0)); close();
                }
                have word == address(0) + 1 by {
                    rewrite(word, address(parent) + 1);
                    rewrite(parent, 0); close();
                }
                rewrite(ctx, SizedContext::Top);
                unfold(sized_context_parent_word(SizedContext::Top, word));
                normalize() using { word == address(0) + 1; };
            },
            SizedContext::Left(a, ancestor, color, count, sibling, up) => {
                have parent == a by {
                    rewrite(parent, sized_context_parent(ctx, 0));
                    rewrite(ctx, SizedContext::Left(a, ancestor, color, count, sibling, up));
                    unfold(sized_context_parent(SizedContext::Left(a, ancestor, color, count, sibling, up), 0)); close();
                }
                have word == address(a) + 1 by {
                    rewrite(a, parent); close();
                }
                rewrite(ctx, SizedContext::Left(a, ancestor, color, count, sibling, up));
                unfold(sized_context_parent_word(SizedContext::Left(a, ancestor, color, count, sibling, up), word));
                normalize() using { word == address(a) + 1; };
            },
            SizedContext::Right(a, ancestor, color, count, sibling, up) => {
                have parent == a by {
                    rewrite(parent, sized_context_parent(ctx, 0));
                    rewrite(ctx, SizedContext::Right(a, ancestor, color, count, sibling, up));
                    unfold(sized_context_parent(SizedContext::Right(a, ancestor, color, count, sibling, up), 0)); close();
                }
                have word == address(a) + 1 by {
                    rewrite(a, parent); close();
                }
                rewrite(ctx, SizedContext::Right(a, ancestor, color, count, sibling, up));
                unfold(sized_context_parent_word(SizedContext::Right(a, ancestor, color, count, sibling, up), word));
                normalize() using { word == address(a) + 1; };
            },
        }
    }
}

// Keep the complete copied parent pointer across the ancestor-link update.
resource sized_copied_parent_tag(p: struct rb_node*, up: struct rb_node*) {
    field word: uint64;
    owns p->__rb_parent_color;
    fact p->__rb_parent_color == word;
    fact ((p->__rb_parent_color & ~3) as (struct rb_node*)) == up;
}

void insert::__rb_rotate_set_parents(struct rb_node* old, struct rb_node* new,
                             struct rb_root* root, int32 color) {
    consumes c: sized_link_at(old, root, (old as (uint8 *) as (struct sized_node *))->size);
    owns old->__rb_parent_color;
    owns (old as (uint8 *) as (struct sized_node *))->size;
    owns new->__rb_parent_color;
    requires old != 0;
    requires new != 0;
    requires aligned(new, 8);
    requires 0 <= color;
    requires color <= 1;
    requires sized_context_parent_word(c.model, old->__rb_parent_color) == 1;
    // The numeric word relation does not establish the parent provenance.
    requires ((old->__rb_parent_color & ~3) as (struct rb_node *))
        == sized_context_parent(c.model, 0);
    produces after: sized_link_at(new, root, old((old as (uint8 *) as (struct sized_node *))->size));
    ensures after.model == old(c.model);
    ensures (old as (uint8 *) as (struct sized_node *))->size == old((old as (uint8 *) as (struct sized_node *))->size);
    ensures new->__rb_parent_color == old(old->__rb_parent_color);
    ensures ((new->__rb_parent_color & ~3) as (struct rb_node *))
        == sized_context_parent(old(c.model), 0);
    ensures old->__rb_parent_color == address(new) + color;
    ensures ((old->__rb_parent_color & ~3) as (struct rb_node *)) == new;
} by {
    sized_link_replacement_distinct(old, new, root,
        (old as (uint8 *) as (struct sized_node *))->size, { link: c });
    have sized_context_parent(old(c.model), 0) == 0 or new != sized_context_parent(old(c.model), 0) by {
        rewrite(old(c.model), c.model); close();
    }
    match c.model {
        SizedContext::Top => {
            let { frames: frames } = unfold(c);
            unfold(frames);
            let frames = fold(sized_context_at(old, root->rb_node, 0, (old as (uint8 *) as (struct sized_node *))->size), { model: SizedContext::Top });
            let d = fold(sized_link_at(old, root, (old as (uint8 *) as (struct sized_node *))->size), { model: SizedContext::Top, frames: frames });
            have sized_context_parent_word(d.model, old->__rb_parent_color) == 1 by { rewrite(d.model, SizedContext::Top); rewrite(SizedContext::Top, old(c.model)); close(); }
            have (old->__rb_parent_color & ~3) == 0 by {
                if old->__rb_parent_color == 0 {
                    rewrite(old->__rb_parent_color, 0); close();
                } else {
                    have old->__rb_parent_color == 1 by {
                        if old->__rb_parent_color == 1 { close(); } else {
                            have sized_context_parent_word(d.model, old->__rb_parent_color) == 0 by {
                                rewrite(d.model, SizedContext::Top); unfold(sized_context_parent_word(SizedContext::Top, old->__rb_parent_color));
                                close() using { not(old->__rb_parent_color == 0); not(old->__rb_parent_color == 1); };
                            }
                            have not(sized_context_parent_word(d.model, old->__rb_parent_color) == 1) by { rewrite(sized_context_parent_word(d.model, old->__rb_parent_color), 0); close(); }
                            contradiction(sized_context_parent_word(d.model, old->__rb_parent_color) == 1);
                        }
                    }
                    rewrite(old->__rb_parent_color, 1); close();
                }
            }
            mark s0; step();
            have (old as (uint8 *) as (struct sized_node *))->size == at(s0, (old as (uint8 *) as (struct sized_node *))->size) by close();
            mark s1; step();
            have (old as (uint8 *) as (struct sized_node *))->size == at(s1, (old as (uint8 *) as (struct sized_node *))->size) by close();
            step(); // Assign the decoded parent before reading the C local.
            have parent == 0;
            have parent == sized_context_parent(d.model, 0) by { rewrite(d.model, SizedContext::Top); unfold(sized_context_parent(SizedContext::Top, 0)); close(); }
            mark s2; step();
            have separate(memory((&((old as (uint8 *) as (struct sized_node *))->size))[0..1]), memory(new->__rb_parent_color)) by { close(); }
            have separate(statement(1).footprint, memory((&((old as (uint8 *) as (struct sized_node *))->size))[0..1])) by {
                close() using { separate(memory((&((old as (uint8 *) as (struct sized_node *))->size))[0..1]), memory(new->__rb_parent_color)); };
            }
            have (old as (uint8 *) as (struct sized_node *))->size == at(s2, (old as (uint8 *) as (struct sized_node *))->size) by {
                preserve(memory((&((old as (uint8 *) as (struct sized_node *))->size))[0..1]), statement(1));
            }
            mark s3; step();
            have (old as (uint8 *) as (struct sized_node *))->size == at(s3, (old as (uint8 *) as (struct sized_node *))->size) by close();
            have old->__rb_parent_color == (address(new) | color);
            have old->__rb_parent_color == address(new) + color by {
                rewrite(old->__rb_parent_color, (address(new) | color));
                if color == 0 { rewrite(color, 0); close(); } else {
                    have color == 1 by { close() using { 0 <= color; color <= 1; not(color == 0); }; }
                    rewrite(color, 1);
                    close() using { aligned(new, 8); };
                }
            }
            have parent == 0 or new != parent by {
                rewrite(parent, sized_context_parent(d.model, 0));
                rewrite(d.model, old(c.model)); close();
            }
            have separate(d, memory(new->__rb_parent_color)) by { close(); }
            have separate(memory(old->__rb_parent_color), memory(new->__rb_parent_color)) by { close(); }
            have separate(memory((old as (uint8 *) as (struct sized_node *))->size), memory(new->__rb_parent_color)) by { close(); }
            mark words;
            have at(words, new->__rb_parent_color) == old(old->__rb_parent_color) by close();
            have at(words, old->__rb_parent_color) == address(new) + color by close();
            have parent == sized_context_parent(old(c.model), 0) by close();
            have ((new->__rb_parent_color & ~3) as (struct rb_node*)) == parent by close();
            let copied_tag = fold(sized_copied_parent_tag(new, parent), { word: new->__rb_parent_color });
            let { after: after } = step(insert::__rb_change_child, { before: d });
            unfold(copied_tag);
            have old->__rb_parent_color == address(new) + color by {
                have old->__rb_parent_color == at(words, old->__rb_parent_color);
                rewrite(old->__rb_parent_color, at(words, old->__rb_parent_color)); close();
            }
            have new->__rb_parent_color == old(old->__rb_parent_color) by close();
            have ((new->__rb_parent_color & ~3) as (struct rb_node*)) == sized_context_parent(old(c.model), 0) by close();
            step_until(function.exit);
        },
        SizedContext::Left(id, above, pc, count, sibling, up) => {
            have ((old->__rb_parent_color & ~3) as (struct rb_node *)) == id by {
                rewrite(((old->__rb_parent_color & ~3) as (struct rb_node *)), sized_context_parent(c.model, 0));
                rewrite(c.model, SizedContext::Left(id, above, pc, count, sibling, up));
                unfold(sized_context_parent(SizedContext::Left(id, above, pc, count, sibling, up), 0));
                close();
            }
            let { frames: frames } = unfold(c);
            let { metadata: metadata, sibling: s, up: u } = unfold(frames);
            let frames = fold(sized_context_at(old, root->rb_node, 0, (old as (uint8 *) as (struct sized_node *))->size), { model: SizedContext::Left(id, above, pc, count, sibling, up), metadata: metadata, sibling: s, up: u });
            let d = fold(sized_link_at(old, root, (old as (uint8 *) as (struct sized_node *))->size), { model: SizedContext::Left(id, above, pc, count, sibling, up), frames: frames });
            have sized_context_parent_word(d.model, old->__rb_parent_color) == 1 by { rewrite(d.model, SizedContext::Left(id, above, pc, count, sibling, up)); rewrite(SizedContext::Left(id, above, pc, count, sibling, up), old(c.model)); close(); }
            have (old->__rb_parent_color & ~3) == address(id) by {
                if old->__rb_parent_color == address(id) {
                    close() using { old->__rb_parent_color == address(id); aligned(id, 8); };
                } else {
                    have old->__rb_parent_color == address(id) + 1 by {
                        if old->__rb_parent_color == address(id) + 1 { close(); } else {
                            have sized_context_parent_word(d.model, old->__rb_parent_color) == 0 by {
                                rewrite(d.model, SizedContext::Left(id, above, pc, count, sibling, up)); unfold(sized_context_parent_word(SizedContext::Left(id, above, pc, count, sibling, up), old->__rb_parent_color));
                                close() using { not(old->__rb_parent_color == address(id)); not(old->__rb_parent_color == address(id) + 1); };
                            }
                            have not(sized_context_parent_word(d.model, old->__rb_parent_color) == 1) by { rewrite(sized_context_parent_word(d.model, old->__rb_parent_color), 0); close(); }
                            contradiction(sized_context_parent_word(d.model, old->__rb_parent_color) == 1);
                        }
                    }
                    close() using { old->__rb_parent_color == address(id) + 1; aligned(id, 8); };
                }
            }
            mark s0; step();
            have (old as (uint8 *) as (struct sized_node *))->size == at(s0, (old as (uint8 *) as (struct sized_node *))->size) by close();
            mark s1; step();
            have (old as (uint8 *) as (struct sized_node *))->size == at(s1, (old as (uint8 *) as (struct sized_node *))->size) by close();
            step(); // Assign the decoded parent before reading the C local.
            have parent == id;
            have parent == sized_context_parent(d.model, 0) by { rewrite(d.model, SizedContext::Left(id, above, pc, count, sibling, up)); unfold(sized_context_parent(SizedContext::Left(id, above, pc, count, sibling, up), 0)); close(); }
            mark s2; step();
            have separate(memory((&((old as (uint8 *) as (struct sized_node *))->size))[0..1]), memory(new->__rb_parent_color)) by { close(); }
            have separate(statement(1).footprint, memory((&((old as (uint8 *) as (struct sized_node *))->size))[0..1])) by {
                close() using { separate(memory((&((old as (uint8 *) as (struct sized_node *))->size))[0..1]), memory(new->__rb_parent_color)); };
            }
            have (old as (uint8 *) as (struct sized_node *))->size == at(s2, (old as (uint8 *) as (struct sized_node *))->size) by {
                preserve(memory((&((old as (uint8 *) as (struct sized_node *))->size))[0..1]), statement(1));
            }
            mark s3; step();
            have (old as (uint8 *) as (struct sized_node *))->size == at(s3, (old as (uint8 *) as (struct sized_node *))->size) by close();
            have old->__rb_parent_color == (address(new) | color);
            have old->__rb_parent_color == address(new) + color by {
                rewrite(old->__rb_parent_color, (address(new) | color));
                if color == 0 { rewrite(color, 0); close(); } else {
                    have color == 1 by { close() using { 0 <= color; color <= 1; not(color == 0); }; }
                    rewrite(color, 1);
                    close() using { aligned(new, 8); };
                }
            }
            have parent == 0 or new != parent by {
                rewrite(parent, sized_context_parent(d.model, 0));
                rewrite(d.model, old(c.model)); close();
            }
            have separate(d, memory(new->__rb_parent_color)) by { close(); }
            have separate(memory(old->__rb_parent_color), memory(new->__rb_parent_color)) by { close(); }
            have separate(memory((old as (uint8 *) as (struct sized_node *))->size), memory(new->__rb_parent_color)) by { close(); }
            mark words;
            have at(words, new->__rb_parent_color) == old(old->__rb_parent_color) by close();
            have at(words, old->__rb_parent_color) == address(new) + color by close();
            have parent == sized_context_parent(old(c.model), 0) by close();
            have ((new->__rb_parent_color & ~3) as (struct rb_node*)) == parent by close();
            let copied_tag = fold(sized_copied_parent_tag(new, parent), { word: new->__rb_parent_color });
            let { after: after } = step(insert::__rb_change_child, { before: d });
            unfold(copied_tag);
            have old->__rb_parent_color == address(new) + color by {
                have old->__rb_parent_color == at(words, old->__rb_parent_color);
                rewrite(old->__rb_parent_color, at(words, old->__rb_parent_color)); close();
            }
            have new->__rb_parent_color == old(old->__rb_parent_color) by close();
            have ((new->__rb_parent_color & ~3) as (struct rb_node*)) == sized_context_parent(old(c.model), 0) by close();
            step_until(function.exit);
        },
        SizedContext::Right(id, above, pc, count, sibling, up) => {
            have ((old->__rb_parent_color & ~3) as (struct rb_node *)) == id by {
                rewrite(((old->__rb_parent_color & ~3) as (struct rb_node *)), sized_context_parent(c.model, 0));
                rewrite(c.model, SizedContext::Right(id, above, pc, count, sibling, up));
                unfold(sized_context_parent(SizedContext::Right(id, above, pc, count, sibling, up), 0));
                close();
            }
            let { frames: frames } = unfold(c);
            let { metadata: metadata, sibling: s, up: u } = unfold(frames);
            let frames = fold(sized_context_at(old, root->rb_node, 0, (old as (uint8 *) as (struct sized_node *))->size), { model: SizedContext::Right(id, above, pc, count, sibling, up), metadata: metadata, sibling: s, up: u });
            let d = fold(sized_link_at(old, root, (old as (uint8 *) as (struct sized_node *))->size), { model: SizedContext::Right(id, above, pc, count, sibling, up), frames: frames });
            have sized_context_parent_word(d.model, old->__rb_parent_color) == 1 by { rewrite(d.model, SizedContext::Right(id, above, pc, count, sibling, up)); rewrite(SizedContext::Right(id, above, pc, count, sibling, up), old(c.model)); close(); }
            have (old->__rb_parent_color & ~3) == address(id) by {
                if old->__rb_parent_color == address(id) {
                    close() using { old->__rb_parent_color == address(id); aligned(id, 8); };
                } else {
                    have old->__rb_parent_color == address(id) + 1 by {
                        if old->__rb_parent_color == address(id) + 1 { close(); } else {
                            have sized_context_parent_word(d.model, old->__rb_parent_color) == 0 by {
                                rewrite(d.model, SizedContext::Right(id, above, pc, count, sibling, up)); unfold(sized_context_parent_word(SizedContext::Right(id, above, pc, count, sibling, up), old->__rb_parent_color));
                                close() using { not(old->__rb_parent_color == address(id)); not(old->__rb_parent_color == address(id) + 1); };
                            }
                            have not(sized_context_parent_word(d.model, old->__rb_parent_color) == 1) by { rewrite(sized_context_parent_word(d.model, old->__rb_parent_color), 0); close(); }
                            contradiction(sized_context_parent_word(d.model, old->__rb_parent_color) == 1);
                        }
                    }
                    close() using { old->__rb_parent_color == address(id) + 1; aligned(id, 8); };
                }
            }
            mark s0; step();
            have (old as (uint8 *) as (struct sized_node *))->size == at(s0, (old as (uint8 *) as (struct sized_node *))->size) by close();
            mark s1; step();
            have (old as (uint8 *) as (struct sized_node *))->size == at(s1, (old as (uint8 *) as (struct sized_node *))->size) by close();
            step(); // Assign the decoded parent before reading the C local.
            have parent == id;
            have parent == sized_context_parent(d.model, 0) by { rewrite(d.model, SizedContext::Right(id, above, pc, count, sibling, up)); unfold(sized_context_parent(SizedContext::Right(id, above, pc, count, sibling, up), 0)); close(); }
            mark s2; step();
            have separate(memory((&((old as (uint8 *) as (struct sized_node *))->size))[0..1]), memory(new->__rb_parent_color)) by { close(); }
            have separate(statement(1).footprint, memory((&((old as (uint8 *) as (struct sized_node *))->size))[0..1])) by {
                close() using { separate(memory((&((old as (uint8 *) as (struct sized_node *))->size))[0..1]), memory(new->__rb_parent_color)); };
            }
            have (old as (uint8 *) as (struct sized_node *))->size == at(s2, (old as (uint8 *) as (struct sized_node *))->size) by {
                preserve(memory((&((old as (uint8 *) as (struct sized_node *))->size))[0..1]), statement(1));
            }
            mark s3; step();
            have (old as (uint8 *) as (struct sized_node *))->size == at(s3, (old as (uint8 *) as (struct sized_node *))->size) by close();
            have old->__rb_parent_color == (address(new) | color);
            have old->__rb_parent_color == address(new) + color by {
                rewrite(old->__rb_parent_color, (address(new) | color));
                if color == 0 { rewrite(color, 0); close(); } else {
                    have color == 1 by { close() using { 0 <= color; color <= 1; not(color == 0); }; }
                    rewrite(color, 1);
                    close() using { aligned(new, 8); };
                }
            }
            have parent == 0 or new != parent by {
                rewrite(parent, sized_context_parent(d.model, 0));
                rewrite(d.model, old(c.model)); close();
            }
            have separate(d, memory(new->__rb_parent_color)) by { close(); }
            have separate(memory(old->__rb_parent_color), memory(new->__rb_parent_color)) by { close(); }
            have separate(memory((old as (uint8 *) as (struct sized_node *))->size), memory(new->__rb_parent_color)) by { close(); }
            mark words;
            have at(words, new->__rb_parent_color) == old(old->__rb_parent_color) by close();
            have at(words, old->__rb_parent_color) == address(new) + color by close();
            have parent == sized_context_parent(old(c.model), 0) by close();
            have ((new->__rb_parent_color & ~3) as (struct rb_node*)) == parent by close();
            let copied_tag = fold(sized_copied_parent_tag(new, parent), { word: new->__rb_parent_color });
            let { after: after } = step(insert::__rb_change_child, { before: d });
            unfold(copied_tag);
            have old->__rb_parent_color == address(new) + color by {
                have old->__rb_parent_color == at(words, old->__rb_parent_color);
                rewrite(old->__rb_parent_color, at(words, old->__rb_parent_color)); close();
            }
            have new->__rb_parent_color == old(old->__rb_parent_color) by close();
            have ((new->__rb_parent_color & ~3) as (struct rb_node*)) == sized_context_parent(old(c.model), 0) by close();
            step_until(function.exit);
        },
    }
}
