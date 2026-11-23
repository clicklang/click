// The caller lends the root object or the parent node. The zero-length range
// leaves the other object with the caller.
verifying "rb_erase_augmented.c";
import "../rbtree-model/rbtree_resources.click";

resource erase_change_links(focus: struct rb_node*, parent: struct rb_node*, root: struct rb_root*) {
    field model: Context;
    field sibling_ptr: int32*;
    field root_count: int32;
    field parent_count: int32;
    field tag: uint64;
    field above: int32*;
    owns root[0..root_count];
    owns parent[0..parent_count];
}

function erase_context_is_right(model: Context) -> int32 {
    match model {
        Context::Top => 0,
        Context::Left(identity, grandparent, color, sibling_model, outer_model) => 0,
        Context::Right(identity, grandparent, color, sibling_model, outer_model) => 1,
    }
}

void __rb_change_child(struct rb_node* old, struct rb_node* new,
                       struct rb_node* parent, struct rb_root* root) {
    consumes links: erase_change_links(old, parent, root);
    requires links.model == Context::Top implies parent == 0 and links.root_count == 1 and links.parent_count == 0;
    requires links.model != Context::Top implies parent != 0 and links.root_count == 0 and links.parent_count == 1;

    requires links.model == Context::Top implies root->rb_node == old;
    requires links.model != Context::Top and erase_context_is_right(links.model) == 0
        implies parent->rb_left == old and parent->rb_right == links.sibling_ptr;
    requires erase_context_is_right(links.model) == 1
        implies parent->rb_right == old and parent->rb_left == links.sibling_ptr;
    requires erase_context_is_right(links.model) == 1
        implies address(links.sibling_ptr) != address(old);
    requires parent != 0 implies parent->__rb_parent_color == links.tag
        and ((parent->__rb_parent_color & ~3) as (struct rb_node*)) == links.above;
    produces updated: erase_change_links(new, parent, root);
    ensures updated.model == Context::Top implies root->rb_node == new;
    ensures updated.model != Context::Top and erase_context_is_right(updated.model) == 0
        implies parent->rb_left == new and parent->rb_right == updated.sibling_ptr;
    ensures erase_context_is_right(updated.model) == 1
        implies parent->rb_right == new and parent->rb_left == updated.sibling_ptr;
    ensures updated.model == old(links.model);
    ensures updated.sibling_ptr == old(links.sibling_ptr);
    ensures updated.root_count == old(links.root_count);
    ensures updated.parent_count == old(links.parent_count);
    ensures updated.model == Context::Top implies parent == 0 and updated.root_count == 1 and updated.parent_count == 0;
    ensures updated.model != Context::Top implies parent != 0 and updated.root_count == 0 and updated.parent_count == 1;
    ensures updated.tag == old(links.tag);
    ensures updated.above == old(links.above);
    ensures parent != 0 implies parent->__rb_parent_color == updated.tag
        and ((parent->__rb_parent_color & ~3) as (struct rb_node*)) == updated.above;
} by {
    match links.model {
        Context::Top => {
            apply(links.model == Context::Top implies parent == 0 and links.root_count == 1 and links.parent_count == 0);
            have links.root_count == 1 by known();
            have links.parent_count == 0 by known();
            unfold(links);
            step_until(function.exit);
            have root->rb_node == new by known();
            let updated = fold(erase_change_links(new, parent, root), {
                model: Context::Top, sibling_ptr: old(links.sibling_ptr), root_count: old(links.root_count), parent_count: old(links.parent_count),
                tag: old(links.tag), above: old(links.above)
            });
            solve();
        },
        Context::Left(identity, grandparent, color, sibling_model, outer_model) => {
            have links.model != Context::Top by {
                rewrite(links.model, Context::Left(identity, grandparent, color, sibling_model, outer_model)); known();
            }
            apply(links.model != Context::Top implies parent != 0 and links.root_count == 0 and links.parent_count == 1);
            have links.root_count == 0 by known();
            have links.parent_count == 1 by known();
            have erase_context_is_right(links.model) == 0 by {
                rewrite(links.model, Context::Left(identity, grandparent, color, sibling_model, outer_model));
                unfold(erase_context_is_right(Context::Left(identity, grandparent, color, sibling_model, outer_model)));
                known();
            }
            have links.model != Context::Top and erase_context_is_right(links.model) == 0 by known();
            apply(links.model != Context::Top and erase_context_is_right(links.model) == 0
                implies parent->rb_left == old and parent->rb_right == links.sibling_ptr);
            unfold(links);
            step_until(function.exit);
            have parent->rb_left == new by known();
            let updated = fold(erase_change_links(new, parent, root), {
                model: Context::Left(identity, grandparent, color, sibling_model, outer_model),
                sibling_ptr: old(links.sibling_ptr), root_count: old(links.root_count), parent_count: old(links.parent_count),
                tag: old(links.tag), above: old(links.above)
            });
            solve();
        },
        Context::Right(identity, grandparent, color, sibling_model, outer_model) => {
            have links.model != Context::Top by {
                rewrite(links.model, Context::Right(identity, grandparent, color, sibling_model, outer_model)); known();
            }
            apply(links.model != Context::Top implies parent != 0 and links.root_count == 0 and links.parent_count == 1);
            have links.root_count == 0 by known();
            have links.parent_count == 1 by known();
            have erase_context_is_right(links.model) == 1 by {
                rewrite(links.model, Context::Right(identity, grandparent, color, sibling_model, outer_model));
                unfold(erase_context_is_right(Context::Right(identity, grandparent, color, sibling_model, outer_model)));
                known();
            }
            have address(links.sibling_ptr) != address(old) by {
                apply(erase_context_is_right(links.model) == 1
                    implies address(links.sibling_ptr) != address(old));
                known();
            }
            apply(erase_context_is_right(links.model) == 1
                implies parent->rb_right == old and parent->rb_left == links.sibling_ptr);
            let { sibling_ptr: sibling_ptr } = unfold(links);
            have address(parent->rb_left) != address(old) by {
                rewrite(parent->rb_left, sibling_ptr); known();
            }
            step_until(function.exit);
            have parent->rb_right == new by known();
            let updated = fold(erase_change_links(new, parent, root), {
                model: Context::Right(identity, grandparent, color, sibling_model, outer_model),
                sibling_ptr: old(links.sibling_ptr), root_count: old(links.root_count), parent_count: old(links.parent_count),
                tag: old(links.tag), above: old(links.above)
            });
            solve();
        },
    }
}


// The caller keeps the sibling and outer context while the
// helper replaces the incoming link.
resource erase_change_frame(parent: struct rb_node*, root: struct rb_root*) {
    field model: Context;
    field sibling_ptr: int32*;
    field tag: uint64;
    field above: int32*;
    match model {
        Context::Top => {
            fact parent == 0;
            fact sibling_ptr == 0;
            fact root != 0;
        },
        Context::Left(identity, grandparent, color, sibling_model, outer_model) => {
            owns sibling: rb_at(sibling_ptr);
            owns outer: ctx_at(identity, root);
            fact parent == identity;
            fact identity != 0;
            fact aligned(identity, 8);
            fact aligned(grandparent, 8);
            fact tag == address(grandparent) + (tag & 1);
            fact above == grandparent;
            fact (tag & 1) == color_bit(color);
            fact sibling.model == sibling_model;
            fact rb_parent_is(sibling_model, identity) == 1;
            fact outer.model == outer_model;
            fact ctx_node_is(outer_model, grandparent) == 1;
            fact outer_model == ctx_reroot(outer_model, grandparent);
        },
        Context::Right(identity, grandparent, color, sibling_model, outer_model) => {
            owns sibling: rb_at(sibling_ptr);
            owns outer: ctx_at(identity, root);
            fact parent == identity;
            fact identity != 0;
            fact aligned(identity, 8);
            fact aligned(grandparent, 8);
            fact tag == address(grandparent) + (tag & 1);
            fact above == grandparent;
            fact (tag & 1) == color_bit(color);
            fact sibling.model == sibling_model;
            fact rb_parent_is(sibling_model, identity) == 1;
            fact outer.model == outer_model;
            fact ctx_node_is(outer_model, grandparent) == 1;
            fact outer_model == ctx_reroot(outer_model, grandparent);
        },
    }
}

// Independent ownership of the two live node tags proves address separation.
tactic distinct_erase_sibling(focus: struct rb_node*, sibling: struct rb_node*) {
    consumes before: rb_at(sibling);
    owns focus->__rb_parent_color;
    requires focus != 0;
    produces updated: rb_at(sibling);
    ensures updated.model == old(before.model);
    ensures address(sibling) != address(focus);
} by {
    match before.model {
        RbTree::Empty => {
            unfold(before);
            have address(sibling) != address(focus) by {
                rewrite(sibling, 0); known();
            }
            let updated = fold(rb_at(sibling), { model: RbTree::Empty });
        },
        RbTree::Node(sid, sp, sc, sl, sr) => {
            let { left: left, right: right } = unfold(before);
            have separate(memory(sid->__rb_parent_color), memory(focus->__rb_parent_color)) by known();
            have address(sid) != address(focus);
            have address(sibling) != address(focus) by { rewrite(sibling, sid); known(); }
            let updated = fold(rb_at(sibling), {
                model: RbTree::Node(sid, sp, sc, sl, sr), left: left, right: right
            });
        },
    }
}

tactic detach_erase_links(focus: struct rb_node*, parent: struct rb_node*, root: struct rb_root*) {
    consumes before: ctx_at(focus, root);
    owns focus->__rb_parent_color;
    requires focus != 0;
    requires ctx_node_is(before.model, parent) == 1;
    produces links: erase_change_links(focus, parent, root);
    produces frame: erase_change_frame(parent, root);
    ensures frame.model == old(before.model);
    ensures links.model == frame.model;
    ensures links.sibling_ptr == frame.sibling_ptr;
    ensures links.tag == frame.tag;
    ensures links.above == frame.above;
    ensures links.model == Context::Top implies parent == 0 and links.root_count == 1 and links.parent_count == 0;
    ensures links.model != Context::Top implies parent != 0 and links.root_count == 0 and links.parent_count == 1;

    ensures links.model == Context::Top implies root->rb_node == focus;
    ensures links.model != Context::Top and erase_context_is_right(links.model) == 0
        implies parent->rb_left == focus and parent->rb_right == links.sibling_ptr;
    ensures erase_context_is_right(links.model) == 1
        implies parent->rb_right == focus and parent->rb_left == links.sibling_ptr;
    ensures erase_context_is_right(links.model) == 1
        implies address(links.sibling_ptr) != address(focus);
    ensures parent != 0 implies parent->__rb_parent_color == links.tag
        and ((parent->__rb_parent_color & ~3) as (struct rb_node*)) == links.above;
} by {
    apply(ctx_node_is_identity(before.model, parent));
    match before.model {
        Context::Top => {
            have parent == 0 by {
                rewrite(parent, ctx_identity(before.model));
                rewrite(before.model, Context::Top);
                unfold(ctx_identity(Context::Top)); known();
            }
            unfold(before);
            let frame = fold(erase_change_frame(parent, root), {
                model: Context::Top, sibling_ptr: 0 as (int32*), tag: 0u64, above: 0 as (int32*)
            });
            let links = fold(erase_change_links(focus, parent, root), {
                model: Context::Top, sibling_ptr: 0 as (int32*),
                root_count: 1, parent_count: 0, tag: 0u64, above: 0 as (int32*)
            });
            have erase_context_is_right(links.model) == 0 by {
                rewrite(links.model, Context::Top);
                unfold(erase_context_is_right(Context::Top)); known();
            }
            have links.model == Context::Top implies parent == 0 and links.root_count == 1 and links.parent_count == 0 by {
                intro();
                known();
            }
            have links.model != Context::Top implies parent != 0 and links.root_count == 0 and links.parent_count == 1 by {
                intro();
                contradiction(links.model != Context::Top);
            }
            have links.model == Context::Top implies root->rb_node == focus by {
                intro();
                known();
            }
            have links.model != Context::Top and erase_context_is_right(links.model) == 0 implies parent->rb_left == focus and parent->rb_right == links.sibling_ptr by {
                intro();
                have not(links.model != Context::Top and erase_context_is_right(links.model) == 0) by { rewrite(links.model, Context::Top); known(); }
                contradiction(links.model != Context::Top and erase_context_is_right(links.model) == 0);
            }
            have erase_context_is_right(links.model) == 1 implies parent->rb_right == focus and parent->rb_left == links.sibling_ptr by {
                intro();
                have erase_context_is_right(links.model) != 1 by { rewrite(erase_context_is_right(links.model), 0); known(); }
                contradiction(erase_context_is_right(links.model) == 1);
            }
            have erase_context_is_right(links.model) == 1 implies address(links.sibling_ptr) != address(focus) by {
                intro();
                have erase_context_is_right(links.model) != 1 by { rewrite(erase_context_is_right(links.model), 0); known(); }
                contradiction(erase_context_is_right(links.model) == 1);
            }
            have parent != 0 implies parent->__rb_parent_color == links.tag and ((parent->__rb_parent_color & ~3) as (struct rb_node*)) == links.above by {
                intro();
                contradiction(parent != 0);
            }
        },
        Context::Left(identity, grandparent, color, sibling_model, outer_model) => {
            have parent == identity by {
                rewrite(parent, ctx_identity(before.model));
                rewrite(before.model, Context::Left(identity, grandparent, color, sibling_model, outer_model));
                unfold(ctx_identity(Context::Left(identity, grandparent, color, sibling_model, outer_model))); known();
            }
            let { sibling: sibling, up: outer } = unfold(before);
            have parent != 0 by { rewrite(parent, identity); known(); }
            have parent->rb_left == focus by { rewrite(parent, identity); known(); }
            have parent->rb_right == identity->rb_right by { rewrite(parent, identity); known(); }
            have parent->__rb_parent_color == identity->__rb_parent_color by { rewrite(parent, identity); known(); }
            have ((parent->__rb_parent_color & ~3) as (struct rb_node*)) == grandparent by {
                rewrite(parent, identity); known();
            }
            let frame = fold(erase_change_frame(parent, root), {
                model: Context::Left(identity, grandparent, color, sibling_model, outer_model), sibling_ptr: identity->rb_right,
                tag: identity->__rb_parent_color, above: grandparent, sibling: sibling, outer: outer
            });
            let links = fold(erase_change_links(focus, parent, root), {
                model: Context::Left(identity, grandparent, color, sibling_model, outer_model), sibling_ptr: identity->rb_right,
                root_count: 0, parent_count: 1, tag: identity->__rb_parent_color, above: grandparent
            });
            have erase_context_is_right(links.model) == 0 by {
                rewrite(links.model, Context::Left(identity, grandparent, color, sibling_model, outer_model));
                unfold(erase_context_is_right(Context::Left(identity, grandparent, color, sibling_model, outer_model))); known();
            }
            have links.model == Context::Top implies parent == 0 and links.root_count == 1 and links.parent_count == 0 by {
                intro();
                have links.model != Context::Top by { rewrite(links.model, Context::Left(identity, grandparent, color, sibling_model, outer_model)); known(); }
                contradiction(links.model == Context::Top);
            }
            have links.model != Context::Top implies parent != 0 and links.root_count == 0 and links.parent_count == 1 by {
                intro();
                known();
            }
            have links.model == Context::Top implies root->rb_node == focus by {
                intro();
                have links.model != Context::Top by { rewrite(links.model, Context::Left(identity, grandparent, color, sibling_model, outer_model)); known(); }
                contradiction(links.model == Context::Top);
            }
            have links.model != Context::Top and erase_context_is_right(links.model) == 0 implies parent->rb_left == focus and parent->rb_right == links.sibling_ptr by {
                intro();
                known();
            }
            have erase_context_is_right(links.model) == 1 implies parent->rb_right == focus and parent->rb_left == links.sibling_ptr by {
                intro();
                have erase_context_is_right(links.model) != 1 by { rewrite(erase_context_is_right(links.model), 0); known(); }
                contradiction(erase_context_is_right(links.model) == 1);
            }
            have erase_context_is_right(links.model) == 1 implies address(links.sibling_ptr) != address(focus) by {
                intro();
                have erase_context_is_right(links.model) != 1 by { rewrite(erase_context_is_right(links.model), 0); known(); }
                contradiction(erase_context_is_right(links.model) == 1);
            }
            have parent != 0 implies parent->__rb_parent_color == links.tag and ((parent->__rb_parent_color & ~3) as (struct rb_node*)) == links.above by {
                intro();
                known();
            }
        },
        Context::Right(identity, grandparent, color, sibling_model, outer_model) => {
            have parent == identity by {
                rewrite(parent, ctx_identity(before.model));
                rewrite(before.model, Context::Right(identity, grandparent, color, sibling_model, outer_model));
                unfold(ctx_identity(Context::Right(identity, grandparent, color, sibling_model, outer_model))); known();
            }
            let { sibling: sibling, up: outer } = unfold(before);
            have parent != 0 by { rewrite(parent, identity); known(); }
            let { updated: sibling } = distinct_erase_sibling(focus, identity->rb_left, { before: sibling });
            have parent->rb_right == focus by { rewrite(parent, identity); known(); }
            have parent->rb_left == identity->rb_left by { rewrite(parent, identity); known(); }
            have parent->__rb_parent_color == identity->__rb_parent_color by { rewrite(parent, identity); known(); }
            have ((parent->__rb_parent_color & ~3) as (struct rb_node*)) == grandparent by {
                rewrite(parent, identity); known();
            }
            let frame = fold(erase_change_frame(parent, root), {
                model: Context::Right(identity, grandparent, color, sibling_model, outer_model), sibling_ptr: identity->rb_left,
                tag: identity->__rb_parent_color, above: grandparent, sibling: sibling, outer: outer
            });
            let links = fold(erase_change_links(focus, parent, root), {
                model: Context::Right(identity, grandparent, color, sibling_model, outer_model), sibling_ptr: identity->rb_left,
                root_count: 0, parent_count: 1, tag: identity->__rb_parent_color, above: grandparent
            });
            have erase_context_is_right(links.model) == 1 by {
                rewrite(links.model, Context::Right(identity, grandparent, color, sibling_model, outer_model));
                unfold(erase_context_is_right(Context::Right(identity, grandparent, color, sibling_model, outer_model))); known();
            }
            have links.model == Context::Top implies parent == 0 and links.root_count == 1 and links.parent_count == 0 by {
                intro();
                have links.model != Context::Top by { rewrite(links.model, Context::Right(identity, grandparent, color, sibling_model, outer_model)); known(); }
                contradiction(links.model == Context::Top);
            }
            have links.model != Context::Top implies parent != 0 and links.root_count == 0 and links.parent_count == 1 by {
                intro();
                known();
            }
            have links.model == Context::Top implies root->rb_node == focus by {
                intro();
                have links.model != Context::Top by { rewrite(links.model, Context::Right(identity, grandparent, color, sibling_model, outer_model)); known(); }
                contradiction(links.model == Context::Top);
            }
            have links.model != Context::Top and erase_context_is_right(links.model) == 0 implies parent->rb_left == focus and parent->rb_right == links.sibling_ptr by {
                intro();
                have not(links.model != Context::Top and erase_context_is_right(links.model) == 0) by { rewrite(erase_context_is_right(links.model), 1); known(); }
                contradiction(links.model != Context::Top and erase_context_is_right(links.model) == 0);
            }
            have erase_context_is_right(links.model) == 1 implies parent->rb_right == focus and parent->rb_left == links.sibling_ptr by {
                intro();
                known();
            }
            have erase_context_is_right(links.model) == 1 implies address(links.sibling_ptr) != address(focus) by {
                intro();
                known();
            }
            have parent != 0 implies parent->__rb_parent_color == links.tag and ((parent->__rb_parent_color & ~3) as (struct rb_node*)) == links.above by {
                intro();
                known();
            }
        },
    }
}

tactic attach_erase_links(focus: struct rb_node*, parent: struct rb_node*, root: struct rb_root*) {
    consumes links: erase_change_links(focus, parent, root);
    consumes frame: erase_change_frame(parent, root);
    requires links.model == frame.model;
    requires links.model == Context::Top implies parent == 0 and links.root_count == 1 and links.parent_count == 0;
    requires links.model != Context::Top implies parent != 0 and links.root_count == 0 and links.parent_count == 1;
    requires links.sibling_ptr == frame.sibling_ptr;
    requires links.tag == frame.tag;
    requires links.above == frame.above;
    requires links.model == Context::Top implies root->rb_node == focus;
    requires links.model != Context::Top and erase_context_is_right(links.model) == 0
        implies parent->rb_left == focus and parent->rb_right == links.sibling_ptr;
    requires erase_context_is_right(links.model) == 1
        implies parent->rb_right == focus and parent->rb_left == links.sibling_ptr;
    requires parent != 0 implies parent->__rb_parent_color == links.tag
        and ((parent->__rb_parent_color & ~3) as (struct rb_node*)) == links.above;
    produces updated: ctx_at(focus, root);
    ensures updated.model == old(frame.model);
} by {
    match frame.model {
        Context::Top => {
            have links.model == Context::Top by known();
            apply(links.model == Context::Top implies parent == 0 and links.root_count == 1 and links.parent_count == 0);
            apply(links.model == Context::Top implies root->rb_node == focus);
            unfold(links);
            unfold(frame);
            let updated = fold(ctx_at(focus, root), { model: Context::Top });
        },
        Context::Left(identity, grandparent, color, sibling_model, outer_model) => {
            have links.model == Context::Left(identity, grandparent, color, sibling_model, outer_model) by known();
            have erase_context_is_right(links.model) == 0 by {
                rewrite(links.model, Context::Left(identity, grandparent, color, sibling_model, outer_model));
                unfold(erase_context_is_right(Context::Left(identity, grandparent, color, sibling_model, outer_model))); normalize();
            }
            have links.model != Context::Top by { rewrite(links.model, Context::Left(identity, grandparent, color, sibling_model, outer_model)); normalize(); }
            apply(links.model != Context::Top and erase_context_is_right(links.model) == 0
                implies parent->rb_left == focus and parent->rb_right == links.sibling_ptr);
            apply(links.model != Context::Top implies parent != 0 and links.root_count == 0 and links.parent_count == 1);
            let { tag: tag, above: above, sibling_ptr: link_sibling } = unfold(links);
            let { sibling: sibling, outer: outer, sibling_ptr: sibling_ptr } = unfold(frame);
            have parent != 0 by known();
            apply(parent != 0 implies parent->__rb_parent_color == tag
                and ((parent->__rb_parent_color & ~3) as (struct rb_node*)) == above);
            have parent == identity by known();
            have parent->rb_right == sibling_ptr by {
                rewrite(sibling_ptr, link_sibling);
                known();
            }
            let updated = fold(ctx_at(focus, root), {
                model: Context::Left(parent, grandparent, color, sibling_model, outer_model),
                sibling: sibling, up: outer
            });
            have updated.model == old(frame.model) by {
                rewrite(parent, identity);
                known();
            }
        },
        Context::Right(identity, grandparent, color, sibling_model, outer_model) => {
            have links.model == Context::Right(identity, grandparent, color, sibling_model, outer_model) by known();
            have links.model != Context::Top by { rewrite(links.model, Context::Right(identity, grandparent, color, sibling_model, outer_model)); normalize(); }
            have erase_context_is_right(links.model) == 1 by {
                rewrite(links.model, Context::Right(identity, grandparent, color, sibling_model, outer_model));
                unfold(erase_context_is_right(Context::Right(identity, grandparent, color, sibling_model, outer_model))); normalize();
            }
            apply(erase_context_is_right(links.model) == 1
                implies parent->rb_right == focus and parent->rb_left == links.sibling_ptr);
            apply(links.model != Context::Top implies parent != 0 and links.root_count == 0 and links.parent_count == 1);
            let { tag: tag, above: above, sibling_ptr: link_sibling } = unfold(links);
            let { sibling: sibling, outer: outer, sibling_ptr: sibling_ptr } = unfold(frame);
            have parent != 0 by known();
            apply(parent != 0 implies parent->__rb_parent_color == tag
                and ((parent->__rb_parent_color & ~3) as (struct rb_node*)) == above);
            have parent == identity by known();
            have parent->rb_left == sibling_ptr by {
                rewrite(sibling_ptr, link_sibling);
                known();
            }
            let updated = fold(ctx_at(focus, root), {
                model: Context::Right(parent, grandparent, color, sibling_model, outer_model),
                sibling: sibling, up: outer
            });
            have updated.model == old(frame.model) by {
                rewrite(parent, identity);
                known();
            }
        },
    }
}
