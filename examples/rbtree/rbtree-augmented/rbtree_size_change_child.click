// Replace a focus link while retaining every cached ancestor count.
verifying "rb_insert_augmented.c" as insert;
verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_context_resources.click";

resource sized_link_at(child: struct rb_node*, root: struct rb_root*, previous: int32) {
    field model: SizedContext;
    owns root->rb_node;
    owns frames: sized_context_at(child,root->rb_node,0,previous);
    fact frames.model == model;
}

// These observations stay owned while the other child slot is updated.
resource change_child_parent_tag(node: struct rb_node*, parent: struct rb_node*) {
    field color: Color;
    owns node->__rb_parent_color;
    fact node->__rb_parent_color == address(parent) + (node->__rb_parent_color & 1);
    fact ((node->__rb_parent_color & ~3) as (struct rb_node *)) == parent;
    fact (node->__rb_parent_color & 1) == color_bit(color);
}

resource change_child_old_tag(node: struct rb_node*) {
    field word: uint64;
    field parent: int32*;
    owns node->__rb_parent_color;
    fact node->__rb_parent_color == word;
    fact ((node->__rb_parent_color & ~3) as (struct rb_node *)) == parent;
}

resource change_child_sibling_link(node: struct rb_node*, slot: struct rb_node**) {
    field child: int32*;
    owns *slot;
    fact *slot == child;
    fact *slot != node;
}

resource change_child_root_link(root: struct rb_root*) {
    field node: int32*;
    owns root->rb_node;
    fact root->rb_node == node;
}

void insert::__rb_change_child(struct rb_node* old, struct rb_node* new,
                       struct rb_node* parent, struct rb_root* root) {
    consumes before: sized_link_at(old,root,(old as (void *) as (struct sized_node *))->size);
    owns old->__rb_parent_color;
    owns (old as (void *) as (struct sized_node *))->size;
    requires old != 0;
    requires parent == sized_context_parent(before.model,0);
    requires parent == 0 or new != parent;
    produces after: sized_link_at(new,root,old((old as (void *) as (struct sized_node *))->size));
    ensures after.model == old(before.model);
    ensures (old as (void *) as (struct sized_node *))->size == old((old as (void *) as (struct sized_node *))->size);
    ensures old->__rb_parent_color == old(old->__rb_parent_color);
    // The parent the word designates, so a caller keeps its parent cast.
    ensures ((old->__rb_parent_color & ~3) as (struct rb_node *)) == old(((old->__rb_parent_color & ~3) as (struct rb_node *)));
} by {
    let old_size = fold(size_metadata(old), { value: (old as (void *) as (struct sized_node *))->size });
    let old_tag = fold(change_child_old_tag(old), { word: old(old->__rb_parent_color), parent: old(((old->__rb_parent_color & ~3) as (struct rb_node *))) });
    match before.model {
        SizedContext::Top => {
            have parent == 0 by {
                rewrite(parent, sized_context_parent(before.model,0));
                rewrite(before.model, SizedContext::Top);
                unfold(sized_context_parent(SizedContext::Top,0)); normalize();
            }
            let { frames: frames } = unfold(before);
            unfold(frames);
            step_until(function.exit);
            let frames = fold(sized_context_at(new,root->rb_node,0, old((old as (void *) as (struct sized_node *))->size)), { model: SizedContext::Top });
            let after = fold(sized_link_at(new,root, old((old as (void *) as (struct sized_node *))->size)), { model: SizedContext::Top }, { frames: frames });
            unfold(old_tag);
            unfold(old_size);
            have (old as (void *) as (struct sized_node *))->size == old((old as (void *) as (struct sized_node *))->size) by known();
            have old->__rb_parent_color == old(old->__rb_parent_color) by known();
            have ((old->__rb_parent_color & ~3) as (struct rb_node *)) == old(((old->__rb_parent_color & ~3) as (struct rb_node *))) by known();
            solve();
        },
        SizedContext::Left(a, above, shade, value, sibling_model, up_model) => {
            have parent == a by {
                rewrite(parent, sized_context_parent(before.model,0));
                rewrite(before.model, SizedContext::Left(a, above, shade, value, sibling_model, up_model));
                unfold(sized_context_parent(SizedContext::Left(a, above, shade, value, sibling_model, up_model),0)); normalize();
            }
            let { frames: frames } = unfold(before);
            let { metadata: a_size, sibling: sibling, up: up } = unfold(frames);
            have parent != 0 by { rewrite(parent, a); known(); }
            have new != a by {
                rewrite(a, parent);
                cases {
                    parent == 0 => { contradiction(parent == 0); }
                    new != parent => { known(); }
                }
            }
            let tag = fold(change_child_parent_tag(a, above), { color: shade });
            let sibling_link = fold(change_child_sibling_link(a, &a->rb_right), { child: a->rb_right });
            let root_link = fold(change_child_root_link(root), { node: old(root->rb_node) });
            step(); step(); step();
            step_until(function.exit);
            unfold(tag); unfold(sibling_link); unfold(root_link);
            have root->rb_node == old(root->rb_node) by known();
            let frames = fold(sized_context_at(new,old(root->rb_node),0, old((old as (void *) as (struct sized_node *))->size)), { model: SizedContext::Left(a, above, shade, value, sibling_model, up_model) }, { metadata: a_size, sibling: sibling, up: up });
            let after = fold(sized_link_at(new,root, old((old as (void *) as (struct sized_node *))->size)), { model: SizedContext::Left(a, above, shade, value, sibling_model, up_model) }, { frames: frames });
            unfold(old_tag);
            unfold(old_size);
            have (old as (void *) as (struct sized_node *))->size == old((old as (void *) as (struct sized_node *))->size) by known();
            have old->__rb_parent_color == old(old->__rb_parent_color) by known();
            have ((old->__rb_parent_color & ~3) as (struct rb_node *)) == old(((old->__rb_parent_color & ~3) as (struct rb_node *))) by known();
            solve();
        },
        SizedContext::Right(a, above, shade, value, sibling_model, up_model) => {
            have parent == a by {
                rewrite(parent, sized_context_parent(before.model,0));
                rewrite(before.model, SizedContext::Right(a, above, shade, value, sibling_model, up_model));
                unfold(sized_context_parent(SizedContext::Right(a, above, shade, value, sibling_model, up_model),0)); normalize();
            }
            let { frames: frames } = unfold(before);
            let { metadata: a_size, sibling: sibling, up: up } = unfold(frames);
            have parent != 0 by { rewrite(parent, a); known(); }
            have new != a by {
                rewrite(a, parent);
                cases {
                    parent == 0 => { contradiction(parent == 0); }
                    new != parent => { known(); }
                }
            }
            match sibling.model {
                SizedTree::Empty => {
                    unfold(sibling);
                    have parent->rb_left == 0 by known();
                    have parent->rb_left != old by {
                        rewrite(parent->rb_left, 0); known();
                    }
                    let sibling = fold(sized_at(0), { model: SizedTree::Empty });
                    let tag = fold(change_child_parent_tag(a, above), { color: shade });
                    let sibling_link = fold(change_child_sibling_link(a, &a->rb_left), { child: 0 as (int32*) });
                    let root_link = fold(change_child_root_link(root), { node: old(root->rb_node) });
                    step(); step(); step();
                    step_until(function.exit);
                    unfold(tag); unfold(sibling_link); unfold(root_link);
                    have root->rb_node == old(root->rb_node) by known();
                    let frames = fold(sized_context_at(new,old(root->rb_node),0, old((old as (void *) as (struct sized_node *))->size)), { model: SizedContext::Right(a, above, shade, value, sibling_model, up_model) }, { metadata: a_size, sibling: sibling, up: up });
                    let after = fold(sized_link_at(new,root, old((old as (void *) as (struct sized_node *))->size)), { model: SizedContext::Right(a, above, shade, value, sibling_model, up_model) }, { frames: frames });
                    unfold(old_tag);
                    unfold(old_size);
                    have (old as (void *) as (struct sized_node *))->size == old((old as (void *) as (struct sized_node *))->size) by known();
                    have old->__rb_parent_color == old(old->__rb_parent_color) by known();
                    have ((old->__rb_parent_color & ~3) as (struct rb_node *)) == old(((old->__rb_parent_color & ~3) as (struct rb_node *))) by known();
                    solve();
                },
                SizedTree::Node(identity, sp, sc, size, sl, sr) => {
                    let { metadata: s_size, left: s_left, right: s_right } = unfold(sibling);
                    have a->rb_left == identity by known();
                    unfold(old_tag);
                    have separate(memory(identity->__rb_parent_color), memory(old->__rb_parent_color)) by known();
                    have identity != old by known();
                    have parent->rb_left != old by {
                        rewrite(parent, a);
                        rewrite(a->rb_left, identity); known();
                    }
                    let old_tag = fold(change_child_old_tag(old), { word: old(old->__rb_parent_color), parent: old(((old->__rb_parent_color & ~3) as (struct rb_node *))) });
                    let sibling = fold(sized_at(identity), { model: SizedTree::Node(identity,sp,sc,size,sl,sr) }, { metadata: s_size, left: s_left, right: s_right });
                    let tag = fold(change_child_parent_tag(a, above), { color: shade });
                    let sibling_link = fold(change_child_sibling_link(a, &a->rb_left), { child: identity });
                    let root_link = fold(change_child_root_link(root), { node: old(root->rb_node) });
                    step(); step(); step();
                    step_until(function.exit);
                    unfold(tag); unfold(sibling_link); unfold(root_link);
                    have root->rb_node == old(root->rb_node) by known();
                    let frames = fold(sized_context_at(new,old(root->rb_node),0, old((old as (void *) as (struct sized_node *))->size)), { model: SizedContext::Right(a, above, shade, value, sibling_model, up_model) }, { metadata: a_size, sibling: sibling, up: up });
                    let after = fold(sized_link_at(new,root, old((old as (void *) as (struct sized_node *))->size)), { model: SizedContext::Right(a, above, shade, value, sibling_model, up_model) }, { frames: frames });
                    unfold(old_tag);
                    unfold(old_size);
                    have (old as (void *) as (struct sized_node *))->size == old((old as (void *) as (struct sized_node *))->size) by known();
                    have old->__rb_parent_color == old(old->__rb_parent_color) by known();
                    have ((old->__rb_parent_color & ~3) as (struct rb_node *)) == old(((old->__rb_parent_color & ~3) as (struct rb_node *))) by known();
                    solve();
                },
            }
        },
    }
}
