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

void insert::__rb_change_child(struct rb_node* old, struct rb_node* new,
                       struct rb_node* parent, struct rb_root* root) {
    consumes before: sized_link_at(old,root,(old as (void *) as (struct sized_node *))->size);
    owns old->__rb_parent_color;
    owns (old as (void *) as (struct sized_node *))->size;
    requires old != 0;
    requires parent == sized_context_parent(before.model,0);
    requires parent == 0 or new != parent;
    produces after: sized_link_at(new,root,(old as (void *) as (struct sized_node *))->size);
    ensures after.model == old(before.model);
    ensures (old as (void *) as (struct sized_node *))->size == old((old as (void *) as (struct sized_node *))->size);
    ensures old->__rb_parent_color == old(old->__rb_parent_color);
} by {
    match before.model {
        SizedContext::Top => {
            have parent == 0 by {
                rewrite(parent == sized_context_parent(before.model,0));
                rewrite(before.model == SizedContext::Top);
                unfold(sized_context_parent(SizedContext::Top,0)); normalize();
            }
            let { frames: frames } = unfold(before);
            unfold(frames);
            step_until(function.exit);
            let frames = fold(sized_context_at(new,root->rb_node,0,(old as (void *) as (struct sized_node *))->size), { model: SizedContext::Top });
            let after = fold(sized_link_at(new,root,(old as (void *) as (struct sized_node *))->size), { model: SizedContext::Top }, { frames: frames });
            solve();
        },
        SizedContext::Left(a, above, shade, value, sibling_model, up_model) => {
            have parent == a by {
                rewrite(parent == sized_context_parent(before.model,0));
                rewrite(before.model == SizedContext::Left(a, above, shade, value, sibling_model, up_model));
                unfold(sized_context_parent(SizedContext::Left(a, above, shade, value, sibling_model, up_model),0)); normalize();
            }
            let { frames: frames } = unfold(before);
            let { metadata: a_size, sibling: sibling, up: up } = unfold(frames);
            have parent != 0 by { rewrite(parent == a); assumption(); }
            have new != a by {
                rewrite(a == parent);
                cases {
                    parent == 0 => { contradiction(parent == 0); }
                    new != parent => { assumption(); }
                }
            }
            have a->rb_right != a by assumption();
            mark a_links;
            step_until(function.exit);
            have a->rb_right != a by {
                transport(at(a_links, a->rb_right != a), a->rb_right != a);
            }
            let frames = fold(sized_context_at(new,root->rb_node,0,(old as (void *) as (struct sized_node *))->size), { model: SizedContext::Left(a, above, shade, value, sibling_model, up_model) }, { metadata: a_size, sibling: sibling, up: up });
            let after = fold(sized_link_at(new,root,(old as (void *) as (struct sized_node *))->size), { model: SizedContext::Left(a, above, shade, value, sibling_model, up_model) }, { frames: frames });
            solve();
        },
        SizedContext::Right(a, above, shade, value, sibling_model, up_model) => {
            have parent == a by {
                rewrite(parent == sized_context_parent(before.model,0));
                rewrite(before.model == SizedContext::Right(a, above, shade, value, sibling_model, up_model));
                unfold(sized_context_parent(SizedContext::Right(a, above, shade, value, sibling_model, up_model),0)); normalize();
            }
            let { frames: frames } = unfold(before);
            let { metadata: a_size, sibling: sibling, up: up } = unfold(frames);
            have parent != 0 by { rewrite(parent == a); assumption(); }
            have new != a by {
                rewrite(a == parent);
                cases {
                    parent == 0 => { contradiction(parent == 0); }
                    new != parent => { assumption(); }
                }
            }
            match sibling.model {
                SizedTree::Empty => {
                    unfold(sibling);
                    have parent->rb_left == 0 by { assumption(); }
                    have parent->rb_left != old by {
                        rewrite(parent->rb_left == 0); assumption();
                    }
                    step_until(function.exit);
                    let sibling = fold(sized_at(parent->rb_left), { model: SizedTree::Empty });
                    let frames = fold(sized_context_at(new,root->rb_node,0,(old as (void *) as (struct sized_node *))->size), { model: SizedContext::Right(a, above, shade, value, sibling_model, up_model) }, { metadata: a_size, sibling: sibling, up: up });
                    let after = fold(sized_link_at(new,root,(old as (void *) as (struct sized_node *))->size), { model: SizedContext::Right(a, above, shade, value, sibling_model, up_model) }, { frames: frames });
                    solve();
                },
                SizedTree::Node(identity, sp, sc, size, sl, sr) => {
                    let { metadata: s_size, left: s_left, right: s_right } = unfold(sibling);
                    have parent->rb_left->rb_left != parent->rb_left by assumption();
                    have parent->rb_left->rb_right != parent->rb_left by assumption();
                    step();
                    step();
                    let sibling = fold(sized_at(parent->rb_left), { model: SizedTree::Node(identity,sp,sc,size,sl,sr) }, { metadata: s_size, left: s_left, right: s_right });
                    step_until(function.exit);
                    let frames = fold(sized_context_at(new,root->rb_node,0,(old as (void *) as (struct sized_node *))->size), { model: SizedContext::Right(a, above, shade, value, sibling_model, up_model) }, { metadata: a_size, sibling: sibling, up: up });
                    let after = fold(sized_link_at(new,root,(old as (void *) as (struct sized_node *))->size), { model: SizedContext::Right(a, above, shade, value, sibling_model, up_model) }, { frames: frames });
                    solve();
                },
            }
        },
    }
}
