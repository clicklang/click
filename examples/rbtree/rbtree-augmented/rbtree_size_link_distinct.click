arithmetic "integer";

// An owned replacement word cannot alias the incoming link's parent word.
verifying "rb_insert_augmented.c" as insert;
verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_change_child.click";

tactic sized_link_replacement_distinct(child: struct rb_node*, replacement: struct rb_node*,
                                       root: struct rb_root*, previous: int32) {
    owns link: sized_link_at(child, root, previous);
    owns replacement->__rb_parent_color;
    requires replacement != 0;
    ensures link.model == old(link.model);
    ensures sized_context_parent(link.model, 0) == 0 or replacement != sized_context_parent(link.model, 0);
} by {
    match link.model {
        SizedContext::Top => {
            have link.model == old(link.model) by { normalize(); }
            have sized_context_parent(link.model, 0) == 0 by {
                rewrite(link.model == SizedContext::Top);
                unfold(sized_context_parent(SizedContext::Top, 0)); normalize();
            }
            have sized_context_parent(link.model, 0) == 0 or replacement != sized_context_parent(link.model, 0) by {
                assumption();
            }
        },
        SizedContext::Left(a, above, shade, value, sibling_model, up_model) => {
            let { frames: frames } = unfold(link);
            let { metadata: metadata, sibling: sibling, up: up } = unfold(frames);
            have separate(memory(replacement->__rb_parent_color), memory(a->__rb_parent_color)) by { assumption(); }
            have replacement != a by {
                assumption();
            }
            let frames = fold(sized_context_at(child, root->rb_node, 0, previous), {
                model: SizedContext::Left(a, above, shade, value, sibling_model, up_model)
            }, { metadata: metadata, sibling: sibling, up: up });
            let link = fold(sized_link_at(child, root, previous), {
                model: SizedContext::Left(a, above, shade, value, sibling_model, up_model)
            }, { frames: frames });
            have sized_context_parent(link.model, 0) == a by {
                rewrite(link.model == SizedContext::Left(a, above, shade, value, sibling_model, up_model));
                unfold(sized_context_parent(SizedContext::Left(a, above, shade, value, sibling_model, up_model), 0)); normalize();
            }
            have replacement != sized_context_parent(link.model, 0) by {
                rewrite(sized_context_parent(link.model, 0) == a); assumption();
            }
            have sized_context_parent(link.model, 0) == 0 or replacement != sized_context_parent(link.model, 0) by {
                assumption();
            }
        },
        SizedContext::Right(a, above, shade, value, sibling_model, up_model) => {
            let { frames: frames } = unfold(link);
            let { metadata: metadata, sibling: sibling, up: up } = unfold(frames);
            have separate(memory(replacement->__rb_parent_color), memory(a->__rb_parent_color)) by { assumption(); }
            have replacement != a by {
                assumption();
            }
            let frames = fold(sized_context_at(child, root->rb_node, 0, previous), {
                model: SizedContext::Right(a, above, shade, value, sibling_model, up_model)
            }, { metadata: metadata, sibling: sibling, up: up });
            let link = fold(sized_link_at(child, root, previous), {
                model: SizedContext::Right(a, above, shade, value, sibling_model, up_model)
            }, { frames: frames });
            have sized_context_parent(link.model, 0) == a by {
                rewrite(link.model == SizedContext::Right(a, above, shade, value, sibling_model, up_model));
                unfold(sized_context_parent(SizedContext::Right(a, above, shade, value, sibling_model, up_model), 0)); normalize();
            }
            have replacement != sized_context_parent(link.model, 0) by {
                rewrite(sized_context_parent(link.model, 0) == a); assumption();
            }
            have sized_context_parent(link.model, 0) == 0 or replacement != sized_context_parent(link.model, 0) by {
                assumption();
            }
        },
    }
}
