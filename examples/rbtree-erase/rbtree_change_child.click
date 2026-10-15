// Replace the focus link while preserving its surrounding context.
// Ownership of the old node's tag separates it from a nonempty sibling.
verifying "rb_erase_augmented.c";
import "../rbtree-model/rbtree_resources.click";

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
    match before.model {
        Context::Top => {
            have parent == 0 by auto;
            unfold(before);
            execute();
            let after = fold(ctx_at(new, root), { model: Context::Top });
            simp();
        },
        Context::Left(identity, grandparent, color, sibling_model, outer_model) => {
            have parent == identity by auto;
            let { sibling: sibling, up: outer } = unfold(before);
            execute();
            let after = fold(ctx_at(new, root), {
                model: Context::Left(identity, grandparent, color, sibling_model, outer_model)
            }, { up: outer });
            simp();
        },
        Context::Right(identity, grandparent, color, sibling_model, outer_model) => {
            have parent == identity by auto;
            let { sibling: sibling, up: outer } = unfold(before);
            match sibling.model {
                RbTree::Empty => {
                    unfold(sibling);
                    execute();
                    let sibling = fold(rb_at(parent->rb_left), { model: RbTree::Empty });
                    let after = fold(ctx_at(new, root), {
                        model: Context::Right(identity, grandparent, color, sibling_model, outer_model)
                    }, { up: outer });
                    simp();
                },
                RbTree::Node(sid, sp, sc, sl, sr) => {
                    let { left: left, right: right } = unfold(sibling);
                    execute();
                    let sibling = fold(rb_at(parent->rb_left), {
                        model: RbTree::Node(sid, sp, sc, sl, sr)
                    });
                    let after = fold(ctx_at(new, root), {
                        model: Context::Right(identity, grandparent, color, sibling_model, outer_model)
                    }, { up: outer });
                    simp();
                },
            }
        },
    }
}
