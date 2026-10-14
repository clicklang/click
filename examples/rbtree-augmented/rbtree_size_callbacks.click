verifying "rbtree_size_callbacks.c";
import "rbtree_size_callback_frames.click";
import "rbtree_size_rotate_model.click";
import "rbtree_size_propagate_tree.click";

resource sized_callback_table(augment: const struct rb_augment_callbacks*) {
    views augment->propagate;
    views augment->copy;
    views augment->rotate;
    fact PropagateTree(augment->propagate);
    fact CopySizedStructure(augment->copy);
    fact RotateTreeLeft(augment->rotate);
    fact RotateTreeRight(augment->rotate);
}

void sized_copy_from_table(struct rb_node* old, struct rb_node* new,
                           const struct rb_augment_callbacks* augment) {
    views sized_callback_table(augment);
    owns source_tree: rb_at(old);
    owns target_tree: rb_at(new);
    owns source: size_metadata(old);
    owns target: size_metadata(new);
    ensures source_tree.model == old(source_tree.model);
    ensures target_tree.model == old(target_tree.model);
    ensures source.value == old(source.value);
    ensures target.value == old(source.value);
} by {
    open(sized_callback_table(augment)) {
        step(); step();
        step(CopySizedStructure, {
            source_tree: source_tree, target_tree: target_tree, source: source, target: target
        });
        execute(); simp();
    }
}

void sized_copy_from_generated_table(struct rb_node* old, struct rb_node* new) {
    views sized.propagate;
    views sized.copy;
    views sized.rotate;
    owns source_tree: rb_at(old);
    owns target_tree: rb_at(new);
    owns source: size_metadata(old);
    owns target: size_metadata(new);
    ensures source_tree.model == old(source_tree.model);
    ensures target_tree.model == old(target_tree.model);
    ensures source.value == old(source.value);
    ensures target.value == old(source.value);
} by {
    apply(sized_propagate_has_tree_contract());
    apply(sized_copy_preserves_structure());
    apply(sized_rotate_restores_subtree_size_left());
    apply(sized_rotate_restores_subtree_size_right());
    fold(sized_callback_table(&sized));
    step(sized_copy_from_table(old, new, &sized), {
        source_tree: source_tree, target_tree: target_tree, source: source, target: target
    });
    execute(); simp();
}

void sized_propagate_from_table(struct rb_node* rb, struct rb_node* stop,
                                const struct rb_augment_callbacks* augment) {
    views sized_callback_table(augment);
    consumes walk: sized_walk_at(rb, stop);
    produces whole: sized_result_at(stop);
    requires sized_walk_pending(walk.model) == 1 or rb == stop;
    requires rb_subtree_size(sized_shape(sized_walk_tree(walk.model))) <= 2147483647;
    ensures sized_result_root(whole.model) == sized_walk_root(old(walk.model));
    ensures sized_shape(sized_result_tree(whole.model)) == sized_shape(sized_walk_tree(old(walk.model)));
    ensures sized_counts_valid(sized_result_tree(whole.model)) == 1;
} by {
    open(sized_callback_table(augment)) {
        step(); step();
        let { whole: whole } = step(PropagateTree, { walk: walk });
        execute(); simp();
    }
}
