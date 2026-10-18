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

spec enum SizedRotationInput { Left(SizedTree), Right(SizedTree) }

function sized_rotation_input_tree(model: SizedRotationInput) -> SizedTree {
    match model {
        SizedRotationInput::Left(tree) => tree,
        SizedRotationInput::Right(tree) => tree,
    }
}

resource sized_rotation_input_at(old: struct rb_node*, new: struct rb_node*) {
    field model: SizedRotationInput;
    match model {
        SizedRotationInput::Left(tree_model) => {
            owns tree: sized_rotation_left_at(old, new);
            fact tree.model == tree_model;
            fact 0 <= sized_value(sized_left(sized_left(tree_model)));
            fact 0 <= sized_value(sized_right(sized_left(tree_model)));
            fact sized_value(sized_right(sized_left(tree_model))) <= 2147483646;
            fact sized_value(sized_left(sized_left(tree_model))) <= 2147483646 - sized_value(sized_right(sized_left(tree_model)));
        },
        SizedRotationInput::Right(tree_model) => {
            owns tree: sized_rotation_right_at(old, new);
            fact tree.model == tree_model;
            fact 0 <= sized_value(sized_left(sized_right(tree_model)));
            fact 0 <= sized_value(sized_right(sized_right(tree_model)));
            fact sized_value(sized_right(sized_right(tree_model))) <= 2147483646;
            fact sized_value(sized_left(sized_right(tree_model))) <= 2147483646 - sized_value(sized_right(sized_right(tree_model)));
        },
    }
}

void sized_rotate_from_table(struct rb_node* old, struct rb_node* new,
                            const struct rb_augment_callbacks* augment) {
    views sized_callback_table(augment);
    consumes input: sized_rotation_input_at(old, new);
    produces checked: sized_at(new);
    requires old != 0;
    requires new != 0;
    requires old != new;
    ensures sized_shape(checked.model) == sized_shape(sized_rotation_input_tree(old(input.model)));
    ensures to_integer(sized_value(checked.model)) == rb_subtree_size(sized_shape(checked.model));
} by {
    open(sized_callback_table(augment)) {
        match input.model {
            SizedRotationInput::Left(tree_model) => {
                let { tree: tree } = unfold(input);
                step(); step();
                let { checked: checked } = step(RotateTreeLeft, { tree: tree });
                have sized_rotation_input_tree(old(input.model)) == tree_model by {
                    rewrite(old(input.model) == SizedRotationInput::Left(tree_model));
                    unfold(sized_rotation_input_tree(SizedRotationInput::Left(tree_model)));
                    normalize();
                }
                execute(); simp();
            },
            SizedRotationInput::Right(tree_model) => {
                let { tree: tree } = unfold(input);
                step(); step();
                let { checked: checked } = step(RotateTreeRight, { tree: tree });
                have sized_rotation_input_tree(old(input.model)) == tree_model by {
                    rewrite(old(input.model) == SizedRotationInput::Right(tree_model));
                    unfold(sized_rotation_input_tree(SizedRotationInput::Right(tree_model)));
                    normalize();
                }
                execute(); simp();
            },
        }
    }
}

contract void RotateTableLeft(struct rb_node* old, struct rb_node* new,
                              const struct rb_augment_callbacks* augment) {
    views sized_callback_table(augment);
    consumes tree: sized_rotation_left_at(old, new);
    produces checked: sized_at(new);
    requires old != 0;
    requires new != 0;
    requires old != new;
    requires 0 <= sized_value(sized_left(sized_left(tree.model)));
    requires 0 <= sized_value(sized_right(sized_left(tree.model)));
    requires sized_value(sized_right(sized_left(tree.model))) <= 2147483646;
    requires sized_value(sized_left(sized_left(tree.model))) <= 2147483646 - sized_value(sized_right(sized_left(tree.model)));
    ensures sized_shape(checked.model) == sized_shape(old(tree.model));
    ensures to_integer(sized_value(checked.model)) == rb_subtree_size(sized_shape(checked.model));
}

theorem sized_table_rotate_left()
executes sized_rotate_from_table(struct rb_node* old, struct rb_node* new,
                                 const struct rb_augment_callbacks* augment) {
    ensures RotateTableLeft(&sized_rotate_from_table) as { tree: tree, checked: checked } by {
        let input = fold(sized_rotation_input_at(old, new), { model: SizedRotationInput::Left(tree.model) });
        let { checked: checked } = step(sized_rotate_from_table(old, new, augment), { input: input });
        have sized_rotation_input_tree(SizedRotationInput::Left(old(tree.model))) == old(tree.model) by {
            unfold(sized_rotation_input_tree(SizedRotationInput::Left(old(tree.model))));
            normalize();
        }
        simp();
    }
}

contract void RotateTableRight(struct rb_node* old, struct rb_node* new,
                              const struct rb_augment_callbacks* augment) {
    views sized_callback_table(augment);
    consumes tree: sized_rotation_right_at(old, new);
    produces checked: sized_at(new);
    requires old != 0;
    requires new != 0;
    requires old != new;
    requires 0 <= sized_value(sized_left(sized_right(tree.model)));
    requires 0 <= sized_value(sized_right(sized_right(tree.model)));
    requires sized_value(sized_right(sized_right(tree.model))) <= 2147483646;
    requires sized_value(sized_left(sized_right(tree.model))) <= 2147483646 - sized_value(sized_right(sized_right(tree.model)));
    ensures sized_shape(checked.model) == sized_shape(old(tree.model));
    ensures to_integer(sized_value(checked.model)) == rb_subtree_size(sized_shape(checked.model));
}

theorem sized_table_rotate_right()
executes sized_rotate_from_table(struct rb_node* old, struct rb_node* new,
                                 const struct rb_augment_callbacks* augment) {
    ensures RotateTableRight(&sized_rotate_from_table) as { tree: tree, checked: checked } by {
        let input = fold(sized_rotation_input_at(old, new), { model: SizedRotationInput::Right(tree.model) });
        let { checked: checked } = step(sized_rotate_from_table(old, new, augment), { input: input });
        have sized_rotation_input_tree(SizedRotationInput::Right(old(tree.model))) == old(tree.model) by {
            unfold(sized_rotation_input_tree(SizedRotationInput::Right(old(tree.model))));
            normalize();
        }
        simp();
    }
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
