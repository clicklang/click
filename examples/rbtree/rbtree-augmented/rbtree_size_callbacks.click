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

// Combine the table's three field views into the descriptor used by the call.
theorem separate_from_sized_callback_reads(table: const int32*, input: Resource) {
    requires separate(input, memory(table[0..2]));
    requires separate(input, memory(table[2..4]));
    requires separate(input, memory(table[4..6]));
    ensures separate(input, (((memory(table[0..6]) * memory(table[0..2]))
        * memory(table[2..4])) * memory(table[4..6]))) by {
        apply(click::separation::separate_symm(input, memory(table[0..2])));
        apply(click::separation::separate_symm(input, memory(table[2..4])));
        apply(click::separation::separate_symm(input, memory(table[4..6])));
        apply(click::separation::contains_refl(input));
        apply(click::separation::contains_joined_ranges(table, 0, 2, 4));
        apply(click::separation::separate_star(memory(table[0..2]), memory(table[2..4]), input));
        apply(click::separation::separate_restrict(
            memory(table[0..2]) * memory(table[2..4]), input,
            memory(table[0..4]), input));
        apply(click::separation::contains_joined_ranges(table, 0, 4, 6));
        apply(click::separation::separate_star(
            memory(table[0..4]), memory(table[4..6]), input));
        apply(click::separation::separate_restrict(
            memory(table[0..4]) * memory(table[4..6]), input,
            memory(table[0..6]), input));
        apply(click::separation::separate_star(memory(table[0..6]), memory(table[0..2]), input));
        apply(click::separation::separate_star(
            memory(table[0..6]) * memory(table[0..2]), memory(table[2..4]), input));
        apply(click::separation::separate_star(
            (memory(table[0..6]) * memory(table[0..2])) * memory(table[2..4]), memory(table[4..6]), input));
        apply(click::separation::separate_symm(
            ((memory(table[0..6]) * memory(table[0..2])) * memory(table[2..4])) * memory(table[4..6]), input));
    }
}

theorem separate_callback_inputs(a: Resource, b: Resource, c: Resource, d: Resource, view: Resource) {
    requires separate(a, view);
    requires separate(b, view);
    requires separate(c, view);
    requires separate(d, view);
    ensures separate(((a * b) * c) * d, view) by {
        apply(click::separation::separate_star(a, b, view));
        apply(click::separation::separate_star(a * b, c, view));
        apply(click::separation::separate_star((a * b) * c, d, view));
    }
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
    with(sized_callback_table(augment)) {
        have separate(source_tree, memory(augment->propagate)) by known();
        have separate(target_tree, memory(augment->propagate)) by known();
        have separate(source, memory(augment->propagate)) by known();
        have separate(target, memory(augment->propagate)) by known();
        apply(separate_callback_inputs(source_tree, target_tree, source, target, memory(augment->propagate)));
        have separate(source_tree, memory(augment->copy)) by known();
        have separate(target_tree, memory(augment->copy)) by known();
        have separate(source, memory(augment->copy)) by known();
        have separate(target, memory(augment->copy)) by known();
        apply(separate_callback_inputs(source_tree, target_tree, source, target, memory(augment->copy)));
        have separate(source_tree, memory(augment->rotate)) by known();
        have separate(target_tree, memory(augment->rotate)) by known();
        have separate(source, memory(augment->rotate)) by known();
        have separate(target, memory(augment->rotate)) by known();
        apply(separate_callback_inputs(source_tree, target_tree, source, target, memory(augment->rotate)));
        apply(separate_from_sized_callback_reads(augment as (const int32 *), ((source_tree * target_tree) * source) * target));
        step(CopySizedStructure, {
            source_tree: source_tree, target_tree: target_tree, source: source, target: target
        });
        step_until(function.exit);
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
    step(sized_copy_from_table, {
        source_tree: source_tree, target_tree: target_tree, source: source, target: target
    });
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
    with(sized_callback_table(augment)) {
        match input.model {
            SizedRotationInput::Left(tree_model) => {
                let { tree: tree } = unfold(input);
                have separate(tree, memory(augment->propagate)) by known();
                have separate(tree, memory(augment->copy)) by known();
                have separate(tree, memory(augment->rotate)) by known();
                apply(separate_from_sized_callback_reads(augment as (const int32 *), tree));
                let { checked: checked } = step(RotateTreeLeft, { tree: tree });
                have sized_rotation_input_tree(old(input.model)) == tree_model by {
                    rewrite(old(input.model), SizedRotationInput::Left(tree_model));
                    unfold(sized_rotation_input_tree(SizedRotationInput::Left(tree_model)));
                    normalize();
                }
                step_until(function.exit);
            },
            SizedRotationInput::Right(tree_model) => {
                let { tree: tree } = unfold(input);
                have separate(tree, memory(augment->propagate)) by known();
                have separate(tree, memory(augment->copy)) by known();
                have separate(tree, memory(augment->rotate)) by known();
                apply(separate_from_sized_callback_reads(augment as (const int32 *), tree));
                let { checked: checked } = step(RotateTreeRight, { tree: tree });
                have sized_rotation_input_tree(old(input.model)) == tree_model by {
                    rewrite(old(input.model), SizedRotationInput::Right(tree_model));
                    unfold(sized_rotation_input_tree(SizedRotationInput::Right(tree_model)));
                    normalize();
                }
                step_until(function.exit);
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
        let input = fold(sized_rotation_input_at(old, new), { model: SizedRotationInput::Left(tree.model), tree: tree });
        with(sized_callback_table(augment)) {
            have separate(input, memory(augment->propagate)) by known();
            have separate(input, memory(augment->copy)) by known();
            have separate(input, memory(augment->rotate)) by known();
            apply(separate_from_sized_callback_reads(augment as (const int32 *), input));
        }
        let { checked: checked } = step(sized_rotate_from_table, { input: input });
        have sized_rotation_input_tree(SizedRotationInput::Left(old(tree.model))) == old(tree.model) by {
            unfold(sized_rotation_input_tree(SizedRotationInput::Left(old(tree.model))));
            normalize();
        }
        solve();
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
        let input = fold(sized_rotation_input_at(old, new), { model: SizedRotationInput::Right(tree.model), tree: tree });
        with(sized_callback_table(augment)) {
            have separate(input, memory(augment->propagate)) by known();
            have separate(input, memory(augment->copy)) by known();
            have separate(input, memory(augment->rotate)) by known();
            apply(separate_from_sized_callback_reads(augment as (const int32 *), input));
        }
        let { checked: checked } = step(sized_rotate_from_table, { input: input });
        have sized_rotation_input_tree(SizedRotationInput::Right(old(tree.model))) == old(tree.model) by {
            unfold(sized_rotation_input_tree(SizedRotationInput::Right(old(tree.model))));
            normalize();
        }
        solve();
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
    with(sized_callback_table(augment)) {
        have separate(walk, memory(augment->propagate)) by known();
        have separate(walk, memory(augment->copy)) by known();
        have separate(walk, memory(augment->rotate)) by known();
        apply(separate_from_sized_callback_reads(augment as (const int32 *), walk));
        let { whole: whole } = step(PropagateTree, { walk: walk });
        step_until(function.exit);
    }
}
