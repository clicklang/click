arithmetic "integer";

// A black-parent exit restores any sized subtree through its owned context.
verifying "rb_insert_augmented.c" as insert;
verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_context_resources.click";

function sized_stop_parent_black(ctx: SizedContext) -> int32 {
    match ctx {
        SizedContext::Top => 0,
        SizedContext::Left(node, parent, color, value, sibling, up) => color_bit(color),
        SizedContext::Right(node, parent, color, value, sibling, up) => color_bit(color),
    }
}
resource sized_stop_at(node: struct rb_node*, root: struct rb_root*) {
    field model: SizedTree;
    field context: SizedContext;
    match model {
        SizedTree::Empty => { fact 0 == 1; },
        SizedTree::Node(identity, ancestor, shade, value, left_model, right_model) => {
            owns root->rb_node;
            owns tree: sized_at(node);
            owns path: sized_context_at(node, root->rb_node, 0, value);
            fact tree.model == model;
            fact path.model == context;
            fact identity == node;
            fact ancestor == sized_context_parent(context, 0);
            fact shade == Color::Red;
            fact sized_stop_parent_black(context) == 1;
        },
    }
}

void insert::__rb_insert(struct rb_node* node, struct rb_root* root,
                        void (*augment_rotate)(struct rb_node*, struct rb_node*)) {
    consumes state: sized_stop_at(node, root);
    produces root->rb_node;
    produces whole: sized_at(root->rb_node);
    ensures whole.model == sized_plug(old(state.context), old(state.model));
    ensures sized_parent_is(whole.model, 0) == 1;
} by {
    match state.model {
        SizedTree::Empty => { unfold(state); contradiction(0 == 1); },
        SizedTree::Node(identity, ancestor, original_shade, value, left_model, right_model) => {
            let { tree: tree, path: path } = unfold(state);
            have path.model == old(state.context) by { normalize(); }
            have tree.model == old(state.model) by { normalize(); }
            match path.model {
                SizedContext::Top => {
                    have sized_stop_parent_black(path.model) != 1 by {
                        rewrite(path.model == SizedContext::Top);
                        unfold(sized_stop_parent_black(SizedContext::Top)); normalize();
                    }
                    contradiction(sized_stop_parent_black(path.model) == 1);
                },
                SizedContext::Left(a, above, shade, count, sibling_model, up_model) => {
                    have sized_context_parent(path.model, 0) == a by {
                        rewrite(path.model == SizedContext::Left(a, above, shade, count, sibling_model, up_model));
                        unfold(sized_context_parent(SizedContext::Left(a, above, shade, count, sibling_model, up_model), 0)); normalize();
                    }
                    have ancestor == a by { assumption(); }
                    have color_bit(shade) == 1 by {
                        unfold(sized_stop_parent_black(SizedContext::Left(a, above, shade, count, sibling_model, up_model)));
                        rewrite(color_bit(shade) == sized_stop_parent_black(SizedContext::Left(a, above, shade, count, sibling_model, up_model)));
                        rewrite(SizedContext::Left(a, above, shade, count, sibling_model, up_model) == path.model); assumption();
                    }
                    have tree.model == SizedTree::Node(node, a, Color::Red, value, left_model, right_model) by {
                        rewrite(node == identity);
                        rewrite(a == ancestor);
                        rewrite(Color::Red == original_shade); assumption();
                    }
                    let { metadata: metadata, left: left, right: right } = unfold(tree);
                    unfold(color_bit(Color::Red));
                    have node->__rb_parent_color == address(a) by {
                        rewrite(node->__rb_parent_color == address(a) + (node->__rb_parent_color & 1));
                        rewrite((node->__rb_parent_color & 1) == color_bit(Color::Red));
                        rewrite(color_bit(Color::Red) == 0); normalize();
                    }
                    step(); step(); step(); step();
                    let tree = fold(sized_at(node), { model: old(state.model) }, { metadata: metadata, left: left, right: right });
                    let state = fold(sized_stop_at(node, root), { model: old(state.model), context: old(state.context) }, { tree: tree, path: path });
                    loop {
                        owns state: sized_stop_at(node, root);
                        decreases 0;
                        invariant node == old(node);
                        invariant parent == a;
                        invariant state.model == old(state.model);
                        invariant state.context == old(state.context);
                        invariant state.context == SizedContext::Left(a, above, shade, count, sibling_model, up_model);
                        invariant color_bit(shade) == 1;
                        initialize by simp();
                        preserve by {
                            let { tree: tree, path: path } = unfold(state);
                            let { metadata: parent_size, sibling: sibling, up: up } = unfold(path);
                            have (a->__rb_parent_color & 1) == 1 by {
                                rewrite((a->__rb_parent_color & 1) == color_bit(shade));
                                rewrite(color_bit(shade) == 1); normalize();
                            }
                            step(); step(); step();
                            let path = fold(sized_context_at(node, root->rb_node, 0, value), { model: old(state.context) }, { metadata: parent_size, sibling: sibling, up: up });
                            let state = fold(sized_stop_at(node, root), { model: old(state.model), context: old(state.context) }, { tree: tree, path: path });
                            step();
                        }
                    }
                    let { tree: tree, path: path } = unfold(state);
                    have node == old(node) by { assumption(); }
                    have sized_parent_is(tree.model, sized_context_parent(path.model, 0)) == 1 by {
                        rewrite(tree.model == SizedTree::Node(node, a, Color::Red, value, left_model, right_model));
                        unfold(sized_parent_is(SizedTree::Node(node, a, Color::Red, value, left_model, right_model), sized_context_parent(path.model, 0)));
                        normalize() using { sized_context_parent(path.model, 0) == a; };
                    }
                    have sized_value(tree.model) == value by {
                        rewrite(tree.model == SizedTree::Node(node, a, Color::Red, value, left_model, right_model));
                        unfold(sized_value(SizedTree::Node(node, a, Color::Red, value, left_model, right_model))); normalize();
                    }
                    let { whole: whole } = restore_sized_context(node, root->rb_node, 0, value, { path: path, sub: tree });
                    have whole.model == sized_plug(old(state.context), old(state.model)) by { assumption(); }
                    execute();
                },
                SizedContext::Right(a, above, shade, count, sibling_model, up_model) => {
                    have sized_context_parent(path.model, 0) == a by {
                        rewrite(path.model == SizedContext::Right(a, above, shade, count, sibling_model, up_model));
                        unfold(sized_context_parent(SizedContext::Right(a, above, shade, count, sibling_model, up_model), 0)); normalize();
                    }
                    have ancestor == a by { assumption(); }
                    have color_bit(shade) == 1 by {
                        unfold(sized_stop_parent_black(SizedContext::Right(a, above, shade, count, sibling_model, up_model)));
                        rewrite(color_bit(shade) == sized_stop_parent_black(SizedContext::Right(a, above, shade, count, sibling_model, up_model)));
                        rewrite(SizedContext::Right(a, above, shade, count, sibling_model, up_model) == path.model); assumption();
                    }
                    have tree.model == SizedTree::Node(node, a, Color::Red, value, left_model, right_model) by {
                        rewrite(node == identity);
                        rewrite(a == ancestor);
                        rewrite(Color::Red == original_shade); assumption();
                    }
                    let { metadata: metadata, left: left, right: right } = unfold(tree);
                    unfold(color_bit(Color::Red));
                    have node->__rb_parent_color == address(a) by {
                        rewrite(node->__rb_parent_color == address(a) + (node->__rb_parent_color & 1));
                        rewrite((node->__rb_parent_color & 1) == color_bit(Color::Red));
                        rewrite(color_bit(Color::Red) == 0); normalize();
                    }
                    step(); step(); step(); step();
                    let tree = fold(sized_at(node), { model: old(state.model) }, { metadata: metadata, left: left, right: right });
                    let state = fold(sized_stop_at(node, root), { model: old(state.model), context: old(state.context) }, { tree: tree, path: path });
                    loop {
                        owns state: sized_stop_at(node, root);
                        decreases 0;
                        invariant node == old(node);
                        invariant parent == a;
                        invariant state.model == old(state.model);
                        invariant state.context == old(state.context);
                        invariant state.context == SizedContext::Right(a, above, shade, count, sibling_model, up_model);
                        invariant color_bit(shade) == 1;
                        initialize by simp();
                        preserve by {
                            let { tree: tree, path: path } = unfold(state);
                            let { metadata: parent_size, sibling: sibling, up: up } = unfold(path);
                            have (a->__rb_parent_color & 1) == 1 by {
                                rewrite((a->__rb_parent_color & 1) == color_bit(shade));
                                rewrite(color_bit(shade) == 1); normalize();
                            }
                            step(); step(); step();
                            let path = fold(sized_context_at(node, root->rb_node, 0, value), { model: old(state.context) }, { metadata: parent_size, sibling: sibling, up: up });
                            let state = fold(sized_stop_at(node, root), { model: old(state.model), context: old(state.context) }, { tree: tree, path: path });
                            step();
                        }
                    }
                    let { tree: tree, path: path } = unfold(state);
                    have node == old(node) by { assumption(); }
                    have sized_parent_is(tree.model, sized_context_parent(path.model, 0)) == 1 by {
                        rewrite(tree.model == SizedTree::Node(node, a, Color::Red, value, left_model, right_model));
                        unfold(sized_parent_is(SizedTree::Node(node, a, Color::Red, value, left_model, right_model), sized_context_parent(path.model, 0)));
                        normalize() using { sized_context_parent(path.model, 0) == a; };
                    }
                    have sized_value(tree.model) == value by {
                        rewrite(tree.model == SizedTree::Node(node, a, Color::Red, value, left_model, right_model));
                        unfold(sized_value(SizedTree::Node(node, a, Color::Red, value, left_model, right_model))); normalize();
                    }
                    let { whole: whole } = restore_sized_context(node, root->rb_node, 0, value, { path: path, sub: tree });
                    have whole.model == sized_plug(old(state.context), old(state.model)) by { assumption(); }
                    execute();
                },
            }
        },
    }
}

void insert::__rb_insert_augmented(struct rb_node* node, struct rb_root* root,
                        void (*augment_rotate)(struct rb_node*, struct rb_node*)) {
    consumes state: sized_stop_at(node, root);
    produces root->rb_node;
    produces whole: sized_at(root->rb_node);
    ensures whole.model == sized_plug(old(state.context), old(state.model));
    ensures sized_parent_is(whole.model, 0) == 1;
} by {
    let { whole: whole } = step(insert::__rb_insert(node, root, augment_rotate), { state: state });
    execute(); simp();
}

void insert::rb_insert_augmented(struct rb_node* node, struct rb_root* root,
                         const struct rb_augment_callbacks* augment) {
    views augment->rotate;
    consumes state: sized_stop_at(node, root);
    produces root->rb_node;
    produces whole: sized_at(root->rb_node);
    ensures whole.model == sized_plug(old(state.context), old(state.model));
    ensures sized_parent_is(whole.model, 0) == 1;
} by {
    let { whole: whole } = step(insert::__rb_insert_augmented(node, root, augment->rotate), { state: state });
    execute(); simp();
}
