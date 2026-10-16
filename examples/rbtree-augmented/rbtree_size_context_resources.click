// Owned ancestor frames used when propagation stops without further writes.
verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_context.click";

function sized_context_parent(ctx: SizedContext, stop: struct rb_node*) -> struct rb_node* {
    match ctx {
        SizedContext::Top => stop,
        SizedContext::Left(node, parent, color, value, sibling, up) => node,
        SizedContext::Right(node, parent, color, value, sibling, up) => node,
    }
}

resource sized_context_at(child: struct rb_node*, root: struct rb_node*,
                          stop: struct rb_node*, previous: int32) {
    field model: SizedContext;
    match model {
        SizedContext::Top => { fact child == root; },
        SizedContext::Left(node, parent, color, value, sibling_model, up_model) => {
            owns node->__rb_parent_color;
            owns node->rb_left;
            owns node->rb_right;
            owns metadata: size_metadata(node);
            owns sibling: sized_at(node->rb_right);
            owns up: sized_context_at(node, root, stop, value);
            fact node != 0;
            fact address(node) != address(stop);
            fact node->rb_left == child;
            fact node->rb_left != node;
            fact node->rb_right != node;
            fact aligned(node, 8);
            fact aligned(parent, 8);
            fact node->__rb_parent_color == address(parent) + (node->__rb_parent_color & 1);
            fact (node->__rb_parent_color & 1) == color_bit(color);
            fact metadata.value == value;
            fact sibling.model == sibling_model;
            fact up.model == up_model;
            fact sized_parent_is(sibling_model, node) == 1;
            fact parent == sized_context_parent(up_model, stop);
            fact to_integer(value) == 1 + to_integer(previous) + to_integer(sized_value(sibling_model));
        },
        SizedContext::Right(node, parent, color, value, sibling_model, up_model) => {
            owns node->__rb_parent_color;
            owns node->rb_left;
            owns node->rb_right;
            owns metadata: size_metadata(node);
            owns sibling: sized_at(node->rb_left);
            owns up: sized_context_at(node, root, stop, value);
            fact node != 0;
            fact address(node) != address(stop);
            fact node->rb_right == child;
            fact node->rb_left != node;
            fact node->rb_right != node;
            fact aligned(node, 8);
            fact aligned(parent, 8);
            fact node->__rb_parent_color == address(parent) + (node->__rb_parent_color & 1);
            fact (node->__rb_parent_color & 1) == color_bit(color);
            fact metadata.value == value;
            fact sibling.model == sibling_model;
            fact up.model == up_model;
            fact sized_parent_is(sibling_model, node) == 1;
            fact parent == sized_context_parent(up_model, stop);
            fact to_integer(value) == 1 + to_integer(sized_value(sibling_model)) + to_integer(previous);
        },
    }
}

// The focused subtree's unchanged cached size lets every ancestor refold with
// its existing metadata. Ancestor frames end before the stop node.
tactic restore_sized_context(child: struct rb_node*, root: struct rb_node*,
                             stop: struct rb_node*, previous: int32) {
    consumes path: sized_context_at(child, root, stop, previous);
    consumes sub: sized_at(child);
    requires sized_value(sub.model) == previous;
    requires sized_parent_is(sub.model, sized_context_parent(path.model, stop)) == 1;
    decreases sized_context_depth(path.model);
    produces whole: sized_at(root);
    ensures whole.model == sized_plug(old(path.model), old(sub.model));
    ensures sized_parent_is(whole.model, stop) == 1;
} by {
    match path.model {
        SizedContext::Top => {
            unfold(path);
            unfold(sized_context_parent(SizedContext::Top, stop));
            have sized_context_parent(SizedContext::Top, stop) == stop by {
                unfold(sized_context_parent(SizedContext::Top, stop)); normalize();
            }
            have sized_parent_is(sub.model, stop) == 1 by {
                rewrite(stop == sized_context_parent(SizedContext::Top, stop));
                rewrite(SizedContext::Top == old(path.model));
                assumption();
            }
            match sub.model {
                SizedTree::Empty => {
                    unfold(sub);
                    let whole = fold(sized_at(root), { model: SizedTree::Empty });
                    unfold(sized_plug(SizedContext::Top, SizedTree::Empty));
                    have whole.model == sized_plug(old(path.model), old(sub.model)) by { simp(); }
                    have sized_parent_is(whole.model, stop) == 1 by {
                        rewrite(whole.model == SizedTree::Empty);
                        unfold(sized_parent_is(SizedTree::Empty, stop)); normalize();
                    }
                },
                SizedTree::Node(node, parent, color, value, left_model, right_model) => {
                    let { metadata: metadata, left: left, right: right } = unfold(sub);
                    let whole = fold(sized_at(root), { model: SizedTree::Node(node, parent, color, value, left_model, right_model) }, { metadata: metadata, left: left, right: right });
                    unfold(sized_plug(SizedContext::Top, SizedTree::Node(node, parent, color, value, left_model, right_model)));
                    have whole.model == sized_plug(old(path.model), old(sub.model)) by { simp(); }
                    have sized_parent_is(whole.model, stop) == 1 by {
                        rewrite(whole.model == SizedTree::Node(node, parent, color, value, left_model, right_model));
                        rewrite(SizedTree::Node(node, parent, color, value, left_model, right_model) == old(sub.model));
                        assumption();
                    }
                },
            }
        },
        SizedContext::Left(node, parent, color, value, sibling_model, up_model) => {
            unfold(sized_context_parent(SizedContext::Left(node, parent, color, value, sibling_model, up_model), stop));
            have sized_context_parent(SizedContext::Left(node, parent, color, value, sibling_model, up_model), stop) == node by {
                unfold(sized_context_parent(SizedContext::Left(node, parent, color, value, sibling_model, up_model), stop)); normalize();
            }
            have sized_parent_is(sub.model, node) == 1 by {
                rewrite(node == sized_context_parent(SizedContext::Left(node, parent, color, value, sibling_model, up_model), stop));
                rewrite(SizedContext::Left(node, parent, color, value, sibling_model, up_model) == path.model);
                assumption();
            }
            let { metadata: metadata, sibling: sibling, up: up } = unfold(path);
            have to_integer(value) == 1 + to_integer(sized_value(old(sub.model))) + to_integer(sized_value(sibling_model)) by {
                rewrite(sized_value(old(sub.model)) == previous);
                assumption();
            }
            let lifted = fold(sized_at(node), { model: SizedTree::Node(node, parent, color, value, old(sub.model), sibling_model) }, { metadata: metadata, left: sub, right: sibling });
            have sized_value(lifted.model) == value by {
                rewrite(lifted.model == SizedTree::Node(node, parent, color, value, old(sub.model), sibling_model));
                unfold(sized_value(SizedTree::Node(node, parent, color, value, old(sub.model), sibling_model))); normalize();
            }
            have sized_parent_is(lifted.model, sized_context_parent(up.model, stop)) == 1 by {
                rewrite(lifted.model == SizedTree::Node(node, parent, color, value, old(sub.model), sibling_model));
                rewrite(up.model == up_model);
                unfold(sized_parent_is(SizedTree::Node(node, parent, color, value, old(sub.model), sibling_model), sized_context_parent(up_model, stop)));
                normalize() using { parent == sized_context_parent(up_model, stop); };
            }
            apply(sized_context_depth_nonnegative(up_model));
            have 0 <= sized_context_depth(up.model) by { rewrite(up.model == up_model); assumption(); }
            have sized_context_depth(old(path.model)) == sized_context_depth(up_model) + 1 by {
                rewrite(old(path.model) == SizedContext::Left(node, parent, color, value, sibling_model, up_model));
                unfold(sized_context_depth(SizedContext::Left(node, parent, color, value, sibling_model, up_model))); normalize();
            }
            have sized_context_depth(up.model) < sized_context_depth(old(path.model)) by {
                rewrite(up.model == up_model);
                arithmetic() using { sized_context_depth(old(path.model)) == sized_context_depth(up_model) + 1; };
            }
            have sized_plug(SizedContext::Left(node, parent, color, value, sibling_model, up_model), old(sub.model)) == sized_plug(up_model, SizedTree::Node(node, parent, color, value, old(sub.model), sibling_model)) by {
                unfold(sized_plug(SizedContext::Left(node, parent, color, value, sibling_model, up_model), old(sub.model))); normalize();
            }
            let { whole: whole } = restore_sized_context(node, root, stop, value, { path: up, sub: lifted });
            have whole.model == sized_plug(old(path.model), old(sub.model)) by {
                rewrite(old(path.model) == SizedContext::Left(node, parent, color, value, sibling_model, up_model));
                rewrite(sized_plug(SizedContext::Left(node, parent, color, value, sibling_model, up_model), old(sub.model)) == sized_plug(up_model, SizedTree::Node(node, parent, color, value, old(sub.model), sibling_model)));
                simp();
            }
            have sized_parent_is(whole.model, stop) == 1 by { assumption(); }
        },
        SizedContext::Right(node, parent, color, value, sibling_model, up_model) => {
            unfold(sized_context_parent(SizedContext::Right(node, parent, color, value, sibling_model, up_model), stop));
            have sized_context_parent(SizedContext::Right(node, parent, color, value, sibling_model, up_model), stop) == node by {
                unfold(sized_context_parent(SizedContext::Right(node, parent, color, value, sibling_model, up_model), stop)); normalize();
            }
            have sized_parent_is(sub.model, node) == 1 by {
                rewrite(node == sized_context_parent(SizedContext::Right(node, parent, color, value, sibling_model, up_model), stop));
                rewrite(SizedContext::Right(node, parent, color, value, sibling_model, up_model) == path.model);
                assumption();
            }
            let { metadata: metadata, sibling: sibling, up: up } = unfold(path);
            have to_integer(value) == 1 + to_integer(sized_value(sibling_model)) + to_integer(sized_value(old(sub.model))) by {
                rewrite(sized_value(old(sub.model)) == previous);
                assumption();
            }
            let lifted = fold(sized_at(node), { model: SizedTree::Node(node, parent, color, value, sibling_model, old(sub.model)) }, { metadata: metadata, left: sibling, right: sub });
            have sized_value(lifted.model) == value by {
                rewrite(lifted.model == SizedTree::Node(node, parent, color, value, sibling_model, old(sub.model)));
                unfold(sized_value(SizedTree::Node(node, parent, color, value, sibling_model, old(sub.model)))); normalize();
            }
            have sized_parent_is(lifted.model, sized_context_parent(up.model, stop)) == 1 by {
                rewrite(lifted.model == SizedTree::Node(node, parent, color, value, sibling_model, old(sub.model)));
                rewrite(up.model == up_model);
                unfold(sized_parent_is(SizedTree::Node(node, parent, color, value, sibling_model, old(sub.model)), sized_context_parent(up_model, stop)));
                normalize() using { parent == sized_context_parent(up_model, stop); };
            }
            apply(sized_context_depth_nonnegative(up_model));
            have 0 <= sized_context_depth(up.model) by { rewrite(up.model == up_model); assumption(); }
            have sized_context_depth(old(path.model)) == sized_context_depth(up_model) + 1 by {
                rewrite(old(path.model) == SizedContext::Right(node, parent, color, value, sibling_model, up_model));
                unfold(sized_context_depth(SizedContext::Right(node, parent, color, value, sibling_model, up_model))); normalize();
            }
            have sized_context_depth(up.model) < sized_context_depth(old(path.model)) by {
                rewrite(up.model == up_model);
                arithmetic() using { sized_context_depth(old(path.model)) == sized_context_depth(up_model) + 1; };
            }
            have sized_plug(SizedContext::Right(node, parent, color, value, sibling_model, up_model), old(sub.model)) == sized_plug(up_model, SizedTree::Node(node, parent, color, value, sibling_model, old(sub.model))) by {
                unfold(sized_plug(SizedContext::Right(node, parent, color, value, sibling_model, up_model), old(sub.model))); normalize();
            }
            let { whole: whole } = restore_sized_context(node, root, stop, value, { path: up, sub: lifted });
            have whole.model == sized_plug(old(path.model), old(sub.model)) by {
                rewrite(old(path.model) == SizedContext::Right(node, parent, color, value, sibling_model, up_model));
                rewrite(sized_plug(SizedContext::Right(node, parent, color, value, sibling_model, up_model), old(sub.model)) == sized_plug(up_model, SizedTree::Node(node, parent, color, value, sibling_model, old(sub.model))));
                simp();
            }
            have sized_parent_is(whole.model, stop) == 1 by { assumption(); }
        },
    }
}

// The public path carries its reconstruction root in its owned model, without
// adding a C parameter to the Linux callback.
spec enum SizedPath {
    Path(struct rb_node*, SizedContext),
}

function sized_path_root(path: SizedPath) -> struct rb_node* {
    match path { SizedPath::Path(root, context) => root, }
}

function sized_path_context(path: SizedPath) -> SizedContext {
    match path { SizedPath::Path(root, context) => context, }
}

resource sized_path_at(child: struct rb_node*, stop: struct rb_node*, previous: int32) {
    field model: SizedPath;
    match model {
        SizedPath::Path(root, context) => {
            owns frames: sized_context_at(child, root, stop, previous);
            fact frames.model == context;
        },
    }
}

spec enum SizedResult {
    Tree(struct rb_node*, SizedTree),
}

function sized_result_root(result: SizedResult) -> struct rb_node* {
    match result { SizedResult::Tree(root, tree) => root, }
}

function sized_result_tree(result: SizedResult) -> SizedTree {
    match result { SizedResult::Tree(root, tree) => tree, }
}

resource sized_result_at(stop: struct rb_node*) {
    field model: SizedResult;
    match model {
        SizedResult::Tree(root, tree_model) => {
            owns tree: sized_at(root);
            fact tree.model == tree_model;
            fact sized_parent_is(tree_model, stop) == 1;
        },
    }
}

tactic restore_sized_path(child: struct rb_node*, stop: struct rb_node*, previous: int32) {
    consumes path: sized_path_at(child, stop, previous);
    consumes sub: sized_at(child);
    requires sized_value(sub.model) == previous;
    requires sized_parent_is(sub.model, sized_context_parent(sized_path_context(path.model), stop)) == 1;
    produces whole: sized_result_at(stop);
    ensures sized_result_root(whole.model) == sized_path_root(old(path.model));
    ensures sized_result_tree(whole.model) == sized_plug(sized_path_context(old(path.model)), old(sub.model));
} by {
    match path.model {
        SizedPath::Path(root, context) => {
            unfold(sized_path_root(SizedPath::Path(root, context)));
            unfold(sized_path_context(SizedPath::Path(root, context)));
            have sized_path_context(path.model) == context by {
                rewrite(path.model == SizedPath::Path(root, context));
                unfold(sized_path_context(SizedPath::Path(root, context))); normalize();
            }
            let { frames: frames } = unfold(path);
            have sized_parent_is(sub.model, sized_context_parent(frames.model, stop)) == 1 by {
                rewrite(frames.model == context);
                rewrite(context == sized_path_context(old(path.model)));
                assumption();
            }
            let { whole: repaired } = restore_sized_context(child, root, stop, previous, { path: frames, sub: sub });
            have repaired.model == sized_plug(context, old(sub.model)) by { simp(); }
            have sized_parent_is(sized_plug(context, old(sub.model)), stop) == 1 by {
                rewrite(sized_plug(context, old(sub.model)) == repaired.model);
                assumption();
            }
            let whole = fold(sized_result_at(stop), { model: SizedResult::Tree(root, sized_plug(context, old(sub.model))) }, { tree: repaired });
            unfold(sized_result_root(SizedResult::Tree(root, sized_plug(context, old(sub.model)))));
            unfold(sized_result_tree(SizedResult::Tree(root, sized_plug(context, old(sub.model)))));
            have sized_result_root(whole.model) == sized_path_root(old(path.model)) by {
                rewrite(whole.model == SizedResult::Tree(root, sized_plug(context, old(sub.model))));
                rewrite(old(path.model) == SizedPath::Path(root, context));
                unfold(sized_result_root(SizedResult::Tree(root, sized_plug(context, old(sub.model)))));
                unfold(sized_path_root(SizedPath::Path(root, context)));
                normalize();
            }
            have sized_result_tree(whole.model) == sized_plug(sized_path_context(old(path.model)), old(sub.model)) by {
                rewrite(whole.model == SizedResult::Tree(root, sized_plug(context, old(sub.model))));
                rewrite(old(path.model) == SizedPath::Path(root, context));
                unfold(sized_result_tree(SizedResult::Tree(root, sized_plug(context, old(sub.model)))));
                unfold(sized_path_context(SizedPath::Path(root, context)));
                normalize();
            }
        },
    }
}

// Expose the model's cached-count coherence without changing ancestor memory.
tactic certify_sized_context(child: struct rb_node*, root: struct rb_node*,
                             stop: struct rb_node*, previous: int32) {
    consumes path: sized_context_at(child, root, stop, previous);
    decreases sized_context_depth(path.model);
    produces checked: sized_context_at(child, root, stop, previous);
    ensures checked.model == old(path.model);
    ensures sized_context_valid(checked.model, to_integer(previous)) == 1;
} by {
    match path.model {
        SizedContext::Top => {
            unfold(path);
            let checked = fold(sized_context_at(child, root, stop, previous), { model: SizedContext::Top });
            have checked.model == old(path.model) by { assumption(); }
            have sized_context_valid(checked.model, to_integer(previous)) == 1 by {
                rewrite(checked.model == SizedContext::Top);
                unfold(sized_context_valid(SizedContext::Top, to_integer(previous)));
                normalize();
            }
        },
        SizedContext::Left(node, parent, color, value, sibling_model, up_model) => {
            let { metadata: metadata, sibling: sibling, up: up } = unfold(path);
            apply(sized_context_depth_nonnegative(up_model));
            have 0 <= sized_context_depth(up.model) by { rewrite(up.model == up_model); assumption(); }
            have sized_context_depth(old(path.model)) == sized_context_depth(up_model) + 1 by {
                rewrite(old(path.model) == SizedContext::Left(node, parent, color, value, sibling_model, up_model));
                unfold(sized_context_depth(SizedContext::Left(node, parent, color, value, sibling_model, up_model))); normalize();
            }
            have sized_context_depth(up.model) < sized_context_depth(old(path.model)) by {
                rewrite(up.model == up_model);
                arithmetic() using { sized_context_depth(old(path.model)) == sized_context_depth(up_model) + 1; };
            }
            let { checked: sibling } = certify_size(node->rb_right, { tree: sibling });
            let { checked: up } = certify_sized_context(node, root, stop, value, { path: up });
            have sized_counts_valid(sibling_model) == 1 by { rewrite(sibling_model == sibling.model); assumption(); }
            have sized_context_valid(up_model, to_integer(value)) == 1 by { rewrite(up_model == up.model); assumption(); }
            have sized_context_valid(SizedContext::Left(node, parent, color, value, sibling_model, up_model), to_integer(previous)) == 1 by {
                unfold(sized_context_valid(SizedContext::Left(node, parent, color, value, sibling_model, up_model), to_integer(previous)));
                normalize() using {
                    to_integer(value) == 1 + to_integer(previous) + to_integer(sized_value(sibling_model));
                    sized_counts_valid(sibling_model) == 1;
                    sized_context_valid(up_model, to_integer(value)) == 1;
                };
            }
            let checked = fold(sized_context_at(child, root, stop, previous), { model: SizedContext::Left(node, parent, color, value, sibling_model, up_model) }, { metadata: metadata, sibling: sibling, up: up });
            have checked.model == old(path.model) by { assumption(); }
        },
        SizedContext::Right(node, parent, color, value, sibling_model, up_model) => {
            let { metadata: metadata, sibling: sibling, up: up } = unfold(path);
            apply(sized_context_depth_nonnegative(up_model));
            have 0 <= sized_context_depth(up.model) by { rewrite(up.model == up_model); assumption(); }
            have sized_context_depth(old(path.model)) == sized_context_depth(up_model) + 1 by {
                rewrite(old(path.model) == SizedContext::Right(node, parent, color, value, sibling_model, up_model));
                unfold(sized_context_depth(SizedContext::Right(node, parent, color, value, sibling_model, up_model))); normalize();
            }
            have sized_context_depth(up.model) < sized_context_depth(old(path.model)) by {
                rewrite(up.model == up_model);
                arithmetic() using { sized_context_depth(old(path.model)) == sized_context_depth(up_model) + 1; };
            }
            let { checked: sibling } = certify_size(node->rb_left, { tree: sibling });
            let { checked: up } = certify_sized_context(node, root, stop, value, { path: up });
            have sized_counts_valid(sibling_model) == 1 by { rewrite(sibling_model == sibling.model); assumption(); }
            have sized_context_valid(up_model, to_integer(value)) == 1 by { rewrite(up_model == up.model); assumption(); }
            have sized_context_valid(SizedContext::Right(node, parent, color, value, sibling_model, up_model), to_integer(previous)) == 1 by {
                unfold(sized_context_valid(SizedContext::Right(node, parent, color, value, sibling_model, up_model), to_integer(previous)));
                normalize() using {
                    to_integer(value) == 1 + to_integer(sized_value(sibling_model)) + to_integer(previous);
                    sized_counts_valid(sibling_model) == 1;
                    sized_context_valid(up_model, to_integer(value)) == 1;
                };
            }
            let checked = fold(sized_context_at(child, root, stop, previous), { model: SizedContext::Right(node, parent, color, value, sibling_model, up_model) }, { metadata: metadata, sibling: sibling, up: up });
            have checked.model == old(path.model) by { assumption(); }
            have sized_context_valid(checked.model, to_integer(previous)) == 1 by {
                rewrite(checked.model == SizedContext::Right(node, parent, color, value, sibling_model, up_model)); assumption();
            }
        },
    }
}
