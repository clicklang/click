// Ownership transitions for the unchanged propagation callback.
verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_recompute_model.click";
import "rbtree_size_context_resources.click";

spec enum SizedWalk {
    Active(int32, SizedTree, SizedPath),
    Done(SizedResult),
}

function sized_walk_pending(walk: SizedWalk) -> int32 {
    match walk {
        SizedWalk::Active(previous, sub, path) => 1,
        SizedWalk::Done(whole) => 0,
    }
}

function sized_walk_root(walk: SizedWalk) -> struct rb_node* {
    match walk {
        SizedWalk::Active(previous, sub, path) => sized_path_root(path),
        SizedWalk::Done(whole) => sized_result_root(whole),
    }
}

function sized_walk_tree(walk: SizedWalk) -> SizedTree {
    match walk {
        SizedWalk::Active(previous, sub, path) => sized_plug(sized_path_context(path), sub),
        SizedWalk::Done(whole) => sized_result_tree(whole),
    }
}

function sized_walk_rank(walk: SizedWalk) -> Integer {
    match walk {
        SizedWalk::Active(previous, sub, path) => sized_context_depth(sized_path_context(path)) + 1,
        SizedWalk::Done(whole) => 0,
    }
}

resource sized_walk_at(rb: struct rb_node*, stop: struct rb_node*) {
    field model: SizedWalk;
    match model {
        SizedWalk::Active(previous, sub_model, path_model) => {
            owns focus: sized_recompute_at(rb);
            owns path: sized_path_at(rb, stop, previous);
            fact rb != 0;
            fact rb != stop;
            fact focus.model == sub_model;
            fact path.model == path_model;
            fact sized_value(sub_model) == previous;
            fact sized_parent_is(sub_model, sized_context_parent(sized_path_context(path_model), stop)) == 1;
        },
        SizedWalk::Done(result_model) => {
            owns whole: sized_result_at(stop);
            fact whole.model == result_model;
        },
    }
}

// Move the repaired focus into its parent, retaining the parent's old cache
// and the untouched sibling. At the top frame, the whole tree is repaired.
tactic advance_sized_path(child: struct rb_node*, parent_node: struct rb_node*,
                         stop: struct rb_node*, previous: int32) {
    consumes sub: sized_at(child);
    consumes path: sized_path_at(child, stop, previous);
    requires child != 0;
    requires parent_node == sized_context_parent(sized_path_context(path.model), stop);
    requires sized_parent_is(sub.model, parent_node) == 1;
    produces next: sized_walk_at(parent_node, stop);
    ensures sized_walk_root(next.model) == sized_path_root(old(path.model));
    ensures sized_walk_tree(next.model) == sized_plug(sized_path_context(old(path.model)), old(sub.model));
    ensures sized_walk_rank(next.model) < sized_context_depth(sized_path_context(old(path.model))) + 1;
    ensures sized_walk_pending(next.model) == 1 or parent_node == stop;
    ensures 0 <= sized_walk_rank(next.model);
} by {
    match path.model {
        SizedPath::Path(root, context) => {
            let { frames: frames } = unfold(path);
            have sized_path_context(old(path.model)) == context by {
                rewrite(old(path.model) == SizedPath::Path(root, context));
                unfold(sized_path_context(SizedPath::Path(root, context))); normalize();
            }
            have parent_node == sized_context_parent(context, stop) by {
                rewrite(context == sized_path_context(old(path.model))); assumption();
            }
            match frames.model {
                SizedContext::Top => {
                    have sized_context_parent(context, stop) == stop by {
                        rewrite(context == SizedContext::Top);
                        unfold(sized_context_parent(SizedContext::Top, stop)); normalize();
                    }
                    have parent_node == stop by { assumption(); }
                    unfold(frames);
                    have sized_parent_is(old(sub.model), stop) == 1 by {
                        rewrite(stop == parent_node); assumption();
                    }
                    let whole = fold(sized_result_at(stop), { model: SizedResult::Tree(root, old(sub.model)) }, { tree: sub });
                    let next = fold(sized_walk_at(parent_node, stop), { model: SizedWalk::Done(SizedResult::Tree(root, old(sub.model))) }, { whole: whole });
                    have sized_walk_root(next.model) == sized_path_root(old(path.model)) by {
                        rewrite(next.model == SizedWalk::Done(SizedResult::Tree(root, old(sub.model))));
                        rewrite(old(path.model) == SizedPath::Path(root, context));
                        unfold(sized_walk_root(SizedWalk::Done(SizedResult::Tree(root, old(sub.model)))));
                        unfold(sized_path_root(SizedPath::Path(root, context)));
                        unfold(sized_result_root(SizedResult::Tree(root, old(sub.model))));
                        normalize();
                    }
                    have sized_walk_tree(next.model) == sized_plug(sized_path_context(old(path.model)), old(sub.model)) by {
                        rewrite(next.model == SizedWalk::Done(SizedResult::Tree(root, old(sub.model))));
                        rewrite(old(path.model) == SizedPath::Path(root, context));
                        unfold(sized_walk_tree(SizedWalk::Done(SizedResult::Tree(root, old(sub.model)))));
                        unfold(sized_path_context(SizedPath::Path(root, context)));
                        unfold(sized_result_tree(SizedResult::Tree(root, old(sub.model))));
                        rewrite(context == SizedContext::Top);
                        unfold(sized_plug(SizedContext::Top, old(sub.model)));
                        normalize();
                    }
                    have sized_walk_rank(next.model) < sized_context_depth(sized_path_context(old(path.model))) + 1 by {
                        rewrite(next.model == SizedWalk::Done(SizedResult::Tree(root, old(sub.model))));
                        rewrite(old(path.model) == SizedPath::Path(root, context));
                        unfold(sized_walk_rank(SizedWalk::Done(SizedResult::Tree(root, old(sub.model)))));
                        unfold(sized_path_context(SizedPath::Path(root, context)));

                        rewrite(context == SizedContext::Top);
                        unfold(sized_context_depth(SizedContext::Top));
                        normalize();
                    }
                    have sized_walk_pending(next.model) == 0 by {
                        rewrite(next.model == SizedWalk::Done(SizedResult::Tree(root, old(sub.model)))); unfold(sized_walk_pending(SizedWalk::Done(SizedResult::Tree(root, old(sub.model))))); normalize();
                    }
                    have sized_walk_pending(next.model) == 1 or parent_node == stop by { assumption(); }
                    have 0 <= sized_walk_rank(next.model) by {
                        rewrite(next.model == SizedWalk::Done(SizedResult::Tree(root, old(sub.model)))); unfold(sized_walk_rank(SizedWalk::Done(SizedResult::Tree(root, old(sub.model))))); normalize();
                    }
                },
                SizedContext::Left(node, parent, color, value, sibling_model, up_model) => {
                    have sized_context_parent(context, stop) == node by {
                        rewrite(context == SizedContext::Left(node, parent, color, value, sibling_model, up_model));
                        unfold(sized_context_parent(SizedContext::Left(node, parent, color, value, sibling_model, up_model), stop)); normalize();
                    }
                    have parent_node == node by { assumption(); }
                    let { metadata: metadata, sibling: sibling, up: up } = unfold(frames);
                    let focus = fold(sized_recompute_at(parent_node), { model: SizedTree::Node(node, parent, color, value, old(sub.model), sibling_model) }, { metadata: metadata, left: sub, right: sibling });
                    let remaining = fold(sized_path_at(parent_node, stop, value), { model: SizedPath::Path(root, up_model) }, { frames: up });
                    have sized_value(SizedTree::Node(node, parent, color, value, old(sub.model), sibling_model)) == value by { unfold(sized_value(SizedTree::Node(node, parent, color, value, old(sub.model), sibling_model))); normalize(); }
                    have sized_parent_is(SizedTree::Node(node, parent, color, value, old(sub.model), sibling_model), sized_context_parent(sized_path_context(SizedPath::Path(root, up_model)), stop)) == 1 by {
                        unfold(sized_path_context(SizedPath::Path(root, up_model)));
                        unfold(sized_parent_is(SizedTree::Node(node, parent, color, value, old(sub.model), sibling_model), sized_context_parent(up_model, stop)));
                        normalize() using { parent == sized_context_parent(up_model, stop); }
                    }
                    let next = fold(sized_walk_at(parent_node, stop), { model: SizedWalk::Active(value, SizedTree::Node(node, parent, color, value, old(sub.model), sibling_model), SizedPath::Path(root, up_model)) }, { focus: focus, path: remaining });
                    have sized_walk_root(next.model) == sized_path_root(old(path.model)) by {
                        rewrite(next.model == SizedWalk::Active(value, SizedTree::Node(node, parent, color, value, old(sub.model), sibling_model), SizedPath::Path(root, up_model)));
                        rewrite(old(path.model) == SizedPath::Path(root, context));
                        unfold(sized_walk_root(SizedWalk::Active(value, SizedTree::Node(node, parent, color, value, old(sub.model), sibling_model), SizedPath::Path(root, up_model))));
                        unfold(sized_path_root(SizedPath::Path(root, context)));
                        unfold(sized_path_root(SizedPath::Path(root, up_model)));
                        normalize();
                    }
                    have sized_walk_tree(next.model) == sized_plug(sized_path_context(old(path.model)), old(sub.model)) by {
                        rewrite(next.model == SizedWalk::Active(value, SizedTree::Node(node, parent, color, value, old(sub.model), sibling_model), SizedPath::Path(root, up_model)));
                        rewrite(old(path.model) == SizedPath::Path(root, context));
                        unfold(sized_walk_tree(SizedWalk::Active(value, SizedTree::Node(node, parent, color, value, old(sub.model), sibling_model), SizedPath::Path(root, up_model))));
                        unfold(sized_path_context(SizedPath::Path(root, context)));
                        unfold(sized_path_context(SizedPath::Path(root, up_model)));
                        rewrite(context == SizedContext::Left(node, parent, color, value, sibling_model, up_model));
                        unfold(sized_plug(SizedContext::Left(node, parent, color, value, sibling_model, up_model), old(sub.model)));
                        normalize();
                    }
                    have sized_walk_rank(next.model) < sized_context_depth(sized_path_context(old(path.model))) + 1 by {
                        rewrite(next.model == SizedWalk::Active(value, SizedTree::Node(node, parent, color, value, old(sub.model), sibling_model), SizedPath::Path(root, up_model)));
                        rewrite(old(path.model) == SizedPath::Path(root, context));
                        unfold(sized_walk_rank(SizedWalk::Active(value, SizedTree::Node(node, parent, color, value, old(sub.model), sibling_model), SizedPath::Path(root, up_model))));
                        unfold(sized_path_context(SizedPath::Path(root, context)));
                        unfold(sized_path_context(SizedPath::Path(root, up_model)));
                        rewrite(context == SizedContext::Left(node, parent, color, value, sibling_model, up_model));
                        unfold(sized_context_depth(SizedContext::Left(node, parent, color, value, sibling_model, up_model)));
                        arithmetic();
                    }
                    have sized_walk_pending(next.model) == 1 by {
                        rewrite(next.model == SizedWalk::Active(value, SizedTree::Node(node, parent, color, value, old(sub.model), sibling_model), SizedPath::Path(root, up_model))); unfold(sized_walk_pending(SizedWalk::Active(value, SizedTree::Node(node, parent, color, value, old(sub.model), sibling_model), SizedPath::Path(root, up_model)))); normalize();
                    }
                    have sized_walk_pending(next.model) == 1 or parent_node == stop by { assumption(); }
                    apply(sized_context_depth_nonnegative(up_model));
                    have 0 <= sized_walk_rank(next.model) by {
                        rewrite(next.model == SizedWalk::Active(value, SizedTree::Node(node, parent, color, value, old(sub.model), sibling_model), SizedPath::Path(root, up_model))); unfold(sized_walk_rank(SizedWalk::Active(value, SizedTree::Node(node, parent, color, value, old(sub.model), sibling_model), SizedPath::Path(root, up_model)))); unfold(sized_path_context(SizedPath::Path(root, up_model))); arithmetic() using { 0 <= sized_context_depth(up_model); }
                    }
                },
                SizedContext::Right(node, parent, color, value, sibling_model, up_model) => {
                    have sized_context_parent(context, stop) == node by {
                        rewrite(context == SizedContext::Right(node, parent, color, value, sibling_model, up_model));
                        unfold(sized_context_parent(SizedContext::Right(node, parent, color, value, sibling_model, up_model), stop)); normalize();
                    }
                    have parent_node == node by { assumption(); }
                    let { metadata: metadata, sibling: sibling, up: up } = unfold(frames);
                    let focus = fold(sized_recompute_at(parent_node), { model: SizedTree::Node(node, parent, color, value, sibling_model, old(sub.model)) }, { metadata: metadata, left: sibling, right: sub });
                    let remaining = fold(sized_path_at(parent_node, stop, value), { model: SizedPath::Path(root, up_model) }, { frames: up });
                    have sized_value(SizedTree::Node(node, parent, color, value, sibling_model, old(sub.model))) == value by { unfold(sized_value(SizedTree::Node(node, parent, color, value, sibling_model, old(sub.model)))); normalize(); }
                    have sized_parent_is(SizedTree::Node(node, parent, color, value, sibling_model, old(sub.model)), sized_context_parent(sized_path_context(SizedPath::Path(root, up_model)), stop)) == 1 by {
                        unfold(sized_path_context(SizedPath::Path(root, up_model)));
                        unfold(sized_parent_is(SizedTree::Node(node, parent, color, value, sibling_model, old(sub.model)), sized_context_parent(up_model, stop)));
                        normalize() using { parent == sized_context_parent(up_model, stop); }
                    }
                    let next = fold(sized_walk_at(parent_node, stop), { model: SizedWalk::Active(value, SizedTree::Node(node, parent, color, value, sibling_model, old(sub.model)), SizedPath::Path(root, up_model)) }, { focus: focus, path: remaining });
                    have sized_walk_root(next.model) == sized_path_root(old(path.model)) by {
                        rewrite(next.model == SizedWalk::Active(value, SizedTree::Node(node, parent, color, value, sibling_model, old(sub.model)), SizedPath::Path(root, up_model)));
                        rewrite(old(path.model) == SizedPath::Path(root, context));
                        unfold(sized_walk_root(SizedWalk::Active(value, SizedTree::Node(node, parent, color, value, sibling_model, old(sub.model)), SizedPath::Path(root, up_model))));
                        unfold(sized_path_root(SizedPath::Path(root, context)));
                        unfold(sized_path_root(SizedPath::Path(root, up_model)));
                        normalize();
                    }
                    have sized_walk_tree(next.model) == sized_plug(sized_path_context(old(path.model)), old(sub.model)) by {
                        rewrite(next.model == SizedWalk::Active(value, SizedTree::Node(node, parent, color, value, sibling_model, old(sub.model)), SizedPath::Path(root, up_model)));
                        rewrite(old(path.model) == SizedPath::Path(root, context));
                        unfold(sized_walk_tree(SizedWalk::Active(value, SizedTree::Node(node, parent, color, value, sibling_model, old(sub.model)), SizedPath::Path(root, up_model))));
                        unfold(sized_path_context(SizedPath::Path(root, context)));
                        unfold(sized_path_context(SizedPath::Path(root, up_model)));
                        rewrite(context == SizedContext::Right(node, parent, color, value, sibling_model, up_model));
                        unfold(sized_plug(SizedContext::Right(node, parent, color, value, sibling_model, up_model), old(sub.model)));
                        normalize();
                    }
                    have sized_walk_rank(next.model) < sized_context_depth(sized_path_context(old(path.model))) + 1 by {
                        rewrite(next.model == SizedWalk::Active(value, SizedTree::Node(node, parent, color, value, sibling_model, old(sub.model)), SizedPath::Path(root, up_model)));
                        rewrite(old(path.model) == SizedPath::Path(root, context));
                        unfold(sized_walk_rank(SizedWalk::Active(value, SizedTree::Node(node, parent, color, value, sibling_model, old(sub.model)), SizedPath::Path(root, up_model))));
                        unfold(sized_path_context(SizedPath::Path(root, context)));
                        unfold(sized_path_context(SizedPath::Path(root, up_model)));
                        rewrite(context == SizedContext::Right(node, parent, color, value, sibling_model, up_model));
                        unfold(sized_context_depth(SizedContext::Right(node, parent, color, value, sibling_model, up_model)));
                        arithmetic();
                    }
                    have sized_walk_pending(next.model) == 1 by {
                        rewrite(next.model == SizedWalk::Active(value, SizedTree::Node(node, parent, color, value, sibling_model, old(sub.model)), SizedPath::Path(root, up_model))); unfold(sized_walk_pending(SizedWalk::Active(value, SizedTree::Node(node, parent, color, value, sibling_model, old(sub.model)), SizedPath::Path(root, up_model)))); normalize();
                    }
                    have sized_walk_pending(next.model) == 1 or parent_node == stop by { assumption(); }
                    apply(sized_context_depth_nonnegative(up_model));
                    have 0 <= sized_walk_rank(next.model) by {
                        rewrite(next.model == SizedWalk::Active(value, SizedTree::Node(node, parent, color, value, sibling_model, old(sub.model)), SizedPath::Path(root, up_model))); unfold(sized_walk_rank(SizedWalk::Active(value, SizedTree::Node(node, parent, color, value, sibling_model, old(sub.model)), SizedPath::Path(root, up_model)))); unfold(sized_path_context(SizedPath::Path(root, up_model))); arithmetic() using { 0 <= sized_context_depth(up_model); }
                    }
                },
            }
        },
    }
}

// Certify the untouched children before calling the checked recomputation.
tactic prepare_sized_focus(p: struct rb_node*) {
    consumes tree: sized_recompute_at(p);
    requires p != 0;
    requires rb_subtree_size(sized_shape(tree.model)) <= 2147483647;
    produces prepared: sized_recompute_at(p);
    ensures prepared.model == old(tree.model);
    ensures 0 <= sized_value(sized_left(prepared.model));
    ensures 0 <= sized_value(sized_right(prepared.model));
    ensures sized_value(sized_right(prepared.model)) <= 2147483646;
    ensures sized_value(sized_left(prepared.model)) <= 2147483646 - sized_value(sized_right(prepared.model));
} by {
    match tree.model {
        SizedTree::Empty => { unfold(tree); contradiction(p == 0); },
        SizedTree::Node(node, parent, color, value, left_model, right_model) => {
            let { metadata: metadata, left: left, right: right } = unfold(tree);
            let { checked: left } = certify_size(p->rb_left, { tree: left });
            let { checked: right } = certify_size(p->rb_right, { tree: right });
            have to_integer(sized_value(left_model)) == rb_subtree_size(sized_shape(left_model)) by {
                rewrite(left_model == left.model); assumption();
            }
            have to_integer(sized_value(right_model)) == rb_subtree_size(sized_shape(right_model)) by {
                rewrite(right_model == right.model); assumption();
            }
            apply(rb_subtree_size_nonnegative(sized_shape(left_model)));
            apply(rb_subtree_size_nonnegative(sized_shape(right_model)));
            have 0 <= to_integer(sized_value(left_model)) by {
                arithmetic() using {
                    to_integer(sized_value(left_model)) == rb_subtree_size(sized_shape(left_model));
                    rb_subtree_size(sized_shape(left_model)) >= 0;
                }
            }
            have 0 <= to_integer(sized_value(right_model)) by {
                arithmetic() using {
                    to_integer(sized_value(right_model)) == rb_subtree_size(sized_shape(right_model));
                    rb_subtree_size(sized_shape(right_model)) >= 0;
                }
            }
            have rb_subtree_size(sized_shape(SizedTree::Node(node, parent, color, value, left_model, right_model))) == 1 + rb_subtree_size(sized_shape(left_model)) + rb_subtree_size(sized_shape(right_model)) by {
                unfold(sized_shape(SizedTree::Node(node, parent, color, value, left_model, right_model)));
                unfold(rb_subtree_size(RbTree::Node(node, parent, color, sized_shape(left_model), sized_shape(right_model))));
                arithmetic();
            }
            have 1 + to_integer(sized_value(left_model)) + to_integer(sized_value(right_model)) <= 2147483647 by {
                rewrite(to_integer(sized_value(left_model)) == rb_subtree_size(sized_shape(left_model)));
                rewrite(to_integer(sized_value(right_model)) == rb_subtree_size(sized_shape(right_model)));
                rewrite(1 + rb_subtree_size(sized_shape(left_model)) + rb_subtree_size(sized_shape(right_model)) == rb_subtree_size(sized_shape(SizedTree::Node(node, parent, color, value, left_model, right_model))));
                rewrite(SizedTree::Node(node, parent, color, value, left_model, right_model) == old(tree.model));
                assumption();
            }
            apply(size_children_fit(sized_value(left_model), sized_value(right_model)));
            let prepared = fold(sized_recompute_at(p), { model: SizedTree::Node(node, parent, color, value, left_model, right_model) }, { metadata: metadata, left: left, right: right });
            have prepared.model == old(tree.model) by { assumption(); }
            have sized_left(prepared.model) == left_model by {
                rewrite(prepared.model == SizedTree::Node(node, parent, color, value, left_model, right_model));
                unfold(sized_left(SizedTree::Node(node, parent, color, value, left_model, right_model))); normalize();
            }
            have sized_right(prepared.model) == right_model by {
                rewrite(prepared.model == SizedTree::Node(node, parent, color, value, left_model, right_model));
                unfold(sized_right(SizedTree::Node(node, parent, color, value, left_model, right_model))); normalize();
            }
            have 0 <= sized_value(sized_left(prepared.model)) by { rewrite(sized_left(prepared.model) == left_model); assumption(); }
            have 0 <= sized_value(sized_right(prepared.model)) by { rewrite(sized_right(prepared.model) == right_model); assumption(); }
            have sized_value(sized_right(prepared.model)) <= 2147483646 by { rewrite(sized_right(prepared.model) == right_model); assumption(); }
            have sized_value(sized_left(prepared.model)) <= 2147483646 - sized_value(sized_right(prepared.model)) by {
                rewrite(sized_left(prepared.model) == left_model);
                rewrite(sized_right(prepared.model) == right_model); assumption();
            }
        },
    }
}

// A successful unchanged-size test repairs the whole ancestor path.
tactic stop_sized_path(child: struct rb_node*, stop: struct rb_node*, previous: int32) {
    consumes sub: sized_at(child);
    consumes path: sized_path_at(child, stop, previous);
    requires sized_value(sub.model) == previous;
    requires sized_parent_is(sub.model, sized_context_parent(sized_path_context(path.model), stop)) == 1;
    produces done: sized_walk_at(child, stop);
    ensures sized_walk_pending(done.model) == 0;
    ensures sized_walk_root(done.model) == sized_path_root(old(path.model));
    ensures sized_walk_tree(done.model) == sized_plug(sized_path_context(old(path.model)), old(sub.model));
} by {
    let { whole: whole } = restore_sized_path(child, stop, previous, { sub: sub, path: path });
    match whole.model {
        SizedResult::Tree(root, tree_model) => {
            have sized_result_root(SizedResult::Tree(root, tree_model)) == root by {
                unfold(sized_result_root(SizedResult::Tree(root, tree_model))); normalize();
            }
            have sized_result_tree(SizedResult::Tree(root, tree_model)) == tree_model by {
                unfold(sized_result_tree(SizedResult::Tree(root, tree_model))); normalize();
            }
            have root == sized_path_root(old(path.model)) by {
                rewrite(root == sized_result_root(SizedResult::Tree(root, tree_model)));
                rewrite(SizedResult::Tree(root, tree_model) == whole.model); assumption();
            }
            have tree_model == sized_plug(sized_path_context(old(path.model)), old(sub.model)) by {
                rewrite(tree_model == sized_result_tree(SizedResult::Tree(root, tree_model)));
                rewrite(SizedResult::Tree(root, tree_model) == whole.model); assumption();
            }
            let done = fold(sized_walk_at(child, stop), { model: SizedWalk::Done(SizedResult::Tree(root, tree_model)) }, { whole: whole });
            have sized_walk_pending(done.model) == 0 by {
                rewrite(done.model == SizedWalk::Done(SizedResult::Tree(root, tree_model)));
                unfold(sized_walk_pending(SizedWalk::Done(SizedResult::Tree(root, tree_model)))); normalize();
            }
            have sized_walk_root(done.model) == sized_path_root(old(path.model)) by {
                rewrite(done.model == SizedWalk::Done(SizedResult::Tree(root, tree_model)));
                unfold(sized_walk_root(SizedWalk::Done(SizedResult::Tree(root, tree_model))));
                unfold(sized_result_root(SizedResult::Tree(root, tree_model))); assumption();
            }
            have sized_walk_tree(done.model) == sized_plug(sized_path_context(old(path.model)), old(sub.model)) by {
                rewrite(done.model == SizedWalk::Done(SizedResult::Tree(root, tree_model)));
                unfold(sized_walk_tree(SizedWalk::Done(SizedResult::Tree(root, tree_model))));
                unfold(sized_result_tree(SizedResult::Tree(root, tree_model))); assumption();
            }
        },
    }
}

// The caller receives a single checked whole-tree resource on every exit.
tactic finish_sized_walk(rb: struct rb_node*, stop: struct rb_node*) {
    consumes walk: sized_walk_at(rb, stop);
    requires sized_walk_pending(walk.model) == 0;
    produces whole: sized_result_at(stop);
    ensures sized_result_root(whole.model) == sized_walk_root(old(walk.model));
    ensures sized_result_tree(whole.model) == sized_walk_tree(old(walk.model));
    ensures sized_counts_valid(sized_result_tree(whole.model)) == 1;
} by {
    match walk.model {
        SizedWalk::Active(previous, sub_model, path_model) => {
            have sized_walk_pending(walk.model) == 1 by {
                rewrite(walk.model == SizedWalk::Active(previous, sub_model, path_model));
                unfold(sized_walk_pending(SizedWalk::Active(previous, sub_model, path_model))); normalize();
            }
            have not (sized_walk_pending(walk.model) == 0) by {
                rewrite(sized_walk_pending(walk.model) == 1); normalize();
            }
            contradiction(sized_walk_pending(walk.model) == 0);
        },
        SizedWalk::Done(result_model) => {
            let { whole: result } = unfold(walk);
            match result.model {
                SizedResult::Tree(root, tree_model) => {
                    let { tree: tree } = unfold(result);
                    let { checked: checked } = certify_size(root, { tree: tree });
                    have sized_counts_valid(tree_model) == 1 by { rewrite(tree_model == checked.model); assumption(); }
                    let whole = fold(sized_result_at(stop), { model: SizedResult::Tree(root, tree_model) }, { tree: checked });
                    have sized_result_root(whole.model) == sized_walk_root(old(walk.model)) by {
                        rewrite(whole.model == SizedResult::Tree(root, tree_model));
                        rewrite(old(walk.model) == SizedWalk::Done(result_model));
                        rewrite(result_model == SizedResult::Tree(root, tree_model));
                        unfold(sized_walk_root(SizedWalk::Done(SizedResult::Tree(root, tree_model)))); normalize();
                    }
                    have sized_result_tree(whole.model) == sized_walk_tree(old(walk.model)) by {
                        rewrite(whole.model == SizedResult::Tree(root, tree_model));
                        rewrite(old(walk.model) == SizedWalk::Done(result_model));
                        rewrite(result_model == SizedResult::Tree(root, tree_model));
                        unfold(sized_walk_tree(SizedWalk::Done(SizedResult::Tree(root, tree_model)))); normalize();
                    }
                    have sized_counts_valid(sized_result_tree(whole.model)) == 1 by {
                        rewrite(whole.model == SizedResult::Tree(root, tree_model));
                        unfold(sized_result_tree(SizedResult::Tree(root, tree_model))); assumption();
                    }
                },
            }
        },
    }
}
