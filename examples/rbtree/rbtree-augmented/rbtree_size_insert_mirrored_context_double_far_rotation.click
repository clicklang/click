// Two writable insertion callbacks with an arbitrary far subtree and owned context.
verifying "rb_insert_augmented.c" as insert;
verifying "rbtree_size_rotate.c";
verifying "rbtree_size_copy.c";
verifying "rbtree_size_compute.c";
import "rbtree_size_rotate_model.click";
import "rbtree_size_model_unique.click";
import "rbtree_size_insert_double_subtree_model.click";
import "rbtree_size_valid_value.click";
import "rbtree_size_rotate_set_parents.click";

spec enum SizedInsertMirroredContextDoubleFarPhase {
    Before(struct rb_node*, struct rb_node*, struct rb_node*, int32, int32, SizedTree),
    After(struct rb_node*, struct rb_node*, struct rb_node*, int32, int32, SizedTree),
}

function sized_mirrored_context_double_far_pending(phase: SizedInsertMirroredContextDoubleFarPhase) -> int32 {
    match phase {
        SizedInsertMirroredContextDoubleFarPhase::Before(g, p, above, pv, gv, far) => 1,
        SizedInsertMirroredContextDoubleFarPhase::After(g, p, above, pv, gv, far) => 0,
    }
}

function sized_mirrored_context_double_far_finish(phase: SizedInsertMirroredContextDoubleFarPhase) -> SizedInsertMirroredContextDoubleFarPhase {
    match phase {
        SizedInsertMirroredContextDoubleFarPhase::Before(g, p, above, pv, gv, far) => SizedInsertMirroredContextDoubleFarPhase::After(g, p, above, pv, gv, far),
        SizedInsertMirroredContextDoubleFarPhase::After(g, p, above, pv, gv, far) => SizedInsertMirroredContextDoubleFarPhase::After(g, p, above, pv, gv, far),
    }
}

function sized_mirrored_context_double_far_before(g: struct rb_node*, p: struct rb_node*, n: struct rb_node*, above: struct rb_node*, pv: int32, gv: int32, far: SizedTree) -> SizedTree {
    SizedTree::Node(g, above, Color::Black, gv, SizedTree::Empty, SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(n, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), far))
}

function sized_mirrored_context_double_far_after(g: struct rb_node*, p: struct rb_node*, n: struct rb_node*, above: struct rb_node*, pv: int32, gv: int32, far: SizedTree) -> RbTree {
    RbTree::Node(n, above, Color::Black, RbTree::Node(g, n, Color::Red, RbTree::Empty, RbTree::Empty), RbTree::Node(p, n, Color::Red, RbTree::Empty, sized_shape(far)))
}

function sized_mirrored_context_double_far_expected(phase: SizedInsertMirroredContextDoubleFarPhase, node: struct rb_node*) -> RbTree {
    match phase {
        SizedInsertMirroredContextDoubleFarPhase::Before(g, p, above, pv, gv, far) => sized_mirrored_context_double_far_after(g, p, node, above, pv, gv, far),
        SizedInsertMirroredContextDoubleFarPhase::After(g, p, above, pv, gv, far) => sized_mirrored_context_double_far_after(g, p, node, above, pv, gv, far),
    }
}

// The checked shape retains every identity, including those in the far subtree.
theorem sized_mirrored_context_double_far_preserves_inorder(g: struct rb_node*, p: struct rb_node*, node: struct rb_node*,
                                            above: struct rb_node*, pv: int32, gv: int32, far: SizedTree) {
    ensures rb_inorder(sized_mirrored_context_double_far_after(g, p, node, above, pv, gv, far))
        == rb_inorder(sized_shape(sized_mirrored_context_double_far_before(g, p, node, above, pv, gv, far))) by {
        apply(sized_mirrored_context_double_subtree_preserves_inorder(g, p, node, above, 1, pv, gv, far, SizedTree::Empty, SizedTree::Empty, SizedTree::Empty));
        unfold(sized_mirrored_context_double_far_before(g, p, node, above, pv, gv, far));
        unfold(sized_mirrored_context_double_subtree_before(g, p, node, above, 1, pv, gv, far, SizedTree::Empty, SizedTree::Empty, SizedTree::Empty));
        unfold(sized_mirrored_context_double_far_after(g, p, node, above, pv, gv, far));
        unfold(sized_mirrored_context_double_subtree_after(g, p, node, above, far, SizedTree::Empty, SizedTree::Empty, SizedTree::Empty));
        unfold(sized_shape(SizedTree::Empty));
        unfold(rb_reparent(RbTree::Empty, p));
        unfold(rb_reparent(RbTree::Empty, g));
        assumption();
    }
}

resource sized_insert_mirrored_context_double_far_at(node: struct rb_node*, root: struct rb_root*) {
    field phase: SizedInsertMirroredContextDoubleFarPhase;
    field model: SizedTree;
    field context: SizedContext;
    field whole_model: SizedTree;
    match phase {
        SizedInsertMirroredContextDoubleFarPhase::Before(g, p, above, pv, gv, far) => {
            owns link: sized_link_at(g, root, gv);
            owns tree: sized_at(g);
            fact link.model == context;
            fact above == sized_context_parent(context, 0);
            fact tree.model == model;
            fact model == sized_mirrored_context_double_far_before(g, p, node, above, pv, gv, far);
        },
        SizedInsertMirroredContextDoubleFarPhase::After(g, p, above, pv, gv, far) => {
            owns root->rb_node;
            owns whole: sized_at(root->rb_node);
            fact above == sized_context_parent(context, 0);
            fact whole.model == whole_model;
            fact sized_parent_is(whole.model, 0) == 1;
        },
    }
}

void insert::__rb_insert(struct rb_node* node, struct rb_root* root,
                  void (*augment_rotate)(struct rb_node*, struct rb_node*)) {
    requires RotateTreeLeft(augment_rotate);
    requires RotateTreeRight(augment_rotate);
    owns state: sized_insert_mirrored_context_double_far_at(node, root);
    requires sized_mirrored_context_double_far_pending(state.phase) == 1;
    ensures state.context == old(state.context);
    ensures state.whole_model == sized_plug(old(state.context), state.model);
    ensures state.phase == sized_mirrored_context_double_far_finish(old(state.phase));
    ensures sized_shape(state.model) == sized_mirrored_context_double_far_expected(old(state.phase), node);
} by {
    match state.phase {
        SizedInsertMirroredContextDoubleFarPhase::After(g, p, above, pv, gv, far) => {
            have sized_mirrored_context_double_far_pending(state.phase) != 1 by {
                rewrite(state.phase == SizedInsertMirroredContextDoubleFarPhase::After(g, p, above, pv, gv, far));
                unfold(sized_mirrored_context_double_far_pending(SizedInsertMirroredContextDoubleFarPhase::After(g, p, above, pv, gv, far))); normalize();
            }
            contradiction(sized_mirrored_context_double_far_pending(state.phase) == 1);
        },
        SizedInsertMirroredContextDoubleFarPhase::Before(g, p, above, pv, gv, far) => {
            let { tree: tree, link: link } = unfold(state);
            unfold(sized_mirrored_context_double_far_before(g, p, node, above, pv, gv, far));
            have tree.model == SizedTree::Node(g, above, Color::Black, gv, SizedTree::Empty, SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), far)) by {
                rewrite(tree.model == sized_mirrored_context_double_far_before(g, p, node, above, pv, gv, far));
                unfold(sized_mirrored_context_double_far_before(g, p, node, above, pv, gv, far)); normalize();
            }
            let { metadata: g_size, right: parent_tree, left: g_left } = unfold(tree);
            let { metadata: p_size, right: p_right, left: focus } = unfold(parent_tree);
            let { metadata: n_size, right: n_right, left: n_left } = unfold(focus);
            unfold(color_bit(Color::Red));
            have (node->__rb_parent_color & 1) == 0 by {
                rewrite((node->__rb_parent_color & 1) == color_bit(Color::Red));
                rewrite(color_bit(Color::Red) == 0); normalize();
            }
            have node->__rb_parent_color == address(p) by {
                rewrite(node->__rb_parent_color == address(p) + (node->__rb_parent_color & 1));
                rewrite((node->__rb_parent_color & 1) == 0); normalize();
            }
            step(); step(); step(); step();
            unfold(n_right); unfold(n_left);
            have node->rb_right == 0 by { assumption(); }
            have node->rb_left == 0 by { assumption(); }
            let n_right = fold(sized_at(node->rb_right), { model: SizedTree::Empty });
            let n_left = fold(sized_at(node->rb_left), { model: SizedTree::Empty });
            let focus = fold(sized_at(node), { model: SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty) }, { metadata: n_size, right: n_right, left: n_left });
            have p->rb_left == node by { assumption(); }
            have p->rb_right != p by {
                assumption();
            }
            have p->rb_left != p by {
                assumption();
            }
            let parent_tree = fold(sized_at(p), { model: SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), far) }, { metadata: p_size, right: p_right, left: focus });
            let tree = fold(sized_at(g), { model: old(state.model) }, { metadata: g_size, right: parent_tree, left: g_left });
            let state = fold(sized_insert_mirrored_context_double_far_at(node, root), { phase: SizedInsertMirroredContextDoubleFarPhase::Before(g, p, above, pv, gv, far), model: old(state.model), context: old(state.context), whole_model: old(state.whole_model) }, { tree: tree, link: link });
            loop {
                owns state: sized_insert_mirrored_context_double_far_at(node, root);
                decreases 0;
                invariant node == old(node);
                invariant parent == p;
                invariant state.context == old(state.context);
                invariant p == old(g->rb_right);
                invariant state.phase == SizedInsertMirroredContextDoubleFarPhase::Before(g, p, above, pv, gv, far);
                invariant old(state.phase) == SizedInsertMirroredContextDoubleFarPhase::Before(g, p, above, pv, gv, far);
                invariant state.model == sized_mirrored_context_double_far_before(g, p, node, above, pv, gv, far);
                initialize by simp();
                preserve by {
                    let { tree: loop_tree, link: link } = unfold(state);
                    unfold(sized_mirrored_context_double_far_before(g, p, node, above, pv, gv, far));
                    have loop_tree.model == SizedTree::Node(g, above, Color::Black, gv, SizedTree::Empty, SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), far)) by {
                        rewrite(loop_tree.model == sized_mirrored_context_double_far_before(g, p, node, above, pv, gv, far));
                        unfold(sized_mirrored_context_double_far_before(g, p, node, above, pv, gv, far)); normalize();
                    }
                    let { metadata: g_size, right: parent_tree, left: g_left } = unfold(loop_tree);
                    let { metadata: p_size, right: p_right, left: focus } = unfold(parent_tree);
                    unfold(g_left);
                    let { checked: p_right } = certify_size(p->rb_right, { tree: p_right });
                    apply(sized_valid_value_nonnegative(far));
                    unfold(sized_value(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty)));
                    unfold(sized_value(SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), far)));
                    unfold(sized_value(SizedTree::Empty));
                    have to_integer(pv) == 2 + to_integer(sized_value(far)) by {
                        arithmetic() using {
                            to_integer(pv) == 1 + to_integer(sized_value(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))) + to_integer(sized_value(far));
                            to_integer(sized_value(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))) == 1;
                        };
                    }
                    have to_integer(gv) == 1 + to_integer(pv) by {
                        arithmetic() using {
                            to_integer(gv) == 1 + to_integer(sized_value(SizedTree::Empty)) + to_integer(sized_value(SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), far)));
                            to_integer(sized_value(SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), far))) == to_integer(pv);
                            to_integer(sized_value(SizedTree::Empty)) == 0;
                        };
                    }
                    apply(click::integer::int32_to_integer_bounds(pv));
                    have to_integer(pv) - to_integer(1) >= -2147483648 by { arithmetic() using {
                        to_integer(pv) == 2 + to_integer(sized_value(far));
                        0 <= to_integer(sized_value(far));
                    }; }
                    have to_integer(pv) - to_integer(1) <= 2147483647 by { arithmetic() using { to_integer(pv) <= 2147483647; }; }
                    apply(click::integer::int32_subtract_defined_by_integer_bounds(pv, 1));
                    apply(click::integer::int32_subtract_to_integer(pv, 1));
                    have to_integer(pv - 1) == 1 + to_integer(sized_value(SizedTree::Empty)) + to_integer(sized_value(far)) by { arithmetic() using {
                        to_integer(pv - 1) == to_integer(pv) - to_integer(1);
                        to_integer(pv) == 2 + to_integer(sized_value(far));
                        to_integer(sized_value(SizedTree::Empty)) == 0;
                    }; }
                    have 1 + to_integer(0) + to_integer(sized_value(far)) <= 2147483647 by { arithmetic() using {
                        to_integer(pv) == 2 + to_integer(sized_value(far));
                        to_integer(pv) <= 2147483647;
                    }; }
                    apply(size_children_fit(0, sized_value(far)));
                    mark before_inner_rotation;
                    let { metadata: n_size, right: n_right, left: n_left } = unfold(focus);
                    let focus = fold(sized_at(node), { model: SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty) }, { metadata: n_size, right: n_right, left: n_left });
                    unfold(color_bit(Color::Red)); unfold(color_bit(Color::Black));
                    have p->__rb_parent_color == address(g) by {
                        rewrite(p->__rb_parent_color == address(g) + (p->__rb_parent_color & 1));
                        rewrite((p->__rb_parent_color & 1) == color_bit(Color::Red));
                        rewrite(color_bit(Color::Red) == 0); normalize();
                    }
                    have g->__rb_parent_color == address(above) + 1 by {
                        rewrite(g->__rb_parent_color == address(above) + (g->__rb_parent_color & 1));
                        rewrite((g->__rb_parent_color & 1) == color_bit(Color::Black));
                        rewrite(color_bit(Color::Black) == 1); normalize();
                    }
                    step(); step(); step(); step(); step(); step(); step();
                    have gparent == g by { assumption(); }
                    have parent == p by { assumption(); }
                    step(); step(); step(); step();
                    have tmp == node by { assumption(); }
                    step();
                    let { metadata: n_size, right: n_right, left: n_left } = unfold(focus);
                    unfold(n_right); unfold(n_left);
                    step(); step(); mark after_inner_child_store;
                    step(); step(); step(); step();
                    have at(after_inner_child_store, parent) == p by { assumption(); }
                    have p->rb_left == parent->rb_left by { assumption(); }
                    have separate(memory(parent->rb_left), memory(node->rb_right)) by { assumption(); }
                    have separate(memory(parent->rb_left), memory(parent->__rb_parent_color)) by { assumption(); }
                    have separate(memory(parent->rb_left), memory(p->__rb_parent_color)) by { assumption(); }
                    have at(before_inner_rotation, g->rb_right) == parent by { assumption(); }
                    transport(at(after_inner_child_store, parent->rb_left == 0), parent->rb_left == 0) using {
                        at(after_inner_child_store, parent->rb_left == 0);
                        parent == p;
                        at(after_inner_child_store, parent) == p;
                        p == old(g->rb_right);
                        at(before_inner_rotation, g->rb_right) == parent;
                        gparent == g;
                        separate(memory(parent->rb_left), memory(node->rb_right));
                        separate(memory(parent->rb_left), memory(p->__rb_parent_color));
                    };
                    have p->rb_left == 0 by { assumption(); }
                    have separate(memory(p->rb_right), memory(p->rb_left)) by { assumption(); }
                    have separate(memory(p->rb_right), memory(node->rb_right)) by { assumption(); }
                    have separate(memory(p->rb_right), memory(p->__rb_parent_color)) by { assumption(); }
                    transport(at(before_inner_rotation, p->rb_right) == at(before_inner_rotation, p->rb_right),
                              p->rb_right == at(before_inner_rotation, p->rb_right)) using {
                        parent == p;
                        separate(memory(p->rb_right), memory(p->rb_left));
                        separate(memory(p->rb_right), memory(node->rb_right));
                        separate(memory(p->rb_right), memory(p->__rb_parent_color));
                    };
                    let p_left = fold(sized_at(p->rb_left), { model: SizedTree::Empty });
                    have at(before_inner_rotation, g->rb_right) == parent by { assumption(); }
                    have p->__rb_parent_color == address(node) by { normalize() using { parent == p; at(before_inner_rotation, g->rb_right) == parent; }; }
                    have (address(node) & 7) == 0 by { assumption(); }
                    have (p->__rb_parent_color & 1) == 0 by {
                        rewrite(p->__rb_parent_color == address(node)); arithmetic() using { aligned(node, 8); };
                    }
                    have p->__rb_parent_color == address(node) + (p->__rb_parent_color & 1) by {
                        rewrite((p->__rb_parent_color & 1) == 0);
                        rewrite(p->__rb_parent_color == address(node)); normalize();
                    }
                    have sized_parent_is(SizedTree::Empty, p) == 1 by {
                        unfold(sized_parent_is(SizedTree::Empty, p)); normalize();
                    }
                    let demoted = fold(sized_recompute_at(p), { model: SizedTree::Node(p, node, Color::Red, pv, SizedTree::Empty, far) }, { metadata: p_size, right: p_right, left: p_left });
                    have node->rb_left == 0 by { simp(); }
                    let other = fold(sized_at(node->rb_left), { model: SizedTree::Empty });
                    have sized_parent_is(SizedTree::Node(p, node, Color::Red, pv, SizedTree::Empty, far), node) == 1 by { unfold(sized_parent_is(SizedTree::Node(p, node, Color::Red, pv, SizedTree::Empty, far), node)); normalize(); }
                    have sized_parent_is(SizedTree::Empty, node) == 1 by { unfold(sized_parent_is(SizedTree::Empty, node)); normalize(); }
                    unfold(sized_value(SizedTree::Node(p, node, Color::Red, pv, SizedTree::Empty, far)));
                    unfold(sized_right(SizedTree::Node(p, node, Color::Red, pv, SizedTree::Empty, far)));
                    unfold(sized_left(SizedTree::Node(p, node, Color::Red, pv, SizedTree::Empty, far)));
                    unfold(sized_value(SizedTree::Empty));
                    have to_integer(sized_value(SizedTree::Node(p, node, Color::Red, pv, SizedTree::Empty, far))) == 2 + to_integer(sized_value(sized_left(SizedTree::Node(p, node, Color::Red, pv, SizedTree::Empty, far)))) + to_integer(sized_value(sized_right(SizedTree::Node(p, node, Color::Red, pv, SizedTree::Empty, far)))) + to_integer(sized_value(SizedTree::Empty)) by {
                        rewrite(sized_value(SizedTree::Node(p, node, Color::Red, pv, SizedTree::Empty, far)) == pv);
                        rewrite(sized_right(SizedTree::Node(p, node, Color::Red, pv, SizedTree::Empty, far)) == far);
                        rewrite(sized_left(SizedTree::Node(p, node, Color::Red, pv, SizedTree::Empty, far)) == SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty) == 0); assumption();
                    }
                    let rotated = fold(sized_rotation_right_at(p, node), { model: SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, pv, SizedTree::Empty, far)) }, { metadata: n_size, demoted: demoted, other: other });
                    unfold(sized_right(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, pv, SizedTree::Empty, far))));
                    let { checked: first } = step(RotateTreeRight, { tree: rotated });
                    let { checked: first } = certify_size(node, { tree: first });
                    unfold(sized_counts_valid(SizedTree::Empty));
                    apply(sized_valid_node(p, node, Color::Red, pv - 1, SizedTree::Empty, far));
                    unfold(sized_value(SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far)));
                    have to_integer(pv) == 1 + to_integer(sized_value(SizedTree::Empty)) + to_integer(sized_value(SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far))) by {
                        rewrite(sized_value(SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far)) == pv - 1);
                        rewrite(sized_value(SizedTree::Empty) == 0);
                        arithmetic() using { to_integer(pv - 1) == to_integer(pv) - to_integer(1); };
                    }
                    apply(sized_valid_node(node, p, Color::Red, pv, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far)));
                    have sized_shape(first.model) == sized_shape(SizedTree::Node(node, p, Color::Red, pv, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far))) by {
                        rewrite(sized_shape(first.model) == sized_shape(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, pv, SizedTree::Empty, far))));
                        unfold(sized_shape(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, pv, SizedTree::Empty, far))));
                        unfold(sized_shape(SizedTree::Node(node, p, Color::Red, pv, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far))));
                        unfold(sized_shape(SizedTree::Node(p, node, Color::Red, pv, SizedTree::Empty, far)));
                        unfold(sized_shape(SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far))); normalize();
                    }
                    apply(sized_model_unique(first.model, SizedTree::Node(node, p, Color::Red, pv, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far))));
                    have first.model == SizedTree::Node(node, p, Color::Red, pv, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far)) by { assumption(); }
                    let { metadata: n_size, right: parent_subtree, left: outer_empty } = unfold(first);
                    unfold(outer_empty);
                    mark before_outer_rotation;
                    step(); step(); step();
                    mark after_outer_right_write;
                    have at(after_outer_right_write, g->rb_right == 0) by { assumption(); }
                    have separate(memory(g->rb_right), memory(node->rb_left)) by { assumption(); }
                    step(); step(); step();
                    let { metadata: p_size, right: far_subtree, left: p_empty_left } = unfold(parent_subtree);
                    unfold(p_size); unfold(n_size);
                    have separate(memory(g->__rb_parent_color), memory(p->__rb_parent_color)) by { assumption(); }
                    have separate(memory(g->__rb_parent_color), memory(p->rb_right)) by { assumption(); }
                    have separate(memory(g->__rb_parent_color), memory(p->rb_left)) by { assumption(); }
                    have separate(memory(g->__rb_parent_color), memory(((struct sized_node*)(void*)p)->size)) by { assumption(); }
                    have separate(memory(g->__rb_parent_color), memory(node->__rb_parent_color)) by { assumption(); }
                    have separate(memory(g->__rb_parent_color), memory(node->rb_right)) by { assumption(); }
                    have separate(memory(g->__rb_parent_color), memory(node->rb_left)) by { assumption(); }
                    have separate(memory(g->__rb_parent_color), memory(((struct sized_node*)(void*)node)->size)) by { assumption(); }
                    have separate(memory(g->__rb_parent_color), memory(g->rb_right)) by { assumption(); }
                    have at(before_inner_rotation, g->__rb_parent_color == address(above) + 1) by { assumption(); }
                    transport(at(before_inner_rotation, g->__rb_parent_color == address(above) + 1), g->__rb_parent_color == address(above) + 1) using {
                        at(before_inner_rotation, g->__rb_parent_color == address(above) + 1);
                        g == g;
                        at(before_inner_rotation, g->rb_right) == p;
                        gparent == g;
                        parent == node;
                        separate(memory(g->__rb_parent_color), memory(p->__rb_parent_color));
                        separate(memory(g->__rb_parent_color), memory(p->rb_right));
                        separate(memory(g->__rb_parent_color), memory(p->rb_left));
                        separate(memory(g->__rb_parent_color), memory(((struct sized_node*)(void*)p)->size));
                        separate(memory(g->__rb_parent_color), memory(node->__rb_parent_color));
                        separate(memory(g->__rb_parent_color), memory(node->rb_right));
                        separate(memory(g->__rb_parent_color), memory(node->rb_left));
                        separate(memory(g->__rb_parent_color), memory(((struct sized_node*)(void*)node)->size));
                        separate(memory(g->__rb_parent_color), memory(g->rb_right));
                    };
                    let p_size = fold(size_metadata(p), { value: pv - 1 });
                    let n_size = fold(size_metadata(node), { value: pv });
                    let parent_subtree = fold(sized_at(p), { model: SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far) }, { metadata: p_size, right: far_subtree, left: p_empty_left });
                    have gparent == g by { assumption(); }
                    have gparent->__rb_parent_color == address(above) + 1 by { assumption(); }
                    unfold(g_size);
                    have sized_context_parent_word(link.model, g->__rb_parent_color) == 1 by {
                        apply(sized_context_parent_word_black(link.model, above, g->__rb_parent_color));
                    }
                    have g->rb_right == 0 by {
                        transport(at(after_outer_right_write, g->rb_right == 0), g->rb_right == 0) using {
                            at(after_outer_right_write, g->rb_right == 0);
                            separate(memory(g->rb_right), memory(node->rb_left));
                        };
                    }
                    mark before_parent_update;
                    have at(before_parent_update, g->rb_right == 0) by { assumption(); }
                    have at(before_parent_update, node->rb_right == p) by { assumption(); }
                    let { after: link } = step(insert::__rb_rotate_set_parents(g, node, root, 0), { c: link });
                    let g_size = fold(size_metadata(g), { value: gv });
                    transport(at(before_parent_update, g->rb_right == 0), g->rb_right == 0) using {
                        at(before_parent_update, g->rb_right == 0);
                    };
                    let g_right = fold(sized_at(g->rb_right), { model: SizedTree::Empty });
                    have g->rb_left == 0 by { simp(); }
                    let g_left = fold(sized_at(g->rb_left), { model: SizedTree::Empty });
                    let demoted = fold(sized_recompute_at(g), {
                        model: SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)
                    }, { metadata: g_size, right: g_right, left: g_left });
                    have old(g->rb_right->rb_left) == node by { assumption(); }
                    have at(before_parent_update, (old(g->rb_right->rb_left))->rb_right == p) by { rewrite(old(g->rb_right->rb_left) == node); assumption(); }
                    transport(at(before_parent_update, node->rb_right == p), node->rb_right == p) using {
                        at(before_parent_update, (old(g->rb_right->rb_left))->rb_right == p);
                        old(g->rb_right->rb_left) == node;
                        gparent == g;
                        parent == node;
                        p == old(g->rb_right);
                        at(before_parent_update, node->rb_right == p);
                    };
                    have parent->rb_left == gparent by { simp(); }
                    have node->rb_left == g by {
                        rewrite(node == parent);
                        rewrite(g == gparent);
                        assumption();
                    }
                    have parent == node by { assumption(); }
                    have node->__rb_parent_color == at(before_parent_update, g->__rb_parent_color) by { simp(); }
                    have node->__rb_parent_color == address(above) + (node->__rb_parent_color & 1) by {
                        rewrite(node->__rb_parent_color == at(before_parent_update, g->__rb_parent_color));
                        assumption();
                    }
                    have (node->__rb_parent_color & 1) == color_bit(Color::Black) by {
                        rewrite(node->__rb_parent_color == at(before_parent_update, g->__rb_parent_color));
                        assumption();
                    }
                    have sized_parent_is(SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far), node) == 1 by {
                        unfold(sized_parent_is(SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far), node)); normalize();
                    }
                    have sized_parent_is(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty), node) == 1 by {
                        unfold(sized_parent_is(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty), node)); normalize();
                    }
                    unfold(sized_value(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)));
                    unfold(sized_right(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)));
                    unfold(sized_left(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)));
                    unfold(sized_value(SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far)));
                    have to_integer(sized_value(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty))) == 2 + to_integer(sized_value(sized_left(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)))) + to_integer(sized_value(sized_right(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)))) + to_integer(sized_value(SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far))) by {
                        rewrite(sized_value(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)) == gv);
                        rewrite(sized_right(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)) == SizedTree::Empty);
                        rewrite(sized_left(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)) == SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far)) == pv - 1);
                        rewrite(sized_value(SizedTree::Empty) == 0);
                        arithmetic() using {
                            to_integer(gv) == 1 + to_integer(pv);
                            to_integer(pv - 1) == to_integer(pv) - to_integer(1);
                        };
                    }
                    let second_rotated = fold(sized_rotation_left_at(g, node), {
                        model: SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far))
                    }, { metadata: n_size, other: parent_subtree, demoted: demoted });
                    unfold(sized_left(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far))));
                    unfold(sized_right(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)));
                    unfold(sized_left(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)));
                    unfold(sized_value(SizedTree::Empty));
                    have 0 <= sized_value(sized_right(sized_left(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far))))) by {
                        rewrite(sized_left(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far))) == SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty));
                        rewrite(sized_right(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)) == SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty) == 0); normalize();
                    }
                    have 0 <= sized_value(sized_left(sized_left(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far))))) by {
                        rewrite(sized_left(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far))) == SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty));
                        rewrite(sized_left(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)) == SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty) == 0); normalize();
                    }
                    have sized_value(sized_left(sized_left(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far))))) <= 2147483646 by {
                        rewrite(sized_left(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far))) == SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty));
                        rewrite(sized_left(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)) == SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty) == 0); normalize();
                    }
                    have sized_value(sized_right(sized_left(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far))))) <= 2147483646 - sized_value(sized_left(sized_left(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far))))) by {
                        rewrite(sized_left(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far))) == SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty));
                        rewrite(sized_right(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)) == SizedTree::Empty);
                        rewrite(sized_left(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)) == SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty) == 0); normalize();
                    }
                    let { checked: second } = step(RotateTreeLeft, { tree: second_rotated });
                    have sized_shape(second.model) == sized_mirrored_context_double_far_after(g, p, node, above, pv, gv, far) by {
                        rewrite(sized_shape(second.model) == sized_shape(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far))));
                        unfold(sized_shape(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far))));
                        unfold(sized_shape(SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far)));
                        unfold(sized_shape(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)));
                        unfold(sized_shape(SizedTree::Empty));
                        unfold(sized_mirrored_context_double_far_after(g, p, node, above, pv, gv, far)); normalize();
                    }
                    have rb_subtree_size(sized_mirrored_context_double_far_after(g, p, node, above, pv, gv, far)) == to_integer(gv) by {
                        unfold(sized_mirrored_context_double_far_after(g, p, node, above, pv, gv, far));
                        unfold(rb_subtree_size(RbTree::Node(node, above, Color::Black, RbTree::Node(g, node, Color::Red, RbTree::Empty, RbTree::Empty), RbTree::Node(p, node, Color::Red, RbTree::Empty, sized_shape(far)))));
                        unfold(rb_subtree_size(RbTree::Node(p, node, Color::Red, RbTree::Empty, sized_shape(far)))); unfold(rb_subtree_size(RbTree::Node(g, node, Color::Red, RbTree::Empty, RbTree::Empty)));
                        unfold(rb_subtree_size(RbTree::Empty));
                        apply(sized_valid_value_matches_size(far));
                        arithmetic() using {
                            to_integer(gv) == 1 + to_integer(pv);
                            to_integer(pv) == 2 + to_integer(sized_value(far));
                            to_integer(sized_value(far)) == rb_subtree_size(sized_shape(far));
                        };
                    }
                    have to_integer(sized_value(second.model)) == to_integer(gv) by {
                        rewrite(to_integer(sized_value(second.model)) == rb_subtree_size(sized_shape(second.model)));
                        rewrite(sized_shape(second.model) == sized_mirrored_context_double_far_after(g, p, node, above, pv, gv, far)); assumption();
                    }
                    have sized_value(second.model) == gv by {
                        apply(click::integer::int32_to_integer_equal_implies_equal(sized_value(second.model), gv));
                    }
                    apply(sized_parent_is_shape(second.model, above));
                    have rb_parent_is(sized_shape(second.model), above) == 1 by {
                        rewrite(sized_shape(second.model) == sized_mirrored_context_double_far_after(g, p, node, above, pv, gv, far));
                        unfold(sized_mirrored_context_double_far_after(g, p, node, above, pv, gv, far));
                        unfold(rb_parent_is(RbTree::Node(node, above, Color::Black, RbTree::Node(g, node, Color::Red, RbTree::Empty, RbTree::Empty), RbTree::Node(p, node, Color::Red, RbTree::Empty, sized_shape(far))), above)); normalize();
                    }
                    have sized_parent_is(second.model, above) == 1 by {
                        rewrite(sized_parent_is(second.model, above) == rb_parent_is(sized_shape(second.model), above)); assumption();
                    }
                    let { frames: path } = unfold(link);
                    have path.model == old(state.context) by { assumption(); }
                    have sized_parent_is(second.model, sized_context_parent(path.model, 0)) == 1 by {
                        rewrite(path.model == old(state.context));
                        rewrite(sized_context_parent(old(state.context), 0) == above); assumption();
                    }
                    mark before_restore;
                    let { whole: whole } = restore_sized_context(node, root->rb_node, 0, gv, { path: path, sub: second });
                    have whole.model == sized_plug(old(state.context), at(before_restore, second.model)) by { assumption(); }
                    let state = fold(sized_insert_mirrored_context_double_far_at(node, root), {
                        phase: SizedInsertMirroredContextDoubleFarPhase::After(g, p, above, pv, gv, far), model: at(before_restore, second.model), context: old(state.context), whole_model: whole.model
                    }, { whole: whole });
                    have state.context == old(state.context) by { assumption(); }
                    have state.whole_model == sized_plug(old(state.context), state.model) by { assumption(); }
                    have state.phase == sized_mirrored_context_double_far_finish(old(state.phase)) by {
                        unfold(sized_mirrored_context_double_far_finish(SizedInsertMirroredContextDoubleFarPhase::Before(g, p, above, pv, gv, far))); simp();
                    }
                    have sized_shape(state.model) == sized_mirrored_context_double_far_expected(old(state.phase), node) by {
                        rewrite(old(state.phase) == SizedInsertMirroredContextDoubleFarPhase::Before(g, p, above, pv, gv, far));
                        unfold(sized_mirrored_context_double_far_expected(SizedInsertMirroredContextDoubleFarPhase::Before(g, p, above, pv, gv, far), node)); simp();
                    }
                    step();


                }
            }
            have node == old(node) by { assumption(); }
            execute(); simp();
        },
    }
}

void insert::__rb_insert_augmented(struct rb_node* node, struct rb_root* root,
                  void (*augment_rotate)(struct rb_node*, struct rb_node*)) {
    requires RotateTreeLeft(augment_rotate);
    requires RotateTreeRight(augment_rotate);
    owns state: sized_insert_mirrored_context_double_far_at(node, root);
    requires sized_mirrored_context_double_far_pending(state.phase) == 1;
    ensures state.context == old(state.context);
    ensures state.whole_model == sized_plug(old(state.context), state.model);
    ensures state.phase == sized_mirrored_context_double_far_finish(old(state.phase));
    ensures sized_shape(state.model) == sized_mirrored_context_double_far_expected(old(state.phase), node);
} by {
    step(insert::__rb_insert(node, root, augment_rotate), { state: state });
    execute(); simp();
}

void insert::rb_insert_augmented(struct rb_node* node, struct rb_root* root,
                         const struct rb_augment_callbacks* augment) {
    views augment->rotate;
    requires RotateTreeLeft(augment->rotate);
    requires RotateTreeRight(augment->rotate);
    owns state: sized_insert_mirrored_context_double_far_at(node, root);
    requires sized_mirrored_context_double_far_pending(state.phase) == 1;
    ensures state.context == old(state.context);
    ensures state.whole_model == sized_plug(old(state.context), state.model);
    ensures state.phase == sized_mirrored_context_double_far_finish(old(state.phase));
    ensures sized_shape(state.model) == sized_mirrored_context_double_far_expected(old(state.phase), node);
} by {
    step(insert::__rb_insert_augmented(node, root, augment->rotate), { state: state });
    execute(); simp();
}
