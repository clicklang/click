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
        known();
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

// Retain complete node observations through read-only C steps.
resource mirrored_context_double_far_node_frame(p: struct rb_node*, up: struct rb_node*) {
    field color: Color;
    field word: uint64;
    field right: int32*;
    field left: int32*;
    owns p->__rb_parent_color;
    fact p->__rb_parent_color == word;
    fact p->__rb_parent_color == address(up) + (p->__rb_parent_color & 1);
    fact ((p->__rb_parent_color & ~3) as (struct rb_node*)) == up;
    fact (p->__rb_parent_color & 1) == color_bit(color);
    owns p->rb_right;
    owns p->rb_left;
    fact p->rb_right == right;
    fact p->rb_left == left;
    fact p->rb_right != p;
    fact p->rb_left != p;
}

resource mirrored_context_double_far_tag(p: struct rb_node*, up: struct rb_node*) {
    field color: Color;
    field word: uint64;
    owns p->__rb_parent_color;
    fact p->__rb_parent_color == word;
    fact p->__rb_parent_color == address(up) + (p->__rb_parent_color & 1);
    fact ((p->__rb_parent_color & ~3) as (struct rb_node*)) == up;
    fact (p->__rb_parent_color & 1) == color_bit(color);
}

resource mirrored_context_double_far_link(slot: struct rb_node**) {
    field child: int32*;
    owns *slot;
    fact *slot == child;
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
                rewrite(state.phase, SizedInsertMirroredContextDoubleFarPhase::After(g, p, above, pv, gv, far));
                unfold(sized_mirrored_context_double_far_pending(SizedInsertMirroredContextDoubleFarPhase::After(g, p, above, pv, gv, far))); normalize();
            }
            contradiction(sized_mirrored_context_double_far_pending(state.phase) == 1);
        },
        SizedInsertMirroredContextDoubleFarPhase::Before(g, p, above, pv, gv, far) => {
            let { tree: tree, link: link } = unfold(state);
            unfold(sized_mirrored_context_double_far_before(g, p, node, above, pv, gv, far));
            have tree.model == SizedTree::Node(g, above, Color::Black, gv, SizedTree::Empty, SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), far)) by {
                rewrite(tree.model, sized_mirrored_context_double_far_before(g, p, node, above, pv, gv, far));
                unfold(sized_mirrored_context_double_far_before(g, p, node, above, pv, gv, far)); normalize();
            }
            let { metadata: g_size, right: parent_tree, left: g_left } = unfold(tree);
            let { metadata: p_size, right: p_right, left: focus } = unfold(parent_tree);
            let { metadata: n_size, right: n_right, left: n_left } = unfold(focus);
            unfold(color_bit(Color::Red));
            have (node->__rb_parent_color & 1) == 0 by {
                rewrite((node->__rb_parent_color & 1), color_bit(Color::Red));
                rewrite(color_bit(Color::Red), 0); normalize();
            }
            have node->__rb_parent_color == address(p) by {
                rewrite(node->__rb_parent_color, address(p) + (node->__rb_parent_color & 1));
                rewrite((node->__rb_parent_color & 1), 0); normalize();
            }
            let initial_parent = fold(mirrored_context_double_far_node_frame(p, g), { color: Color::Red, word: p->__rb_parent_color, right: p->rb_right, left: p->rb_left });
            let initial_grandparent = fold(mirrored_context_double_far_node_frame(g, above), { color: Color::Black, word: g->__rb_parent_color, right: g->rb_right, left: g->rb_left });
            step(); step(); step(); step();
            unfold(initial_grandparent);
            unfold(initial_parent);
            unfold(n_right); unfold(n_left);
            have node->rb_right == 0 by { known(); }
            have node->rb_left == 0 by { known(); }
            let n_right = fold(sized_at(0), { model: SizedTree::Empty });
            let n_left = fold(sized_at(0), { model: SizedTree::Empty });
            let focus = fold(sized_at(node), { model: SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty) }, { metadata: n_size, right: n_right, left: n_left });
            have p->rb_left == node by { known(); }
            have p->rb_right != p by {
                known();
            }
            have p->rb_left != p by {
                known();
            }
            let parent_tree = fold(sized_at(p), { model: SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), far) }, { metadata: p_size, right: p_right, left: focus });
            have ((g->__rb_parent_color & ~3) as (struct rb_node*)) == above by known();
            let tree = fold(sized_at(g), { model: SizedTree::Node(g, above, Color::Black, gv, SizedTree::Empty, SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), far)) }, { metadata: g_size, right: parent_tree, left: g_left });
            have tree.model == old(state.model) by known();
            let state = fold(sized_insert_mirrored_context_double_far_at(node, root), { phase: SizedInsertMirroredContextDoubleFarPhase::Before(g, p, above, pv, gv, far), model: old(state.model), context: old(state.context), whole_model: old(state.whole_model) }, { tree: tree, link: link });
            step(); // Declare tmp before entering the C loop.
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
                initialize by solve();
                preserve by {
                    let { tree: loop_tree, link: link } = unfold(state);
                    unfold(sized_mirrored_context_double_far_before(g, p, node, above, pv, gv, far));
                    have loop_tree.model == SizedTree::Node(g, above, Color::Black, gv, SizedTree::Empty, SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), far)) by {
                        rewrite(loop_tree.model, sized_mirrored_context_double_far_before(g, p, node, above, pv, gv, far));
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
                        solve() using {
                            to_integer(pv) == 1 + to_integer(sized_value(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))) + to_integer(sized_value(far));
                            to_integer(sized_value(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))) == 1;
                        };
                    }
                    have to_integer(gv) == 1 + to_integer(pv) by {
                        solve() using {
                            to_integer(gv) == 1 + to_integer(sized_value(SizedTree::Empty)) + to_integer(sized_value(SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), far)));
                            to_integer(sized_value(SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), far))) == to_integer(pv);
                            to_integer(sized_value(SizedTree::Empty)) == 0;
                        };
                    }
                    have -2147483648 <= to_integer(pv);
                    have to_integer(pv) <= 2147483647;
                    have to_integer(pv) - to_integer(1) >= -2147483648 by { solve() using {
                        to_integer(pv) == 2 + to_integer(sized_value(far));
                        0 <= to_integer(sized_value(far));
                    }; }
                    have to_integer(pv) - to_integer(1) <= 2147483647 by { solve() using { to_integer(pv) <= 2147483647; }; }
                    have defined(pv - 1);
                    have to_integer(pv - 1) == to_integer(pv) - to_integer(1);
                    have to_integer(pv - 1) == 1 + to_integer(sized_value(SizedTree::Empty)) + to_integer(sized_value(far)) by { solve() using {
                        to_integer(pv - 1) == to_integer(pv) - to_integer(1);
                        to_integer(pv) == 2 + to_integer(sized_value(far));
                        to_integer(sized_value(SizedTree::Empty)) == 0;
                    }; }
                    have 1 + to_integer(0) + to_integer(sized_value(far)) <= 2147483647 by { solve() using {
                        to_integer(pv) == 2 + to_integer(sized_value(far));
                        to_integer(pv) <= 2147483647;
                    }; }
                    apply(size_children_fit(0, sized_value(far)));
                    let { metadata: n_size, right: n_right, left: n_left } = unfold(focus);
                    have separate(memory(g->__rb_parent_color), memory(node->__rb_parent_color)) by known();
                    have g != node by known();
                    let focus = fold(sized_at(node), { model: SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty) }, { metadata: n_size, right: n_right, left: n_left });
                    unfold(color_bit(Color::Red)); unfold(color_bit(Color::Black));
                    have p->__rb_parent_color == address(g) by {
                        rewrite(p->__rb_parent_color, address(g) + (p->__rb_parent_color & 1));
                        rewrite((p->__rb_parent_color & 1), color_bit(Color::Red));
                        rewrite(color_bit(Color::Red), 0); normalize();
                    }
                    have g->__rb_parent_color == address(above) + 1 by {
                        rewrite(g->__rb_parent_color, address(above) + (g->__rb_parent_color & 1));
                        rewrite((g->__rb_parent_color & 1), color_bit(Color::Black));
                        rewrite(color_bit(Color::Black), 1); normalize();
                    }
                    let loop_parent = fold(mirrored_context_double_far_node_frame(p, g), { color: Color::Red, word: p->__rb_parent_color, right: p->rb_right, left: p->rb_left });
                    let loop_grandparent = fold(mirrored_context_double_far_node_frame(g, above), { color: Color::Black, word: g->__rb_parent_color, right: g->rb_right, left: g->rb_left });
                    step(); step(); step(); step(); step(); step(); step();
                    unfold(loop_grandparent);
                    have gparent == g by known();
                    have parent == p by known();
                    let grandparent_tag = fold(mirrored_context_double_far_tag(g, above), { color: Color::Black, word: g->__rb_parent_color });
                    let grandparent_right = fold(mirrored_context_double_far_link(&g->rb_right), { child: g->rb_right });
                    let grandparent_left = fold(mirrored_context_double_far_link(&g->rb_left), { child: g->rb_left });
                    step(); step(); step(); step();
                    step(); // Load parent->rb_left into tmp after skipping the uncle case.
                    unfold(loop_parent);
                    have p->rb_left == node by known();
                    have tmp == node by known();
                    step();
                    let { metadata: n_size, right: n_right, left: n_left } = unfold(focus);
                    unfold(n_right); unfold(n_left);
                    have node->rb_right == 0 by known();
                    have node->rb_left == 0 by known();
                    let node_tag = fold(mirrored_context_double_far_tag(node, p), { color: Color::Red, word: node->__rb_parent_color });
                    let outer_left = fold(mirrored_context_double_far_link(&node->rb_left), { child: node->rb_left });
                    let parent_right = fold(mirrored_context_double_far_link(&p->rb_right), { child: p->rb_right });
                    step(); step(); // Read the null middle child and store it in parent->rb_left.
                    have p->rb_left == 0 by known();
                    let parent_left = fold(mirrored_context_double_far_link(&p->rb_left), { child: p->rb_left });
                    step(); // Put the old parent under the inner pivot.
                    have node->rb_right == p by known();
                    let inner_right = fold(mirrored_context_double_far_link(&node->rb_right), { child: node->rb_right });
                    step(); step(); step(); // Skip the null child and update the old parent's tag.
                    unfold(parent_right); unfold(parent_left);
                    unfold(inner_right); unfold(outer_left); unfold(node_tag);
                    have p->rb_left == 0 by known();
                    let p_left = fold(sized_at(0), { model: SizedTree::Empty });
                    have p->__rb_parent_color == address(node) by known();
                    have ((p->__rb_parent_color & ~3) as (struct rb_node*)) == node by known();
                    have (p->__rb_parent_color & 1) == 0 by {
                        rewrite(p->__rb_parent_color, address(node)); solve() using { aligned(node, 8); };
                    }
                    have p->__rb_parent_color == address(node) + (p->__rb_parent_color & 1) by {
                        rewrite((p->__rb_parent_color & 1), 0);
                        rewrite(p->__rb_parent_color, address(node)); normalize();
                    }
                    have sized_parent_is(SizedTree::Empty, p) == 1 by {
                        unfold(sized_parent_is(SizedTree::Empty, p)); normalize();
                    }
                    let demoted = fold(sized_recompute_at(p), { model: SizedTree::Node(p, node, Color::Red, pv, SizedTree::Empty, far) }, { metadata: p_size, right: p_right, left: p_left });
                    have node->rb_left == 0 by known();
                    let other = fold(sized_at(0), { model: SizedTree::Empty });
                    have sized_parent_is(SizedTree::Node(p, node, Color::Red, pv, SizedTree::Empty, far), node) == 1 by { unfold(sized_parent_is(SizedTree::Node(p, node, Color::Red, pv, SizedTree::Empty, far), node)); normalize(); }
                    have sized_parent_is(SizedTree::Empty, node) == 1 by { unfold(sized_parent_is(SizedTree::Empty, node)); normalize(); }
                    unfold(sized_value(SizedTree::Node(p, node, Color::Red, pv, SizedTree::Empty, far)));
                    unfold(sized_right(SizedTree::Node(p, node, Color::Red, pv, SizedTree::Empty, far)));
                    unfold(sized_left(SizedTree::Node(p, node, Color::Red, pv, SizedTree::Empty, far)));
                    unfold(sized_value(SizedTree::Empty));
                    have to_integer(sized_value(SizedTree::Node(p, node, Color::Red, pv, SizedTree::Empty, far))) == 2 + to_integer(sized_value(sized_left(SizedTree::Node(p, node, Color::Red, pv, SizedTree::Empty, far)))) + to_integer(sized_value(sized_right(SizedTree::Node(p, node, Color::Red, pv, SizedTree::Empty, far)))) + to_integer(sized_value(SizedTree::Empty)) by {
                        rewrite(sized_value(SizedTree::Node(p, node, Color::Red, pv, SizedTree::Empty, far)), pv);
                        rewrite(sized_right(SizedTree::Node(p, node, Color::Red, pv, SizedTree::Empty, far)), far);
                        rewrite(sized_left(SizedTree::Node(p, node, Color::Red, pv, SizedTree::Empty, far)), SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty), 0); known();
                    }
                    let rotated = fold(sized_rotation_right_at(p, node), { model: SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, pv, SizedTree::Empty, far)) }, { metadata: n_size, demoted: demoted, other: other });
                    unfold(sized_right(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, pv, SizedTree::Empty, far))));
                    let { checked: first } = step(RotateTreeRight, { tree: rotated });
                    let { checked: first } = certify_size(node, { tree: first });
                    unfold(sized_counts_valid(SizedTree::Empty));
                    apply(sized_valid_node(p, node, Color::Red, pv - 1, SizedTree::Empty, far));
                    unfold(sized_value(SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far)));
                    have to_integer(pv) == 1 + to_integer(sized_value(SizedTree::Empty)) + to_integer(sized_value(SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far))) by {
                        rewrite(sized_value(SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far)), pv - 1);
                        rewrite(sized_value(SizedTree::Empty), 0);
                        solve() using { to_integer(pv - 1) == to_integer(pv) - to_integer(1); };
                    }
                    apply(sized_valid_node(node, p, Color::Red, pv, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far)));
                    have sized_shape(first.model) == sized_shape(SizedTree::Node(node, p, Color::Red, pv, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far))) by {
                        rewrite(sized_shape(first.model), sized_shape(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, pv, SizedTree::Empty, far))));
                        unfold(sized_shape(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, pv, SizedTree::Empty, far))));
                        unfold(sized_shape(SizedTree::Node(node, p, Color::Red, pv, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far))));
                        unfold(sized_shape(SizedTree::Node(p, node, Color::Red, pv, SizedTree::Empty, far)));
                        unfold(sized_shape(SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far))); normalize();
                    }
                    apply(sized_model_unique(first.model, SizedTree::Node(node, p, Color::Red, pv, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far))));
                    have first.model == SizedTree::Node(node, p, Color::Red, pv, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far)) by { known(); }
                    let { metadata: n_size, right: parent_subtree, left: outer_empty } = unfold(first);
                    unfold(outer_empty);
                    let { metadata: p_size, right: far_subtree, left: p_empty_left } = unfold(parent_subtree);
                    have node->rb_right == p by known();
                    let parent_subtree = fold(sized_at(p), { model: SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far) }, { metadata: p_size, right: far_subtree, left: p_empty_left });
                    let kept_right = fold(mirrored_context_double_far_link(&node->rb_right), { child: p });
                    unfold(grandparent_right);
                    step(); step(); step(); // Select the pivot and store the null outer middle child.
                    have parent == node by known();
                    have g->rb_right == 0 by known();
                    let kept_g_right = fold(mirrored_context_double_far_link(&g->rb_right), { child: g->rb_right });
                    step(); // Put the grandparent under the promoted pivot.
                    have node->rb_left == g by known();
                    let kept_left = fold(mirrored_context_double_far_link(&node->rb_left), { child: node->rb_left });
                    step(); step(); // The outer middle child is null.
                    unfold(grandparent_tag);
                    have g->__rb_parent_color == address(above) + 1 by known();
                    unfold(g_size);
                    have sized_context_parent_word(link.model, g->__rb_parent_color) == 1 by {
                        apply(sized_context_parent_word_black(link.model, above, g->__rb_parent_color));
                    }
                    mark before_parent_update;
                    have ((g->__rb_parent_color & ~3) as (struct rb_node*)) == above by known();
                    have ((g->__rb_parent_color & ~3) as (struct rb_node*)) == sized_context_parent(link.model, 0) by {
                        rewrite(sized_context_parent(link.model, 0), above); known();
                    }
                    let { after: link } = step(insert::__rb_rotate_set_parents, { c: link });
                    let g_size = fold(size_metadata(g), { value: gv });
                    unfold(kept_g_right); unfold(grandparent_left);
                    unfold(kept_right); unfold(kept_left);
                    have g->rb_right == 0 by known();
                    have g->rb_left == 0 by known();
                    let g_right = fold(sized_at(0), { model: SizedTree::Empty });
                    let g_left = fold(sized_at(0), { model: SizedTree::Empty });
                    let demoted = fold(sized_recompute_at(g), {
                        model: SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)
                    }, { metadata: g_size, right: g_right, left: g_left });
                    have node->rb_right == p by known();
                    have node->rb_left == g by known();
                    have parent == node by known();
                    have node->__rb_parent_color == at(before_parent_update, g->__rb_parent_color) by { solve(); }
                    have node->__rb_parent_color == address(above) + (node->__rb_parent_color & 1) by {
                        rewrite(node->__rb_parent_color, at(before_parent_update, g->__rb_parent_color));
                        known();
                    }
                    have (node->__rb_parent_color & 1) == color_bit(Color::Black) by {
                        rewrite(node->__rb_parent_color, at(before_parent_update, g->__rb_parent_color));
                        known();
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
                        rewrite(sized_value(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)), gv);
                        rewrite(sized_right(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty);
                        rewrite(sized_left(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far)), pv - 1);
                        rewrite(sized_value(SizedTree::Empty), 0);
                        solve() using {
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
                        rewrite(sized_left(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far))), SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty));
                        rewrite(sized_right(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty), 0); normalize();
                    }
                    have 0 <= sized_value(sized_left(sized_left(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far))))) by {
                        rewrite(sized_left(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far))), SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty));
                        rewrite(sized_left(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty), 0); normalize();
                    }
                    have sized_value(sized_left(sized_left(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far))))) <= 2147483646 by {
                        rewrite(sized_left(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far))), SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty));
                        rewrite(sized_left(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty), 0); normalize();
                    }
                    have sized_value(sized_right(sized_left(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far))))) <= 2147483646 - sized_value(sized_left(sized_left(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far))))) by {
                        rewrite(sized_left(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far))), SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty));
                        rewrite(sized_right(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty);
                        rewrite(sized_left(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty), 0); normalize();
                    }
                    let { checked: second } = step(RotateTreeLeft, { tree: second_rotated });
                    have sized_shape(second.model) == sized_mirrored_context_double_far_after(g, p, node, above, pv, gv, far) by {
                        rewrite(sized_shape(second.model), sized_shape(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Empty, far))));
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
                        solve() using {
                            to_integer(gv) == 1 + to_integer(pv);
                            to_integer(pv) == 2 + to_integer(sized_value(far));
                            to_integer(sized_value(far)) == rb_subtree_size(sized_shape(far));
                        };
                    }
                    have to_integer(sized_value(second.model)) == to_integer(gv) by {
                        rewrite(to_integer(sized_value(second.model)), rb_subtree_size(sized_shape(second.model)));
                        rewrite(sized_shape(second.model), sized_mirrored_context_double_far_after(g, p, node, above, pv, gv, far)); known();
                    }
                    have sized_value(second.model) == gv;
                    apply(sized_parent_is_shape(second.model, above));
                    have rb_parent_is(sized_shape(second.model), above) == 1 by {
                        rewrite(sized_shape(second.model), sized_mirrored_context_double_far_after(g, p, node, above, pv, gv, far));
                        unfold(sized_mirrored_context_double_far_after(g, p, node, above, pv, gv, far));
                        unfold(rb_parent_is(RbTree::Node(node, above, Color::Black, RbTree::Node(g, node, Color::Red, RbTree::Empty, RbTree::Empty), RbTree::Node(p, node, Color::Red, RbTree::Empty, sized_shape(far))), above)); normalize();
                    }
                    have sized_parent_is(second.model, above) == 1 by {
                        rewrite(sized_parent_is(second.model, above), rb_parent_is(sized_shape(second.model), above)); known();
                    }
                    let { frames: path } = unfold(link);
                    have path.model == old(state.context) by { known(); }
                    have sized_parent_is(second.model, sized_context_parent(path.model, 0)) == 1 by {
                        rewrite(path.model, old(state.context));
                        rewrite(sized_context_parent(old(state.context), 0), above); known();
                    }
                    mark before_restore;
                    let { whole: whole } = restore_sized_context(node, root->rb_node, 0, gv, { path: path, sub: second });
                    have whole.model == sized_plug(old(state.context), at(before_restore, second.model)) by { known(); }
                    let state = fold(sized_insert_mirrored_context_double_far_at(node, root), {
                        phase: SizedInsertMirroredContextDoubleFarPhase::After(g, p, above, pv, gv, far), model: at(before_restore, second.model), context: old(state.context), whole_model: whole.model
                    }, { whole: whole });
                    have state.context == old(state.context) by { known(); }
                    have state.whole_model == sized_plug(old(state.context), state.model) by { known(); }
                    have state.phase == sized_mirrored_context_double_far_finish(old(state.phase)) by {
                        unfold(sized_mirrored_context_double_far_finish(SizedInsertMirroredContextDoubleFarPhase::Before(g, p, above, pv, gv, far))); solve();
                    }
                    have sized_shape(state.model) == sized_mirrored_context_double_far_expected(old(state.phase), node) by {
                        rewrite(old(state.phase), SizedInsertMirroredContextDoubleFarPhase::Before(g, p, above, pv, gv, far));
                        unfold(sized_mirrored_context_double_far_expected(SizedInsertMirroredContextDoubleFarPhase::Before(g, p, above, pv, gv, far), node)); solve();
                    }
                    step();


                }
            }
            have node == old(node) by { known(); }
            step_until(function.exit);
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
    step(insert::__rb_insert, { state: state });
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
    step(insert::__rb_insert_augmented, { state: state });
}
