// Two writable insertion callbacks: a right-left three-node rotation at the root.
verifying "rb_insert_augmented.c";
verifying "rbtree_size_rotate.c";
verifying "rbtree_size_copy.c";
verifying "rbtree_size_compute.c";
import "rbtree_size_rotate_model.click";
import "rbtree_size_model_unique.click";

spec enum SizedInsertMirroredDoublePhase {
    Before(struct rb_node*, struct rb_node*),
    After(struct rb_node*, struct rb_node*),
}

function sized_mirrored_double_pending(phase: SizedInsertMirroredDoublePhase) -> int32 {
    match phase {
        SizedInsertMirroredDoublePhase::Before(g, p) => 1,
        SizedInsertMirroredDoublePhase::After(g, p) => 0,
    }
}

function sized_mirrored_double_finish(phase: SizedInsertMirroredDoublePhase) -> SizedInsertMirroredDoublePhase {
    match phase {
        SizedInsertMirroredDoublePhase::Before(g, p) => SizedInsertMirroredDoublePhase::After(g, p),
        SizedInsertMirroredDoublePhase::After(g, p) => SizedInsertMirroredDoublePhase::After(g, p),
    }
}

function sized_mirrored_double_before(g: struct rb_node*, p: struct rb_node*, n: struct rb_node*) -> SizedTree {
    SizedTree::Node(g, 0, Color::Black, 3, SizedTree::Empty, SizedTree::Node(p, g, Color::Red, 2, SizedTree::Node(n, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty))
}

function sized_mirrored_double_after(g: struct rb_node*, p: struct rb_node*, n: struct rb_node*) -> RbTree {
    RbTree::Node(n, 0, Color::Black, RbTree::Node(g, n, Color::Red, RbTree::Empty, RbTree::Empty), RbTree::Node(p, n, Color::Red, RbTree::Empty, RbTree::Empty))
}

function sized_mirrored_double_expected(phase: SizedInsertMirroredDoublePhase, node: struct rb_node*) -> RbTree {
    match phase {
        SizedInsertMirroredDoublePhase::Before(g, p) => sized_mirrored_double_after(g, p, node),
        SizedInsertMirroredDoublePhase::After(g, p) => sized_mirrored_double_after(g, p, node),
    }
}

resource sized_insert_mirrored_double_at(node: struct rb_node*, root: struct rb_root*) {
    field phase: SizedInsertMirroredDoublePhase;
    field model: SizedTree;
    match phase {
        SizedInsertMirroredDoublePhase::Before(g, p) => {
            owns root->rb_node;
            owns tree: sized_at(g);
            fact root->rb_node == g;
            fact tree.model == model;
            fact model == sized_mirrored_double_before(g, p, node);
        },
        SizedInsertMirroredDoublePhase::After(g, p) => {
            owns root->rb_node;
            owns tree: sized_at(node);
            fact root->rb_node == node;
            fact tree.model == model;
        },
    }
}

void __rb_insert(struct rb_node* node, struct rb_root* root,
                  void (*augment_rotate)(struct rb_node*, struct rb_node*)) {
    requires RotateTreeLeft(augment_rotate);
    requires RotateTreeRight(augment_rotate);
    owns state: sized_insert_mirrored_double_at(node, root);
    requires sized_mirrored_double_pending(state.phase) == 1;
    ensures state.phase == sized_mirrored_double_finish(old(state.phase));
    ensures sized_shape(state.model) == sized_mirrored_double_expected(old(state.phase), node);
} by {
    match state.phase {
        SizedInsertMirroredDoublePhase::After(g, p) => {
            have sized_mirrored_double_pending(state.phase) != 1 by {
                rewrite(state.phase == SizedInsertMirroredDoublePhase::After(g, p));
                unfold(sized_mirrored_double_pending(SizedInsertMirroredDoublePhase::After(g, p))); normalize();
            }
            contradiction(sized_mirrored_double_pending(state.phase) == 1);
        },
        SizedInsertMirroredDoublePhase::Before(g, p) => {
            let { tree: tree } = unfold(state);
            unfold(sized_mirrored_double_before(g, p, node));
            have tree.model == SizedTree::Node(g, 0, Color::Black, 3, SizedTree::Empty, SizedTree::Node(p, g, Color::Red, 2, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty)) by {
                rewrite(tree.model == sized_mirrored_double_before(g, p, node));
                unfold(sized_mirrored_double_before(g, p, node)); normalize();
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
            let parent_tree = fold(sized_at(p), { model: SizedTree::Node(p, g, Color::Red, 2, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty) }, { metadata: p_size, right: p_right, left: focus });
            let tree = fold(sized_at(g), { model: old(state.model) }, { metadata: g_size, right: parent_tree, left: g_left });
            let state = fold(sized_insert_mirrored_double_at(node, root), { phase: SizedInsertMirroredDoublePhase::Before(g, p), model: old(state.model) }, { tree: tree });
            loop {
                owns state: sized_insert_mirrored_double_at(node, root);
                decreases 0;
                invariant node == old(node);
                invariant parent == p;
                invariant g == old(root->rb_node);
                invariant p == old(g->rb_right);
                invariant state.phase == SizedInsertMirroredDoublePhase::Before(g, p);
                invariant old(state.phase) == SizedInsertMirroredDoublePhase::Before(g, p);
                invariant state.model == sized_mirrored_double_before(g, p, node);
                initialize by simp();
                preserve by {
                    let { tree: loop_tree } = unfold(state);
                    unfold(sized_mirrored_double_before(g, p, node));
                    have loop_tree.model == SizedTree::Node(g, 0, Color::Black, 3, SizedTree::Empty, SizedTree::Node(p, g, Color::Red, 2, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty)) by {
                        rewrite(loop_tree.model == sized_mirrored_double_before(g, p, node));
                        unfold(sized_mirrored_double_before(g, p, node)); normalize();
                    }
                    let { metadata: g_size, right: parent_tree, left: g_left } = unfold(loop_tree);
                    let { metadata: p_size, right: p_right, left: focus } = unfold(parent_tree);
                    unfold(g_left); unfold(p_right);
                    mark before_inner_rotation;
                    let { metadata: n_size, right: n_right, left: n_left } = unfold(focus);
                    let focus = fold(sized_at(node), { model: SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty) }, { metadata: n_size, right: n_right, left: n_left });
                    unfold(color_bit(Color::Red)); unfold(color_bit(Color::Black));
                    have p->__rb_parent_color == address(g) by {
                        rewrite(p->__rb_parent_color == address(g) + (p->__rb_parent_color & 1));
                        rewrite((p->__rb_parent_color & 1) == color_bit(Color::Red));
                        rewrite(color_bit(Color::Red) == 0); normalize();
                    }
                    have g->__rb_parent_color == 1 by {
                        rewrite(g->__rb_parent_color == address(0) + (g->__rb_parent_color & 1));
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
                    transport(at(after_inner_child_store, parent->rb_left == 0), parent->rb_left == 0) using {
                        at(after_inner_child_store, parent->rb_left == 0);
                        parent == p;
                        at(after_inner_child_store, parent) == p;
                        separate(memory(parent->rb_left), memory(node->rb_right));
                        separate(memory(parent->rb_left), memory(parent->__rb_parent_color));
                    };
                    have p->rb_left == 0 by { assumption(); }
                    transport(at(before_inner_rotation, p->rb_right == 0), p->rb_right == 0) using {
                        at(before_inner_rotation, p->rb_right == 0);
                        parent == p;
                        separate(memory(p->rb_right), memory(p->rb_left));
                        separate(memory(p->rb_right), memory(node->rb_right));
                        separate(memory(p->rb_right), memory(p->__rb_parent_color));
                    };
                    let p_right = fold(sized_at(p->rb_right), { model: SizedTree::Empty });
                    let p_left = fold(sized_at(p->rb_left), { model: SizedTree::Empty });
                    have at(before_inner_rotation, old(root->rb_node)->rb_right) == parent by { assumption(); }
                    have p->__rb_parent_color == address(node) by { normalize() using { parent == p; at(before_inner_rotation, old(root->rb_node)->rb_right) == parent; }; }
                    have (address(node) & 7) == 0 by { assumption(); }
                    have (p->__rb_parent_color & 1) == 0 by {
                        rewrite(p->__rb_parent_color == address(node)); arithmetic() using { aligned(node, 8); };
                    }
                    have p->__rb_parent_color == address(node) + (p->__rb_parent_color & 1) by {
                        rewrite((p->__rb_parent_color & 1) == 0);
                        rewrite(p->__rb_parent_color == address(node)); normalize();
                    }
                    let demoted = fold(sized_recompute_at(p), { model: SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty) }, { metadata: p_size, right: p_right, left: p_left });
                    have node->rb_left == 0 by { simp(); }
                    let other = fold(sized_at(node->rb_left), { model: SizedTree::Empty });
                    have sized_parent_is(SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty), node) == 1 by { unfold(sized_parent_is(SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty), node)); normalize(); }
                    have sized_parent_is(SizedTree::Empty, node) == 1 by { unfold(sized_parent_is(SizedTree::Empty, node)); normalize(); }
                    unfold(sized_value(SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty)));
                    unfold(sized_right(SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty)));
                    unfold(sized_left(SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty)));
                    unfold(sized_value(SizedTree::Empty));
                    have to_integer(sized_value(SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty))) == 2 + to_integer(sized_value(sized_left(SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty)))) + to_integer(sized_value(sized_right(SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty)))) + to_integer(sized_value(SizedTree::Empty)) by {
                        rewrite(sized_right(SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty)) == SizedTree::Empty);
                        rewrite(sized_left(SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty)) == SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty)) == 2);
                        rewrite(sized_value(SizedTree::Empty) == 0); normalize();
                    }
                    let rotated = fold(sized_rotation_right_at(p, node), { model: SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty)) }, { metadata: n_size, demoted: demoted, other: other });
                    unfold(sized_right(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty))));
                    have 0 <= sized_value(sized_right(sized_right(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty))))) by { rewrite(sized_right(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty))) == SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty)); rewrite(sized_right(SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty)) == SizedTree::Empty); rewrite(sized_value(SizedTree::Empty) == 0); normalize(); }
                    have 0 <= sized_value(sized_left(sized_right(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty))))) by { rewrite(sized_right(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty))) == SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty)); rewrite(sized_left(SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty)) == SizedTree::Empty); rewrite(sized_value(SizedTree::Empty) == 0); normalize(); }
                    have sized_value(sized_left(sized_right(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty))))) <= 2147483646 by { rewrite(sized_right(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty))) == SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty)); rewrite(sized_left(SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty)) == SizedTree::Empty); rewrite(sized_value(SizedTree::Empty) == 0); normalize(); }
                    have sized_value(sized_right(sized_right(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty))))) <= 2147483646 - sized_value(sized_left(sized_right(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty))))) by { rewrite(sized_right(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty))) == SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty)); rewrite(sized_right(SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty)) == SizedTree::Empty); rewrite(sized_left(SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty)) == SizedTree::Empty); rewrite(sized_value(SizedTree::Empty) == 0); normalize(); }
                    let { checked: first } = step(RotateTreeRight, { tree: rotated });
                    let { checked: first } = certify_size(node, { tree: first });
                    have sized_counts_valid(SizedTree::Node(node, p, Color::Red, 2, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))) == 1 by {
                        unfold(sized_counts_valid(SizedTree::Node(node, p, Color::Red, 2, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))));
                        unfold(sized_counts_valid(SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty)));
                        unfold(sized_counts_valid(SizedTree::Empty));
                        unfold(sized_value(SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty)));
                        unfold(sized_value(SizedTree::Empty)); simp();
                    }
                    have sized_shape(first.model) == sized_shape(SizedTree::Node(node, p, Color::Red, 2, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))) by {
                        rewrite(sized_shape(first.model) == sized_shape(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty))));
                        unfold(sized_shape(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty))));
                        unfold(sized_shape(SizedTree::Node(node, p, Color::Red, 2, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))));
                        unfold(sized_shape(SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty)));
                        unfold(sized_shape(SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))); normalize();
                    }
                    apply(sized_model_unique(first.model, SizedTree::Node(node, p, Color::Red, 2, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))));
                    have first.model == SizedTree::Node(node, p, Color::Red, 2, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty)) by { assumption(); }
                    let { metadata: n_size, right: p_leaf, left: outer_empty } = unfold(first);
                    unfold(outer_empty);
                    mark before_outer_rotation;
                    step(); step(); step(); step(); step(); step();
                    let { metadata: p_size, right: p_empty_right, left: p_empty_left } = unfold(p_leaf);
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
                    have at(before_inner_rotation, old(root->rb_node)->__rb_parent_color == 1) by { assumption(); }
                    transport(at(before_inner_rotation, old(root->rb_node)->__rb_parent_color == 1), old(root->rb_node)->__rb_parent_color == 1) using {
                        at(before_inner_rotation, old(root->rb_node)->__rb_parent_color == 1);
                        old(root->rb_node) == g;
                        at(before_inner_rotation, old(root->rb_node)->rb_right) == p;
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
                    let p_size = fold(size_metadata(p), { value: 1 });
                    let n_size = fold(size_metadata(node), { value: 2 });
                    let p_leaf = fold(sized_at(p), { model: SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty) }, { metadata: p_size, right: p_empty_right, left: p_empty_left });
                    have gparent == g by { assumption(); }
                    have gparent->__rb_parent_color == 1 by { assumption(); }
                    mark before_outer_parent_helper;
                    step();
                    have g->rb_right == 0 by { simp(); }
                    let g_right = fold(sized_at(g->rb_right), { model: SizedTree::Empty });
                    transport(at(before_inner_rotation, old(root->rb_node)->rb_left == 0), old(root->rb_node)->rb_left == 0) using {
                        at(before_inner_rotation, old(root->rb_node)->rb_left == 0);
                        old(root->rb_node) == g;
                        at(before_inner_rotation, old(root->rb_node)->rb_right) == p;
                        gparent == g;
                        parent == node;
                        separate(memory(g->rb_left), memory(p->rb_left));
                        separate(memory(g->rb_left), memory(node->rb_right));
                        separate(memory(g->rb_left), memory(p->__rb_parent_color));
                        separate(memory(g->rb_left), memory(g->rb_right));
                        separate(memory(g->rb_left), memory(node->rb_left));
                        separate(memory(g->rb_left), memory(g->__rb_parent_color));
                        separate(memory(g->rb_left), memory(node->__rb_parent_color));
                        separate(memory(g->rb_left), memory(root->rb_node));
                    };
                    have g->rb_left == 0 by { assumption(); }
                    let g_left = fold(sized_at(g->rb_left), { model: SizedTree::Empty });
                    let demoted = fold(sized_recompute_at(g), {
                        model: SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)
                    }, { metadata: g_size, right: g_right, left: g_left });
                    have node->rb_right == p by { simp(); }
                    transport(at(statement(67).exit, parent->rb_left == gparent), parent->rb_left == gparent) using {
                        at(statement(67).exit, parent->rb_left == gparent);
                        separate(memory(parent->rb_left), memory(root->rb_node));
                        separate(memory(parent->rb_left), memory(parent->__rb_parent_color));
                        separate(memory(parent->rb_left), memory(gparent->__rb_parent_color));
                    };
                    have node->rb_left == g by {
                        rewrite(node == parent);
                        rewrite(g == gparent);
                        assumption();
                    }
                    have parent == node by { assumption(); }
                    have parent->__rb_parent_color == at(before_outer_parent_helper, gparent->__rb_parent_color) by { simp(); }
                    have parent->__rb_parent_color == 1 by { simp(); }
                    transport(parent->__rb_parent_color == 1, node->__rb_parent_color == 1);
                    have node->__rb_parent_color == (node->__rb_parent_color & 1) by {
                        rewrite(node->__rb_parent_color == 1); normalize();
                    }
                    have (node->__rb_parent_color & 1) == color_bit(Color::Black) by {
                        rewrite(node->__rb_parent_color == 1);
                        rewrite(color_bit(Color::Black) == 1); normalize();
                    }
                    have sized_parent_is(SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), node) == 1 by {
                        unfold(sized_parent_is(SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), node)); normalize();
                    }
                    have sized_parent_is(SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), node) == 1 by {
                        unfold(sized_parent_is(SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), node)); normalize();
                    }
                    have to_integer(sized_value(SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))) == 2 + to_integer(sized_value(sized_left(SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)))) + to_integer(sized_value(sized_right(SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)))) + to_integer(sized_value(SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))) by {
                        unfold(sized_value(SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)));
                        unfold(sized_right(SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)));
                        unfold(sized_left(SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)));
                        unfold(sized_value(SizedTree::Empty));
                        unfold(sized_value(SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))); normalize();
                    }
                    let second_rotated = fold(sized_rotation_left_at(g, node), {
                        model: SizedTree::Node(node, 0, Color::Black, 2, SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))
                    }, { metadata: n_size, other: p_leaf, demoted: demoted });
                    unfold(sized_left(SizedTree::Node(node, 0, Color::Black, 2, SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))));
                    unfold(sized_right(SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)));
                    unfold(sized_left(SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)));
                    unfold(sized_value(SizedTree::Empty));
                    have 0 <= sized_value(sized_right(sized_left(SizedTree::Node(node, 0, Color::Black, 2, SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))))) by {
                        rewrite(sized_left(SizedTree::Node(node, 0, Color::Black, 2, SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))) == SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty));
                        rewrite(sized_right(SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)) == SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty) == 0); normalize();
                    }
                    have 0 <= sized_value(sized_left(sized_left(SizedTree::Node(node, 0, Color::Black, 2, SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))))) by {
                        rewrite(sized_left(SizedTree::Node(node, 0, Color::Black, 2, SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))) == SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty));
                        rewrite(sized_left(SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)) == SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty) == 0); normalize();
                    }
                    have sized_value(sized_left(sized_left(SizedTree::Node(node, 0, Color::Black, 2, SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))))) <= 2147483646 by {
                        rewrite(sized_left(SizedTree::Node(node, 0, Color::Black, 2, SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))) == SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty));
                        rewrite(sized_left(SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)) == SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty) == 0); normalize();
                    }
                    have sized_value(sized_right(sized_left(SizedTree::Node(node, 0, Color::Black, 2, SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))))) <= 2147483646 - sized_value(sized_left(sized_left(SizedTree::Node(node, 0, Color::Black, 2, SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))))) by {
                        rewrite(sized_left(SizedTree::Node(node, 0, Color::Black, 2, SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))) == SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty));
                        rewrite(sized_right(SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)) == SizedTree::Empty);
                        rewrite(sized_left(SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)) == SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty) == 0); normalize();
                    }
                    let { checked: second } = step(RotateTreeLeft, { tree: second_rotated });
                    have sized_shape(second.model) == sized_mirrored_double_after(g, p, node) by {
                        rewrite(sized_shape(second.model) == sized_shape(SizedTree::Node(node, 0, Color::Black, 2, SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))));
                        unfold(sized_shape(SizedTree::Node(node, 0, Color::Black, 2, SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))));
                        unfold(sized_shape(SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty)));
                        unfold(sized_shape(SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)));
                        unfold(sized_shape(SizedTree::Empty));
                        unfold(sized_mirrored_double_after(g, p, node)); normalize();
                    }
                    let state = fold(sized_insert_mirrored_double_at(node, root), {
                        phase: SizedInsertMirroredDoublePhase::After(g, p), model: second.model
                    }, { tree: second });
                    have state.phase == sized_mirrored_double_finish(old(state.phase)) by {
                        unfold(sized_mirrored_double_finish(SizedInsertMirroredDoublePhase::Before(g, p))); simp();
                    }
                    have sized_shape(state.model) == sized_mirrored_double_expected(old(state.phase), node) by {
                        rewrite(old(state.phase) == SizedInsertMirroredDoublePhase::Before(g, p));
                        unfold(sized_mirrored_double_expected(SizedInsertMirroredDoublePhase::Before(g, p), node)); simp();
                    }
                    step();


                }
            }
            have node == old(node) by { assumption(); }
            execute(); simp();
        },
    }
}

void __rb_insert_augmented(struct rb_node* node, struct rb_root* root,
                  void (*augment_rotate)(struct rb_node*, struct rb_node*)) {
    requires RotateTreeLeft(augment_rotate);
    requires RotateTreeRight(augment_rotate);
    owns state: sized_insert_mirrored_double_at(node, root);
    requires sized_mirrored_double_pending(state.phase) == 1;
    ensures state.phase == sized_mirrored_double_finish(old(state.phase));
    ensures sized_shape(state.model) == sized_mirrored_double_expected(old(state.phase), node);
} by {
    step(__rb_insert(node, root, augment_rotate), { state: state });
    execute(); simp();
}

void rb_insert_augmented(struct rb_node* node, struct rb_root* root,
                         const struct rb_augment_callbacks* augment) {
    views augment->rotate;
    requires RotateTreeLeft(augment->rotate);
    requires RotateTreeRight(augment->rotate);
    owns state: sized_insert_mirrored_double_at(node, root);
    requires sized_mirrored_double_pending(state.phase) == 1;
    ensures state.phase == sized_mirrored_double_finish(old(state.phase));
    ensures sized_shape(state.model) == sized_mirrored_double_expected(old(state.phase), node);
} by {
    step(__rb_insert_augmented(node, root, augment->rotate), { state: state });
    execute(); simp();
}
