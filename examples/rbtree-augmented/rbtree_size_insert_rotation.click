// First writable insertion callback: a left-left three-node rotation at the root.
verifying "rb_insert_augmented.c";
verifying "rbtree_size_rotate.c";
verifying "rbtree_size_copy.c";
verifying "rbtree_size_compute.c";
import "rbtree_size_rotate_model.click";

spec enum SizedInsertThreePhase {
    Before(struct rb_node*, struct rb_node*),
    After(struct rb_node*, struct rb_node*),
}

function sized_three_pending(phase: SizedInsertThreePhase) -> int32 {
    match phase {
        SizedInsertThreePhase::Before(g, p) => 1,
        SizedInsertThreePhase::After(g, p) => 0,
    }
}

function sized_three_finish(phase: SizedInsertThreePhase) -> SizedInsertThreePhase {
    match phase {
        SizedInsertThreePhase::Before(g, p) => SizedInsertThreePhase::After(g, p),
        SizedInsertThreePhase::After(g, p) => SizedInsertThreePhase::After(g, p),
    }
}

function sized_three_before(g: struct rb_node*, p: struct rb_node*, n: struct rb_node*) -> SizedTree {
    SizedTree::Node(g, 0, Color::Black, 3,
        SizedTree::Node(p, g, Color::Red, 2,
            SizedTree::Node(n, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty), SizedTree::Empty)
}

function sized_three_after(g: struct rb_node*, p: struct rb_node*, n: struct rb_node*) -> RbTree {
    RbTree::Node(p, 0, Color::Black,
        RbTree::Node(n, p, Color::Red, RbTree::Empty, RbTree::Empty),
        RbTree::Node(g, p, Color::Red, RbTree::Empty, RbTree::Empty))
}

function sized_three_expected(phase: SizedInsertThreePhase, node: struct rb_node*) -> RbTree {
    match phase {
        SizedInsertThreePhase::Before(g, p) => sized_three_after(g, p, node),
        SizedInsertThreePhase::After(g, p) => sized_three_after(g, p, node),
    }
}

resource sized_insert_three_at(node: struct rb_node*, root: struct rb_root*) {
    field phase: SizedInsertThreePhase;
    field model: SizedTree;
    match phase {
        SizedInsertThreePhase::Before(g, p) => {
            owns root->rb_node;
            owns tree: sized_at(g);
            fact root->rb_node == g;
            fact tree.model == model;
            fact model == sized_three_before(g, p, node);
        },
        SizedInsertThreePhase::After(g, p) => {
            owns root->rb_node;
            owns tree: sized_at(p);
            fact root->rb_node == p;
            fact tree.model == model;
        },
    }
}

void __rb_insert(struct rb_node* node, struct rb_root* root,
                  void (*augment_rotate)(struct rb_node*, struct rb_node*)) {
    requires RotateTreeRight(augment_rotate);
    owns state: sized_insert_three_at(node, root);
    requires sized_three_pending(state.phase) == 1;
    ensures state.phase == sized_three_finish(old(state.phase));
    ensures sized_shape(state.model) == sized_three_expected(old(state.phase), node);
} by {
    match state.phase {
        SizedInsertThreePhase::After(g, p) => {
            have sized_three_pending(state.phase) != 1 by {
                rewrite(state.phase == SizedInsertThreePhase::After(g, p));
                unfold(sized_three_pending(SizedInsertThreePhase::After(g, p))); normalize();
            }
            contradiction(sized_three_pending(state.phase) == 1);
        },
        SizedInsertThreePhase::Before(g, p) => {
            let { tree: tree } = unfold(state);
            unfold(sized_three_before(g, p, node));
            have tree.model == SizedTree::Node(g, 0, Color::Black, 3,
                SizedTree::Node(p, g, Color::Red, 2,
                    SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty), SizedTree::Empty) by {
                rewrite(tree.model == sized_three_before(g, p, node));
                unfold(sized_three_before(g, p, node)); normalize();
            }
            let { metadata: g_size, left: parent_tree, right: g_right } = unfold(tree);
            let { metadata: p_size, left: focus, right: p_right } = unfold(parent_tree);
            let { metadata: n_size, left: n_left, right: n_right } = unfold(focus);
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
            unfold(n_left); unfold(n_right);
            have node->rb_left == 0 by { assumption(); }
            have node->rb_right == 0 by { assumption(); }
            let n_left = fold(sized_at(node->rb_left), { model: SizedTree::Empty });
            let n_right = fold(sized_at(node->rb_right), { model: SizedTree::Empty });
            let focus = fold(sized_at(node), { model: SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty) }, { metadata: n_size, left: n_left, right: n_right });
            have p->rb_left == node by { assumption(); }
            have p->rb_left != p by {
                assumption();
            }
            have p->rb_right != p by {
                assumption();
            }
            let parent_tree = fold(sized_at(p), { model: SizedTree::Node(p, g, Color::Red, 2, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty) }, { metadata: p_size, left: focus, right: p_right });
            let tree = fold(sized_at(g), { model: old(state.model) }, { metadata: g_size, left: parent_tree, right: g_right });
            let state = fold(sized_insert_three_at(node, root), { phase: SizedInsertThreePhase::Before(g, p), model: old(state.model) }, { tree: tree });
            loop {
                owns state: sized_insert_three_at(node, root);
                decreases 0;
                invariant node == old(node);
                invariant parent == p;
                invariant g == old(root->rb_node);
                invariant p == old(g->rb_left);
                invariant state.phase == SizedInsertThreePhase::Before(g, p);
                invariant old(state.phase) == SizedInsertThreePhase::Before(g, p);
                invariant state.model == sized_three_before(g, p, node);
                initialize by simp;
                preserve by {
                    let { tree: loop_tree } = unfold(state);
                    unfold(sized_three_before(g, p, node));
                    have loop_tree.model == SizedTree::Node(g, 0, Color::Black, 3,
                        SizedTree::Node(p, g, Color::Red, 2,
                            SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty), SizedTree::Empty) by {
                        rewrite(loop_tree.model == sized_three_before(g, p, node));
                        unfold(sized_three_before(g, p, node)); normalize();
                    }
                    let { metadata: g_size, left: parent_tree, right: g_right } = unfold(loop_tree);
                    let { metadata: p_size, left: focus, right: p_right } = unfold(parent_tree);
                    unfold(g_right); unfold(p_right);
                    let { metadata: n_size, left: n_left, right: n_right } = unfold(focus);
                    let focus = fold(sized_at(node), { model: SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty) }, { metadata: n_size, left: n_left, right: n_right });
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
                    step(); step(); step();
                    have tmp == 0 by { assumption(); }
                    have node != 0 by { assumption(); }
                    step(); step(); step(); step(); step(); step();
                    have gparent->__rb_parent_color == 1 by { simp(); }
                    step();
                    have g->rb_left == 0 by { simp(); }
                    let p_right = fold(sized_at(g->rb_left), { model: SizedTree::Empty });
                    have g->rb_right == 0 by { simp(); }
                    let g_right = fold(sized_at(g->rb_right), { model: SizedTree::Empty });
                    let demoted = fold(sized_recompute_at(g), {
                        model: SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)
                    }, { metadata: g_size, left: p_right, right: g_right });
                    transport(at(statement(5).entry, parent->rb_left == node), parent->rb_left == node);
                    have parent->rb_right == gparent by { simp(); }
                    have p->rb_right == g by {
                        rewrite(p == parent);
                        rewrite(g == gparent);
                        assumption();
                    }
                    have parent == p by { assumption(); }
                    have parent->__rb_parent_color == at(statement(37).exit, gparent->__rb_parent_color) by { simp(); }
                    have parent->__rb_parent_color == 1 by { simp(); }
                    transport(parent->__rb_parent_color == 1, p->__rb_parent_color == 1);
                    have p->__rb_parent_color == (p->__rb_parent_color & 1) by {
                        rewrite(p->__rb_parent_color == 1); normalize();
                    }
                    have (p->__rb_parent_color & 1) == color_bit(Color::Black) by {
                        rewrite(p->__rb_parent_color == 1);
                        rewrite(color_bit(Color::Black) == 1); normalize();
                    }
                    have sized_parent_is(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), p) == 1 by {
                        unfold(sized_parent_is(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), p)); normalize();
                    }
                    have sized_parent_is(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), p) == 1 by {
                        unfold(sized_parent_is(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), p)); normalize();
                    }
                    have to_integer(sized_value(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))) == 2 + to_integer(sized_value(sized_left(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)))) + to_integer(sized_value(sized_right(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)))) + to_integer(sized_value(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))) by {
                        unfold(sized_value(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)));
                        unfold(sized_left(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)));
                        unfold(sized_right(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)));
                        unfold(sized_value(SizedTree::Empty));
                        unfold(sized_value(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))); normalize();
                    }
                    let rotated = fold(sized_rotation_right_at(g, p), {
                        model: SizedTree::Node(p, 0, Color::Black, 2,
                            SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty),
                            SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))
                    }, { metadata: p_size, other: focus, demoted: demoted });
                    unfold(sized_right(SizedTree::Node(p, 0, Color::Black, 2, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))));
                    unfold(sized_left(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)));
                    unfold(sized_right(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)));
                    unfold(sized_value(SizedTree::Empty));
                    have 0 <= sized_value(sized_left(sized_right(SizedTree::Node(p, 0, Color::Black, 2, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))))) by {
                        rewrite(sized_right(SizedTree::Node(p, 0, Color::Black, 2, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))) == SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty));
                        rewrite(sized_left(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)) == SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty) == 0); normalize();
                    }
                    have 0 <= sized_value(sized_right(sized_right(SizedTree::Node(p, 0, Color::Black, 2, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))))) by {
                        rewrite(sized_right(SizedTree::Node(p, 0, Color::Black, 2, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))) == SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty));
                        rewrite(sized_right(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)) == SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty) == 0); normalize();
                    }
                    have sized_value(sized_right(sized_right(SizedTree::Node(p, 0, Color::Black, 2, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))))) <= 2147483646 by {
                        rewrite(sized_right(SizedTree::Node(p, 0, Color::Black, 2, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))) == SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty));
                        rewrite(sized_right(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)) == SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty) == 0); normalize();
                    }
                    have sized_value(sized_left(sized_right(SizedTree::Node(p, 0, Color::Black, 2, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))))) <= 2147483646 - sized_value(sized_right(sized_right(SizedTree::Node(p, 0, Color::Black, 2, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))))) by {
                        rewrite(sized_right(SizedTree::Node(p, 0, Color::Black, 2, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))) == SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty));
                        rewrite(sized_left(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)) == SizedTree::Empty);
                        rewrite(sized_right(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)) == SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty) == 0); normalize();
                    }
                    let { checked: checked } = step(RotateTreeRight, { tree: rotated });
                    have sized_shape(checked.model) == sized_three_after(g, p, node) by {
                        rewrite(sized_shape(checked.model) == sized_shape(SizedTree::Node(p, 0, Color::Black, 2, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))));
                        unfold(sized_shape(SizedTree::Node(p, 0, Color::Black, 2, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))));
                        unfold(sized_shape(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty)));
                        unfold(sized_shape(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)));
                        unfold(sized_shape(SizedTree::Empty));
                        unfold(sized_three_after(g, p, node)); normalize();
                    }
                    let state = fold(sized_insert_three_at(node, root), {
                        phase: SizedInsertThreePhase::After(g, p), model: checked.model
                    }, { tree: checked });
                    have state.phase == sized_three_finish(old(state.phase)) by {
                        unfold(sized_three_finish(SizedInsertThreePhase::Before(g, p))); simp();
                    }
                    have sized_shape(state.model) == sized_three_expected(old(state.phase), node) by {
                        rewrite(old(state.phase) == SizedInsertThreePhase::Before(g, p));
                        unfold(sized_three_expected(SizedInsertThreePhase::Before(g, p), node)); simp();
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
    requires RotateTreeRight(augment_rotate);
    owns state: sized_insert_three_at(node, root);
    requires sized_three_pending(state.phase) == 1;
    ensures state.phase == sized_three_finish(old(state.phase));
    ensures sized_shape(state.model) == sized_three_expected(old(state.phase), node);
} by {
    step(__rb_insert(node, root, augment_rotate), { state: state });
    execute(); simp();
}

void rb_insert_augmented(struct rb_node* node, struct rb_root* root,
                         const struct rb_augment_callbacks* augment) {
    views augment->rotate;
    requires RotateTreeRight(augment->rotate);
    owns state: sized_insert_three_at(node, root);
    requires sized_three_pending(state.phase) == 1;
    ensures state.phase == sized_three_finish(old(state.phase));
    ensures sized_shape(state.model) == sized_three_expected(old(state.phase), node);
} by {
    step(__rb_insert_augmented(node, root, augment->rotate), { state: state });
    execute(); simp();
}
