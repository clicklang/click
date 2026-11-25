// First writable insertion callback: a right-right three-node rotation at the root.
verifying "rb_insert_augmented.c" as insert;
verifying "rbtree_size_rotate.c";
verifying "rbtree_size_copy.c";
verifying "rbtree_size_compute.c";
import "rbtree_size_rotate_model.click";
import "rbtree_size_rotate_root_parents.click";

spec enum SizedInsertRightThreePhase {
    Before(struct rb_node*, struct rb_node*),
    After(struct rb_node*, struct rb_node*),
}

function sized_right_three_pending(phase: SizedInsertRightThreePhase) -> int32 {
    match phase {
        SizedInsertRightThreePhase::Before(g, p) => 1,
        SizedInsertRightThreePhase::After(g, p) => 0,
    }
}

function sized_right_three_finish(phase: SizedInsertRightThreePhase) -> SizedInsertRightThreePhase {
    match phase {
        SizedInsertRightThreePhase::Before(g, p) => SizedInsertRightThreePhase::After(g, p),
        SizedInsertRightThreePhase::After(g, p) => SizedInsertRightThreePhase::After(g, p),
    }
}

function sized_right_three_before(g: struct rb_node*, p: struct rb_node*, n: struct rb_node*) -> SizedTree {
    SizedTree::Node(g, 0, Color::Black, 3, SizedTree::Empty, SizedTree::Node(p, g, Color::Red, 2, SizedTree::Empty, SizedTree::Node(n, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty)))
}

function sized_right_three_after(g: struct rb_node*, p: struct rb_node*, n: struct rb_node*) -> RbTree {
    RbTree::Node(p, 0, Color::Black, RbTree::Node(g, p, Color::Red, RbTree::Empty, RbTree::Empty), RbTree::Node(n, p, Color::Red, RbTree::Empty, RbTree::Empty))
}

function sized_right_three_expected(phase: SizedInsertRightThreePhase, node: struct rb_node*) -> RbTree {
    match phase {
        SizedInsertRightThreePhase::Before(g, p) => sized_right_three_after(g, p, node),
        SizedInsertRightThreePhase::After(g, p) => sized_right_three_after(g, p, node),
    }
}

resource sized_insert_right_three_at(node: struct rb_node*, root: struct rb_root*) {
    field phase: SizedInsertRightThreePhase;
    field model: SizedTree;
    match phase {
        SizedInsertRightThreePhase::Before(g, p) => {
            owns root->rb_node;
            owns tree: sized_at(g);
            fact root->rb_node == g;
            fact tree.model == model;
            fact model == sized_right_three_before(g, p, node);
        },
        SizedInsertRightThreePhase::After(g, p) => {
            owns root->rb_node;
            owns tree: sized_at(p);
            fact root->rb_node == p;
            fact tree.model == model;
        },
    }
}

void insert::__rb_insert(struct rb_node* node, struct rb_root* root,
                  void (*augment_rotate)(struct rb_node*, struct rb_node*)) {
    requires RotateTreeLeft(augment_rotate);
    owns state: sized_insert_right_three_at(node, root);
    requires sized_right_three_pending(state.phase) == 1;
    ensures state.phase == sized_right_three_finish(old(state.phase));
    ensures sized_shape(state.model) == sized_right_three_expected(old(state.phase), node);
} by {
    match state.phase {
        SizedInsertRightThreePhase::After(g, p) => {
            have sized_right_three_pending(state.phase) != 1 by {
                rewrite(state.phase, SizedInsertRightThreePhase::After(g, p));
                unfold(sized_right_three_pending(SizedInsertRightThreePhase::After(g, p))); normalize();
            }
            contradiction(sized_right_three_pending(state.phase) == 1);
        },
        SizedInsertRightThreePhase::Before(g, p) => {
            let { tree: tree } = unfold(state);
            unfold(sized_right_three_before(g, p, node));
            have tree.model == SizedTree::Node(g, 0, Color::Black, 3, SizedTree::Empty, SizedTree::Node(p, g, Color::Red, 2, SizedTree::Empty, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))) by {
                rewrite(tree.model, sized_right_three_before(g, p, node));
                unfold(sized_right_three_before(g, p, node)); normalize();
            }
            let { metadata: g_size, right: parent_tree, left: g_left } = unfold(tree);
            let { metadata: p_size, right: focus, left: p_left } = unfold(parent_tree);
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
            have g->rb_right == p by close();
            have ((g->rb_right->__rb_parent_color & ~3) as (struct rb_node*)) == g by close();
            have p->__rb_parent_color == g->rb_right->__rb_parent_color by {
                rewrite(p, g->rb_right); close();
            }
            have ((p->__rb_parent_color & ~3) as (struct rb_node*)) == g by {
                rewrite(p->__rb_parent_color, g->rb_right->__rb_parent_color); close();
            }
            let parent_word = fold(sized_rotation_entry_word(p), {
                up: g, word: p->__rb_parent_color, color: Color::Red
            });
            let grand_word = fold(sized_rotation_entry_word(g), {
                up: 0 as (int32*), word: g->__rb_parent_color, color: Color::Black
            });
            step(); step(); step(); step();
            unfold(parent_word);
            unfold(grand_word);
            unfold(n_right); unfold(n_left);
            have g->rb_right->rb_right == node by close();
            have g->rb_right->rb_right->rb_right == 0 by close();
            have node->rb_right == 0 by {
                rewrite(node, g->rb_right->rb_right); close();
            }
            have g->rb_right->rb_right->rb_left == 0 by close();
            have node->rb_left == 0 by {
                rewrite(node, g->rb_right->rb_right); close();
            }
            let n_right = fold(sized_at(0), { model: SizedTree::Empty });
            let n_left = fold(sized_at(0), { model: SizedTree::Empty });
            let focus = fold(sized_at(node), { model: SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), metadata: n_size, right: n_right, left: n_left });
            have p->rb_right == node by { close(); }
            have p->rb_right != p by {
                close();
            }
            unfold(p_left);
            have p->rb_left == 0 by close();
            have p->rb_left != p by { rewrite(p->rb_left, 0); close(); }
            let p_left = fold(sized_at(0), { model: SizedTree::Empty });
            have separate(memory(p->__rb_parent_color), memory(g->__rb_parent_color)) by close();
            have p != g by close();
            have g->rb_right == p by close();
            have g->rb_right != g by { rewrite(g->rb_right, p); close(); }
            unfold(g_left);
            have g->rb_left == 0 by close();
            have g->rb_left != g by { rewrite(g->rb_left, 0); close(); }
            let g_left = fold(sized_at(0), { model: SizedTree::Empty });
            let parent_tree = fold(sized_at(p), { model: SizedTree::Node(p, g, Color::Red, 2, SizedTree::Empty, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty)), metadata: p_size, right: focus, left: p_left });
            have sized_parent_is(SizedTree::Node(p, g, Color::Red, 2, SizedTree::Empty, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty)), g) == 1 by {
                unfold(sized_parent_is(SizedTree::Node(p, g, Color::Red, 2, SizedTree::Empty, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty)), g)); normalize();
            }
            unfold(sized_value(SizedTree::Node(p, g, Color::Red, 2, SizedTree::Empty, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))));
            unfold(sized_value(SizedTree::Empty));
            have to_integer(3) == 1 + to_integer(sized_value(SizedTree::Empty)) + to_integer(sized_value(SizedTree::Node(p, g, Color::Red, 2, SizedTree::Empty, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty)))) by {
                rewrite(sized_value(SizedTree::Node(p, g, Color::Red, 2, SizedTree::Empty, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))), 2);
                rewrite(sized_value(SizedTree::Empty), 0);
                normalize();
            }
            let tree = fold(sized_at(g), { model: old(state.model), metadata: g_size, right: parent_tree, left: g_left });
            let state = fold(sized_insert_right_three_at(node, root), { phase: SizedInsertRightThreePhase::Before(g, p), model: old(state.model), tree: tree });
            step(); // Declare tmp before entering the loop.
            loop {
                owns state: sized_insert_right_three_at(node, root);
                decreases 0;
                invariant node == old(node);
                invariant parent == p;
                invariant g == old(root->rb_node);
                invariant p == old(g->rb_right);
                invariant g->rb_right == p;
                invariant p->rb_right == node;
                invariant state.phase == SizedInsertRightThreePhase::Before(g, p);
                invariant old(state.phase) == SizedInsertRightThreePhase::Before(g, p);
                invariant state.model == sized_right_three_before(g, p, node);
                initialize by close();
                maintain by {
                    let { tree: loop_tree } = unfold(state);
                    unfold(sized_right_three_before(g, p, node));
                    have loop_tree.model == SizedTree::Node(g, 0, Color::Black, 3, SizedTree::Empty, SizedTree::Node(p, g, Color::Red, 2, SizedTree::Empty, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))) by {
                        rewrite(loop_tree.model, sized_right_three_before(g, p, node));
                        unfold(sized_right_three_before(g, p, node)); normalize();
                    }
                    let { metadata: g_size, right: parent_tree, left: g_left } = unfold(loop_tree);
                    let { metadata: p_size, right: focus, left: p_left } = unfold(parent_tree);
                    have p->rb_right == node by close();
                    let parent_focus = fold(sized_rotation_saved_link(&p->rb_right), { child: node });
                    unfold(g_left); unfold(p_left);
                    let { metadata: n_size, right: n_right, left: n_left } = unfold(focus);
                    let focus = fold(sized_at(node), { model: SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), metadata: n_size, right: n_right, left: n_left });
                    unfold(color_bit(Color::Red)); unfold(color_bit(Color::Black));
                    have p->__rb_parent_color == address(g) by {
                        rewrite(p->__rb_parent_color, address(g) + (p->__rb_parent_color & 1));
                        rewrite((p->__rb_parent_color & 1), color_bit(Color::Red));
                        rewrite(color_bit(Color::Red), 0); normalize();
                    }
                    have g->__rb_parent_color == 1 by {
                        rewrite(g->__rb_parent_color, address(0) + (g->__rb_parent_color & 1));
                        rewrite((g->__rb_parent_color & 1), color_bit(Color::Black));
                        rewrite(color_bit(Color::Black), 1); normalize();
                    }
                    let rotating_word = fold(sized_rotation_entry_word(g), {
                        up: 0 as (int32*), word: 1u64, color: Color::Black
                    });
                    step(); step(); step(); step(); step(); step(); step();
                    have gparent == g by { close(); }
                    have parent == p by { close(); }
                    step(); step(); step(); step();
                    have tmp == 0 by { close(); }
                    have node != 0 by { close(); }
                    have separate(memory(gparent->rb_left), memory(gparent->rb_right));
                    have separate(memory(gparent->rb_left), memory(parent->rb_left));
                    have separate(memory(gparent->rb_left), memory(gparent->__rb_parent_color));
                    have separate(memory(gparent->rb_left), memory(parent->__rb_parent_color));
                    have separate(memory(gparent->rb_left), memory(root->rb_node));
                    have gparent->rb_right == parent by { close(); }
                    step(); step(); step(); // Skip the inner rotation.
                    have gparent->rb_left == 0 by close();
                    let grand_sibling = fold(sized_rotation_saved_link(&gparent->rb_left), { child: 0 as (int32*) });
                    step(); // Replace the grandparent's child link.
                    have gparent->rb_right == 0 by { close(); }
                    let grand_middle = fold(sized_rotation_saved_link(&gparent->rb_right), { child: 0 as (int32*) });
                    step(); // Link the demoted grandparent to the promoted parent.
                    have parent->rb_left == gparent by close();
                    have p->rb_left == g by {
                        rewrite(p, parent);
                        rewrite(g, gparent);
                        close();
                    }
                    let rotated_link = fold(sized_rotation_saved_link(&p->rb_left), { child: g });
                    step(); step(); // The middle child is null.
                    unfold(rotating_word);
                    have gparent->__rb_parent_color == 1 by close();
                    step(insert::__rb_rotate_set_parents, {});
                    unfold(grand_middle);
                    have g->rb_right == 0 by { close(); }
                    let p_left = fold(sized_at(0), { model: SizedTree::Empty });
                    unfold(grand_sibling);
                    have g->rb_left == 0 by { close(); }
                    let g_left = fold(sized_at(0), { model: SizedTree::Empty });
                    let demoted = fold(sized_recompute_at(g), {
                        model: SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty),
                        metadata: g_size, right: p_left, left: g_left
                    });
                    unfold(parent_focus);
                    unfold(rotated_link);
                    have p->rb_left == g by close();
                    have parent == p by { close(); }
                    have parent->__rb_parent_color == 1 by close();
                    have p->__rb_parent_color == 1 by { close(); }
                    have ((p->__rb_parent_color & ~3) as (struct rb_node *)) == 0 by {
                        rewrite(p->__rb_parent_color, 1); normalize();
                    }
                    have p->__rb_parent_color == (p->__rb_parent_color & 1) by {
                        rewrite(p->__rb_parent_color, 1); normalize();
                    }
                    have (p->__rb_parent_color & 1) == color_bit(Color::Black) by {
                        rewrite(p->__rb_parent_color, 1);
                        rewrite(color_bit(Color::Black), 1); normalize();
                    }
                    have sized_parent_is(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), p) == 1 by {
                        unfold(sized_parent_is(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), p)); normalize();
                    }
                    have sized_parent_is(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), p) == 1 by {
                        unfold(sized_parent_is(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), p)); normalize();
                    }
                    have to_integer(sized_value(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))) == 2 + to_integer(sized_value(sized_left(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)))) + to_integer(sized_value(sized_right(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)))) + to_integer(sized_value(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))) by {
                        unfold(sized_value(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)));
                        unfold(sized_right(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)));
                        unfold(sized_left(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)));
                        unfold(sized_value(SizedTree::Empty));
                        unfold(sized_value(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))); normalize();
                    }
                    let rotated = fold(sized_rotation_left_at(g, p), {
                        model: SizedTree::Node(p, 0, Color::Black, 2, SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty)),
                        metadata: p_size, other: focus, demoted: demoted
                    });
                    unfold(sized_left(SizedTree::Node(p, 0, Color::Black, 2, SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))));
                    unfold(sized_left(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)));
                    unfold(sized_right(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)));
                    unfold(sized_value(SizedTree::Empty));
                    have 0 <= sized_value(sized_left(sized_left(SizedTree::Node(p, 0, Color::Black, 2, SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))))) by {
                        rewrite(sized_left(SizedTree::Node(p, 0, Color::Black, 2, SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))), SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty));
                        rewrite(sized_left(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty), 0); normalize();
                    }
                    have 0 <= sized_value(sized_right(sized_left(SizedTree::Node(p, 0, Color::Black, 2, SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))))) by {
                        rewrite(sized_left(SizedTree::Node(p, 0, Color::Black, 2, SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))), SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty));
                        rewrite(sized_right(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty), 0); normalize();
                    }
                    have sized_value(sized_right(sized_left(SizedTree::Node(p, 0, Color::Black, 2, SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))))) <= 2147483646 by {
                        rewrite(sized_left(SizedTree::Node(p, 0, Color::Black, 2, SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))), SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty));
                        rewrite(sized_right(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty), 0); normalize();
                    }
                    have sized_value(sized_left(sized_left(SizedTree::Node(p, 0, Color::Black, 2, SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))))) <= 2147483646 - sized_value(sized_right(sized_left(SizedTree::Node(p, 0, Color::Black, 2, SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))))) by {
                        rewrite(sized_left(SizedTree::Node(p, 0, Color::Black, 2, SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))), SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty));
                        rewrite(sized_left(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty);
                        rewrite(sized_right(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty), 0); normalize();
                    }
                    let { checked: checked } = step(RotateTreeLeft, { tree: rotated });
                    have sized_shape(checked.model) == sized_right_three_after(g, p, node) by {
                        rewrite(sized_shape(checked.model), sized_shape(SizedTree::Node(p, 0, Color::Black, 2, SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))));
                        unfold(sized_shape(SizedTree::Node(p, 0, Color::Black, 2, SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))));
                        unfold(sized_shape(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty)));
                        unfold(sized_shape(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)));
                        unfold(sized_shape(SizedTree::Empty));
                        unfold(sized_right_three_after(g, p, node)); normalize();
                    }
                    let state = fold(sized_insert_right_three_at(node, root), {
                        phase: SizedInsertRightThreePhase::After(g, p), model: checked.model,
                        tree: checked
                    });
                    have state.phase == sized_right_three_finish(old(state.phase)) by {
                        unfold(sized_right_three_finish(SizedInsertRightThreePhase::Before(g, p))); close();
                    }
                    have sized_shape(state.model) == sized_right_three_expected(old(state.phase), node) by {
                        rewrite(old(state.phase), SizedInsertRightThreePhase::Before(g, p));
                        unfold(sized_right_three_expected(SizedInsertRightThreePhase::Before(g, p), node)); close();
                    }
                    step();
                }
            }
            have node == old(node) by { close(); }
            step_until(function.exit);
        },
    }
}

void insert::__rb_insert_augmented(struct rb_node* node, struct rb_root* root,
                  void (*augment_rotate)(struct rb_node*, struct rb_node*)) {
    requires RotateTreeLeft(augment_rotate);
    owns state: sized_insert_right_three_at(node, root);
    requires sized_right_three_pending(state.phase) == 1;
    ensures state.phase == sized_right_three_finish(old(state.phase));
    ensures sized_shape(state.model) == sized_right_three_expected(old(state.phase), node);
} by {
    step(insert::__rb_insert, { state: state });
}

void insert::rb_insert_augmented(struct rb_node* node, struct rb_root* root,
                         const struct rb_augment_callbacks* augment) {
    views augment->rotate;
    requires RotateTreeLeft(augment->rotate);
    owns state: sized_insert_right_three_at(node, root);
    requires sized_right_three_pending(state.phase) == 1;
    ensures state.phase == sized_right_three_finish(old(state.phase));
    ensures sized_shape(state.model) == sized_right_three_expected(old(state.phase), node);
} by {
    have separate(state, memory(augment->rotate)) by close();
    step(insert::__rb_insert_augmented, { state: state });
}
