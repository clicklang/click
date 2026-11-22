// Two writable insertion callbacks: a left-right three-node rotation at the root.
verifying "rb_insert_augmented.c" as insert;
verifying "rbtree_size_rotate.c";
verifying "rbtree_size_copy.c";
verifying "rbtree_size_compute.c";
import "rbtree_size_rotate_model.click";
import "rbtree_size_model_unique.click";
import "rbtree_size_reparent_preserve_color_call.click";
import "rbtree_size_rotate_root_parents.click";

spec enum SizedInsertDoublePhase {
    Before(struct rb_node*, struct rb_node*),
    After(struct rb_node*, struct rb_node*),
}

function sized_double_pending(phase: SizedInsertDoublePhase) -> int32 {
    match phase {
        SizedInsertDoublePhase::Before(g, p) => 1,
        SizedInsertDoublePhase::After(g, p) => 0,
    }
}

function sized_double_finish(phase: SizedInsertDoublePhase) -> SizedInsertDoublePhase {
    match phase {
        SizedInsertDoublePhase::Before(g, p) => SizedInsertDoublePhase::After(g, p),
        SizedInsertDoublePhase::After(g, p) => SizedInsertDoublePhase::After(g, p),
    }
}

function sized_double_before(g: struct rb_node*, p: struct rb_node*, n: struct rb_node*) -> SizedTree {
    SizedTree::Node(g, 0, Color::Black, 3,
        SizedTree::Node(p, g, Color::Red, 2,
            SizedTree::Empty, SizedTree::Node(n, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty)
}

function sized_double_after(g: struct rb_node*, p: struct rb_node*, n: struct rb_node*) -> RbTree {
    RbTree::Node(n, 0, Color::Black,
        RbTree::Node(p, n, Color::Red, RbTree::Empty, RbTree::Empty),
        RbTree::Node(g, n, Color::Red, RbTree::Empty, RbTree::Empty))
}

function sized_double_expected(phase: SizedInsertDoublePhase, node: struct rb_node*) -> RbTree {
    match phase {
        SizedInsertDoublePhase::Before(g, p) => sized_double_after(g, p, node),
        SizedInsertDoublePhase::After(g, p) => sized_double_after(g, p, node),
    }
}

resource sized_insert_double_at(node: struct rb_node*, root: struct rb_root*) {
    field phase: SizedInsertDoublePhase;
    field model: SizedTree;
    match phase {
        SizedInsertDoublePhase::Before(g, p) => {
            owns root->rb_node;
            owns tree: sized_at(g);
            fact root->rb_node == g;
            fact tree.model == model;
            fact model == sized_double_before(g, p, node);
        },
        SizedInsertDoublePhase::After(g, p) => {
            owns root->rb_node;
            owns tree: sized_at(node);
            fact root->rb_node == node;
            fact tree.model == model;
        },
    }
}

void insert::__rb_insert(struct rb_node* node, struct rb_root* root,
                  void (*augment_rotate)(struct rb_node*, struct rb_node*)) {
    requires RotateTreeRight(augment_rotate);
    requires RotateTreeLeft(augment_rotate);
    owns state: sized_insert_double_at(node, root);
    requires sized_double_pending(state.phase) == 1;
    ensures state.phase == sized_double_finish(old(state.phase));
    ensures sized_shape(state.model) == sized_double_expected(old(state.phase), node);
} by {
    match state.phase {
        SizedInsertDoublePhase::After(g, p) => {
            have sized_double_pending(state.phase) != 1 by {
                rewrite(state.phase, SizedInsertDoublePhase::After(g, p));
                unfold(sized_double_pending(SizedInsertDoublePhase::After(g, p))); normalize();
            }
            contradiction(sized_double_pending(state.phase) == 1);
        },
        SizedInsertDoublePhase::Before(g, p) => {
            let { tree: tree } = unfold(state);
            unfold(sized_double_before(g, p, node));
            have tree.model == SizedTree::Node(g, 0, Color::Black, 3,
                SizedTree::Node(p, g, Color::Red, 2,
                    SizedTree::Empty, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty) by {
                rewrite(tree.model, sized_double_before(g, p, node));
                unfold(sized_double_before(g, p, node)); normalize();
            }
            let { metadata: g_size, left: parent_tree, right: g_right } = unfold(tree);
            let { metadata: p_size, left: p_left, right: focus } = unfold(parent_tree);
            let { metadata: n_size, left: n_left, right: n_right } = unfold(focus);
            unfold(color_bit(Color::Red));
            have (node->__rb_parent_color & 1) == 0 by {
                rewrite((node->__rb_parent_color & 1), color_bit(Color::Red));
                rewrite(color_bit(Color::Red), 0); normalize();
            }
            have node->__rb_parent_color == address(p) by {
                rewrite(node->__rb_parent_color, address(p) + (node->__rb_parent_color & 1));
                rewrite((node->__rb_parent_color & 1), 0); normalize();
            }
            have g->rb_left == p by known();
            have ((g->rb_left->__rb_parent_color & ~3) as (struct rb_node*)) == g by known();
            have p->__rb_parent_color == g->rb_left->__rb_parent_color by {
                rewrite(p, g->rb_left); known();
            }
            have ((p->__rb_parent_color & ~3) as (struct rb_node*)) == g by {
                rewrite(p->__rb_parent_color, g->rb_left->__rb_parent_color); known();
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
            unfold(n_left); unfold(n_right);
            have g->rb_left->rb_right == node by known();
            have g->rb_left->rb_right->rb_left == 0 by known();
            have g->rb_left->rb_right->rb_right == 0 by known();
            have node->rb_left == 0 by { rewrite(node, g->rb_left->rb_right); known(); }
            have node->rb_right == 0 by { rewrite(node, g->rb_left->rb_right); known(); }
            let n_left = fold(sized_at(0), { model: SizedTree::Empty });
            let n_right = fold(sized_at(0), { model: SizedTree::Empty });
            let focus = fold(sized_at(node), { model: SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), metadata: n_size, left: n_left, right: n_right });
            have p->rb_right == node by { known(); }
            unfold(p_left);
            have p->rb_left == 0 by known();
            have p->rb_left != p by { rewrite(p->rb_left, 0); known(); }
            let p_left = fold(sized_at(0), { model: SizedTree::Empty });
            have p->rb_right != p by {
                known();
            }
            have g->rb_left == p by known();
            have g->rb_left->__rb_parent_color == address(g) + (g->rb_left->__rb_parent_color & 1) by known();
            have p->__rb_parent_color == address(g) + (p->__rb_parent_color & 1) by {
                rewrite(p, g->rb_left); known();
            }
            have separate(memory(p->__rb_parent_color), memory(g->__rb_parent_color)) by known();
            have p != g by known();
            have g->rb_left != g by { rewrite(g->rb_left, p); known(); }
            let parent_tree = fold(sized_at(p), { model: SizedTree::Node(p, g, Color::Red, 2, SizedTree::Empty, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty)), metadata: p_size, left: p_left, right: focus });
            unfold(g_right);
            have g->rb_right == 0 by known();
            have g->rb_right != g by { rewrite(g->rb_right, 0); known(); }
            let g_right = fold(sized_at(0), { model: SizedTree::Empty });
            unfold(color_bit(Color::Black));
            have g->__rb_parent_color == 1 by {
                rewrite(g->__rb_parent_color, address(0u64 as (int32 *)) + (g->__rb_parent_color & 1));
                rewrite((g->__rb_parent_color & 1), color_bit(Color::Black));
                rewrite(color_bit(Color::Black), 1); normalize();
            }
            have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == 0 by {
                rewrite(g->__rb_parent_color, 1); normalize();
            }
            have sized_parent_is(SizedTree::Node(p, g, Color::Red, 2, SizedTree::Empty, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty)), g) == 1 by {
                unfold(sized_parent_is(SizedTree::Node(p, g, Color::Red, 2, SizedTree::Empty, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty)), g)); normalize();
            }
            unfold(sized_value(SizedTree::Node(p, g, Color::Red, 2, SizedTree::Empty, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))));
            unfold(sized_value(SizedTree::Empty));
            have to_integer(3) == 1 + to_integer(sized_value(SizedTree::Node(p, g, Color::Red, 2, SizedTree::Empty, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty)))) + to_integer(sized_value(SizedTree::Empty)) by {
                rewrite(sized_value(SizedTree::Node(p, g, Color::Red, 2, SizedTree::Empty, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))), 2);
                rewrite(sized_value(SizedTree::Empty), 0); normalize();
            }
            let tree = fold(sized_at(g), { model: old(state.model), metadata: g_size, left: parent_tree, right: g_right });
            let state = fold(sized_insert_double_at(node, root), { phase: SizedInsertDoublePhase::Before(g, p), model: old(state.model), tree: tree });
            step(); // Declare tmp before entering the loop.
            loop {
                owns state: sized_insert_double_at(node, root);
                decreases 0;
                invariant node == old(node);
                invariant parent == p;
                invariant g == old(root->rb_node);
                invariant p == old(g->rb_left);
                invariant state.phase == SizedInsertDoublePhase::Before(g, p);
                invariant old(state.phase) == SizedInsertDoublePhase::Before(g, p);
                invariant state.model == sized_double_before(g, p, node);
                initialize by solve();
                maintain by {
                    let { tree: loop_tree } = unfold(state);
                    unfold(sized_double_before(g, p, node));
                    have loop_tree.model == SizedTree::Node(g, 0, Color::Black, 3,
                        SizedTree::Node(p, g, Color::Red, 2,
                            SizedTree::Empty, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty) by {
                        rewrite(loop_tree.model, sized_double_before(g, p, node));
                        unfold(sized_double_before(g, p, node)); normalize();
                    }
                    let { metadata: g_size, left: parent_tree, right: g_right } = unfold(loop_tree);
                    let { metadata: p_size, left: p_left, right: focus } = unfold(parent_tree);
                    unfold(g_right); unfold(p_left);
                    let { metadata: n_size, left: n_left, right: n_right } = unfold(focus);
                    let focus = fold(sized_at(node), { model: SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), metadata: n_size, left: n_left, right: n_right });
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
                    have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == 0 by {
                        rewrite(g->__rb_parent_color, 1); normalize();
                    }
                    let root_tag = fold(sized_root_rotation_parent_word(g, 0), { bits: 1u64 });
                    have g->rb_right == 0 by known();
                    let uncle_link = fold(sized_rotation_saved_link(&g->rb_right), { child: 0 as (int32*) });
                    step(); step(); step(); step(); step(); step(); step();
                    have gparent == g by { known(); }
                    have parent == p by { known(); }
                    step(); step(); step();
                    have parent->rb_right == node by { rewrite(parent, p); known(); }
                    step(); // Load the inner-rotation pivot into tmp.
                    have tmp == node by { known(); }
                    step();
                    let { metadata: n_size, left: n_left, right: n_right } = unfold(focus);
                    unfold(n_left); unfold(n_right);
                    have node->rb_right == 0 by { known(); }
                    have gparent->rb_left == parent by { known(); }
                    have separate(memory(node->rb_right), memory(parent->rb_right));
                    have separate(memory(node->rb_right), memory(node->rb_left));
                    have separate(memory(node->rb_right), memory(parent->__rb_parent_color));
                    have separate(memory(node->__rb_parent_color), memory(parent->rb_right));
                    have separate(memory(node->__rb_parent_color), memory(node->rb_left));
                    have separate(memory(node->__rb_parent_color), memory(parent->__rb_parent_color));
                    have parent->rb_left == 0 by { rewrite(parent, p); known(); }
                    let saved_left = fold(sized_rotation_saved_link(&parent->rb_left), { child: 0 as (int32*) });
                    let parent_word = fold(sized_rotation_entry_word(p), {
                        up: g, word: p->__rb_parent_color, color: Color::Red
                    });
                    let node_tag = fold(sized_rotation_entry_word(node), {
                        up: p, word: node->__rb_parent_color, color: Color::Red
                    });
                    let node_right = fold(sized_rotation_saved_link(&node->rb_right), { child: 0 as (int32*) });
                    step(); step();
                    have parent->rb_right == 0 by known();
                    let saved_right = fold(sized_rotation_saved_link(&parent->rb_right), { child: 0 as (int32*) });
                    step();
                    have node->rb_left == parent by { known(); }
                    have separate(memory(node->rb_left), memory(parent->__rb_parent_color));
                    let node_left = fold(sized_rotation_saved_link(&node->rb_left), { child: parent });

                    step_until(call(rb_set_parent_color, 5).entry);
                    unfold(saved_left);
                    unfold(saved_right);
                    unfold(parent_word);
                    have p->rb_left == 0 by { rewrite(p, parent); known(); }
                    have p->rb_right == 0 by { rewrite(p, parent); known(); }
                    let p_left = fold(sized_at(0), { model: SizedTree::Empty });
                    let p_right = fold(sized_at(0), { model: SizedTree::Empty });
                    let before_parent_update = fold(sized_recompute_at(p), {
                        model: SizedTree::Node(p, g, Color::Red, 2, SizedTree::Empty, SizedTree::Empty),
                        metadata: p_size, left: p_left, right: p_right
                    });
                    unfold(sized_root_color_bit(SizedTree::Node(p, g, Color::Red, 2, SizedTree::Empty, SizedTree::Empty)));
                    have 0 == sized_root_color_bit(before_parent_update.model) by known();
                    let { after: demoted } = step(insert::rb_set_parent_color, { tree: before_parent_update });
                    unfold(sized_reparent(SizedTree::Node(p, g, Color::Red, 2, SizedTree::Empty, SizedTree::Empty), node));
                    have demoted.model == SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty) by known();
                    unfold(node_tag);
                    unfold(node_right);
                    unfold(node_left);
                    have node->rb_right == 0 by known();
                    have node->rb_left == p by { rewrite(p, parent); known(); }
                    let other = fold(sized_at(0), { model: SizedTree::Empty });
                    have sized_parent_is(SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty), node) == 1 by { unfold(sized_parent_is(SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty), node)); normalize(); }
                    have sized_parent_is(SizedTree::Empty, node) == 1 by { unfold(sized_parent_is(SizedTree::Empty, node)); normalize(); }
                    unfold(sized_value(SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty)));
                    unfold(sized_left(SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty)));
                    unfold(sized_right(SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty)));
                    unfold(sized_value(SizedTree::Empty));
                    have to_integer(sized_value(SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty))) == 2 + to_integer(sized_value(sized_left(SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty)))) + to_integer(sized_value(sized_right(SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty)))) + to_integer(sized_value(SizedTree::Empty)) by {
                        rewrite(sized_left(SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty);
                        rewrite(sized_right(SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty)), 2);
                        rewrite(sized_value(SizedTree::Empty), 0); normalize();
                    }
                    let rotated = fold(sized_rotation_left_at(p, node), { model: SizedTree::Node(node, p, Color::Red, 1, SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty), metadata: n_size, demoted: demoted, other: other });
                    unfold(sized_left(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty)));
                    have 0 <= sized_value(sized_left(sized_left(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty)))) by { rewrite(sized_left(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty)), SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty)); rewrite(sized_left(SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty); rewrite(sized_value(SizedTree::Empty), 0); normalize(); }
                    have 0 <= sized_value(sized_right(sized_left(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty)))) by { rewrite(sized_left(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty)), SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty)); rewrite(sized_right(SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty); rewrite(sized_value(SizedTree::Empty), 0); normalize(); }
                    have sized_value(sized_right(sized_left(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty)))) <= 2147483646 by { rewrite(sized_left(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty)), SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty)); rewrite(sized_right(SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty); rewrite(sized_value(SizedTree::Empty), 0); normalize(); }
                    have sized_value(sized_left(sized_left(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty)))) <= 2147483646 - sized_value(sized_right(sized_left(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty)))) by { rewrite(sized_left(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty)), SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty)); rewrite(sized_left(SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty); rewrite(sized_right(SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty); rewrite(sized_value(SizedTree::Empty), 0); normalize(); }
                    let { checked: first } = step(RotateTreeLeft, { tree: rotated });
                    let { checked: first } = certify_size(node, { tree: first });
                    have sized_counts_valid(SizedTree::Node(node, p, Color::Red, 2, SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty)) == 1 by {
                        unfold(sized_counts_valid(SizedTree::Node(node, p, Color::Red, 2, SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty)));
                        unfold(sized_counts_valid(SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty)));
                        unfold(sized_counts_valid(SizedTree::Empty));
                        unfold(sized_value(SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty)));
                        unfold(sized_value(SizedTree::Empty)); solve();
                    }
                    have sized_shape(first.model) == sized_shape(SizedTree::Node(node, p, Color::Red, 2, SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty)) by {
                        rewrite(sized_shape(first.model), sized_shape(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty)));
                        unfold(sized_shape(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty)));
                        unfold(sized_shape(SizedTree::Node(node, p, Color::Red, 2, SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty)));
                        unfold(sized_shape(SizedTree::Node(p, node, Color::Red, 2, SizedTree::Empty, SizedTree::Empty)));
                        unfold(sized_shape(SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))); normalize();
                    }
                    apply(sized_model_unique(first.model, SizedTree::Node(node, p, Color::Red, 2, SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty)));
                    have first.model == SizedTree::Node(node, p, Color::Red, 2, SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty) by { known(); }
                    let { metadata: n_size, left: p_leaf, right: outer_empty } = unfold(first);
                    unfold(outer_empty);
                    have separate(memory(node->rb_left), memory(gparent->rb_left));
                    have separate(memory(node->rb_left), memory(node->rb_right));
                    have separate(memory(node->rb_left), memory(gparent->__rb_parent_color));
                    have separate(memory(node->rb_left), memory(node->__rb_parent_color));
                    have separate(memory(node->rb_left), memory(root->rb_node));
                    let { metadata: p_size, left: p_empty_left, right: p_empty_right } = unfold(p_leaf);
                    have node->rb_left == p by known();
                    let p_leaf = fold(sized_at(p), {
                        model: SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty),
                        metadata: p_size, left: p_empty_left, right: p_empty_right
                    });
                    let pivot_left = fold(sized_rotation_saved_link(&node->rb_left), { child: p });
                    step(); step(); step();
                    have gparent->rb_left == 0 by known();
                    let grand_left = fold(sized_rotation_saved_link(&gparent->rb_left), { child: 0 as (int32*) });
                    step();
                    have parent->rb_right == gparent by known();
                    let pivot_right = fold(sized_rotation_saved_link(&parent->rb_right), { child: gparent });
                    step(); step();
                    unfold(root_tag);
                    have gparent == g by known();
                    have gparent->__rb_parent_color == 1 by known();
                    step(insert::__rb_rotate_set_parents, {});
                    unfold(grand_left);
                    have g->rb_left == 0 by { known(); }
                    let g_left = fold(sized_at(0), { model: SizedTree::Empty });
                    unfold(uncle_link);
                    have g->rb_right == 0 by { known(); }
                    let g_right = fold(sized_at(0), { model: SizedTree::Empty });
                    have gparent->__rb_parent_color == address(node) by {
                        rewrite(node, parent); known();
                    }
                    have (gparent->__rb_parent_color & 1) == 0 by {
                        rewrite(gparent->__rb_parent_color, address(node));
                        solve() using { aligned(node, 8); };
                    }
                    have gparent->__rb_parent_color == address(node) + (gparent->__rb_parent_color & 1) by {
                        rewrite(gparent->__rb_parent_color, address(node));
                        rewrite((address(node) & 1), 0); normalize();
                    }
                    have separate(memory(gparent->__rb_parent_color), memory(parent->__rb_parent_color)) by known();
                    have gparent != parent by known();
                    let demoted = fold(sized_recompute_at(g), {
                        model: SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty),
                        metadata: g_size, left: g_left, right: g_right
                    });
                    unfold(pivot_left);
                    unfold(pivot_right);
                    have node->rb_right == g by {
                        rewrite(node, parent);
                        rewrite(g, gparent);
                        known();
                    }
                    have node->rb_right != node by {
                        rewrite(node->rb_right, g);
                        rewrite(g, gparent);
                        rewrite(node, parent); known();
                    }
                    have parent == node by { known(); }
                    have parent->__rb_parent_color == 1 by known();
                    have node->__rb_parent_color == 1 by { rewrite(node, parent); known(); }
                    have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == 0 by {
                        rewrite(node->__rb_parent_color, 1); normalize();
                    }
                    have node->__rb_parent_color == (node->__rb_parent_color & 1) by {
                        rewrite(node->__rb_parent_color, 1); normalize();
                    }
                    have (node->__rb_parent_color & 1) == color_bit(Color::Black) by {
                        rewrite(node->__rb_parent_color, 1);
                        rewrite(color_bit(Color::Black), 1); normalize();
                    }
                    have sized_parent_is(SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), node) == 1 by {
                        unfold(sized_parent_is(SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), node)); normalize();
                    }
                    have sized_parent_is(SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), node) == 1 by {
                        unfold(sized_parent_is(SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), node)); normalize();
                    }
                    have to_integer(sized_value(SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))) == 2 + to_integer(sized_value(sized_left(SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)))) + to_integer(sized_value(sized_right(SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)))) + to_integer(sized_value(SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))) by {
                        unfold(sized_value(SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)));
                        unfold(sized_left(SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)));
                        unfold(sized_right(SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)));
                        unfold(sized_value(SizedTree::Empty));
                        unfold(sized_value(SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))); normalize();
                    }
                    let second_rotated = fold(sized_rotation_right_at(g, node), {
                        model: SizedTree::Node(node, 0, Color::Black, 2,
                            SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty),
                            SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)),
                        metadata: n_size, other: p_leaf, demoted: demoted
                    });
                    unfold(sized_right(SizedTree::Node(node, 0, Color::Black, 2, SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))));
                    unfold(sized_left(SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)));
                    unfold(sized_right(SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)));
                    unfold(sized_value(SizedTree::Empty));
                    have 0 <= sized_value(sized_left(sized_right(SizedTree::Node(node, 0, Color::Black, 2, SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))))) by {
                        rewrite(sized_right(SizedTree::Node(node, 0, Color::Black, 2, SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))), SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty));
                        rewrite(sized_left(SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty), 0); normalize();
                    }
                    have 0 <= sized_value(sized_right(sized_right(SizedTree::Node(node, 0, Color::Black, 2, SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))))) by {
                        rewrite(sized_right(SizedTree::Node(node, 0, Color::Black, 2, SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))), SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty));
                        rewrite(sized_right(SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty), 0); normalize();
                    }
                    have sized_value(sized_right(sized_right(SizedTree::Node(node, 0, Color::Black, 2, SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))))) <= 2147483646 by {
                        rewrite(sized_right(SizedTree::Node(node, 0, Color::Black, 2, SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))), SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty));
                        rewrite(sized_right(SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty), 0); normalize();
                    }
                    have sized_value(sized_left(sized_right(SizedTree::Node(node, 0, Color::Black, 2, SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))))) <= 2147483646 - sized_value(sized_right(sized_right(SizedTree::Node(node, 0, Color::Black, 2, SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))))) by {
                        rewrite(sized_right(SizedTree::Node(node, 0, Color::Black, 2, SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))), SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty));
                        rewrite(sized_left(SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty);
                        rewrite(sized_right(SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty), 0); normalize();
                    }
                    let { checked: second } = step(RotateTreeRight, { tree: second_rotated });
                    have sized_shape(second.model) == sized_double_after(g, p, node) by {
                        rewrite(sized_shape(second.model), sized_shape(SizedTree::Node(node, 0, Color::Black, 2, SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))));
                        unfold(sized_shape(SizedTree::Node(node, 0, Color::Black, 2, SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))));
                        unfold(sized_shape(SizedTree::Node(p, node, Color::Red, 1, SizedTree::Empty, SizedTree::Empty)));
                        unfold(sized_shape(SizedTree::Node(g, node, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)));
                        unfold(sized_shape(SizedTree::Empty));
                        unfold(sized_double_after(g, p, node)); normalize();
                    }
                    let state = fold(sized_insert_double_at(node, root), {
                        phase: SizedInsertDoublePhase::After(g, p), model: second.model,
                        tree: second
                    });
                    have state.phase == sized_double_finish(old(state.phase)) by {
                        unfold(sized_double_finish(SizedInsertDoublePhase::Before(g, p))); solve();
                    }
                    have sized_shape(state.model) == sized_double_expected(old(state.phase), node) by {
                        rewrite(old(state.phase), SizedInsertDoublePhase::Before(g, p));
                        unfold(sized_double_expected(SizedInsertDoublePhase::Before(g, p), node)); solve();
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
    requires RotateTreeRight(augment_rotate);
    requires RotateTreeLeft(augment_rotate);
    owns state: sized_insert_double_at(node, root);
    requires sized_double_pending(state.phase) == 1;
    ensures state.phase == sized_double_finish(old(state.phase));
    ensures sized_shape(state.model) == sized_double_expected(old(state.phase), node);
} by {
    step(insert::__rb_insert, { state: state });
}

void insert::rb_insert_augmented(struct rb_node* node, struct rb_root* root,
                         const struct rb_augment_callbacks* augment) {
    views augment->rotate;
    requires RotateTreeRight(augment->rotate);
    requires RotateTreeLeft(augment->rotate);
    owns state: sized_insert_double_at(node, root);
    requires sized_double_pending(state.phase) == 1;
    ensures state.phase == sized_double_finish(old(state.phase));
    ensures sized_shape(state.model) == sized_double_expected(old(state.phase), node);
} by {
    have separate(state, memory(augment->rotate)) by known();
    step(insert::__rb_insert_augmented, { state: state });
}
