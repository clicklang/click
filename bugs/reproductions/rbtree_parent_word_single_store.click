// Two writable insertion callbacks with arbitrary far and transferred subtrees.
verifying "rb_insert_augmented.c" as insert;
verifying "rbtree_size_rotate.c";
verifying "rbtree_size_copy.c";
verifying "rbtree_size_compute.c";
import "rbtree_size_rotate_model.click";
import "rbtree_size_model_unique.click";
import "rbtree_size_insert_double_subtree_model.click";
import "rbtree_size_valid_value.click";
import "rbtree_size_rotate_set_parents.click";
import "rbtree_size_reparent_preserve_color_call.click";
import "rbtree_size_double_middle_counts.click";

spec enum SizedInsertContextDoubleMiddleSubtreePhase {
    Before(struct rb_node*, struct rb_node*, struct rb_node*, int32, int32, SizedTree, struct rb_node*, int32, SizedTree, SizedTree, int32),
    After(struct rb_node*, struct rb_node*, struct rb_node*, int32, int32, SizedTree, struct rb_node*, int32, SizedTree, SizedTree, int32),
}

function sized_context_double_middle_subtree_pending(phase: SizedInsertContextDoubleMiddleSubtreePhase) -> int32 {
    match phase {
        SizedInsertContextDoubleMiddleSubtreePhase::Before(g, p, above, pv, gv, far, m, mv, middle_left, middle_right, nv) => 1,
        SizedInsertContextDoubleMiddleSubtreePhase::After(g, p, above, pv, gv, far, m, mv, middle_left, middle_right, nv) => 0,
    }
}

function sized_context_double_middle_subtree_finish(phase: SizedInsertContextDoubleMiddleSubtreePhase) -> SizedInsertContextDoubleMiddleSubtreePhase {
    match phase {
        SizedInsertContextDoubleMiddleSubtreePhase::Before(g, p, above, pv, gv, far, m, mv, middle_left, middle_right, nv) => SizedInsertContextDoubleMiddleSubtreePhase::After(g, p, above, pv, gv, far, m, mv, middle_left, middle_right, nv),
        SizedInsertContextDoubleMiddleSubtreePhase::After(g, p, above, pv, gv, far, m, mv, middle_left, middle_right, nv) => SizedInsertContextDoubleMiddleSubtreePhase::After(g, p, above, pv, gv, far, m, mv, middle_left, middle_right, nv),
    }
}

function sized_context_double_middle_subtree_before(g: struct rb_node*, p: struct rb_node*, n: struct rb_node*, above: struct rb_node*, pv: int32, gv: int32, far: SizedTree, m: struct rb_node*, mv: int32, middle_left: SizedTree, middle_right: SizedTree, nv: int32) -> SizedTree {
    SizedTree::Node(g, above, Color::Black, gv, SizedTree::Node(p, g, Color::Red, pv, far, SizedTree::Node(n, p, Color::Red, nv, SizedTree::Node(m, n, Color::Black, mv, middle_left, middle_right), SizedTree::Empty)), SizedTree::Empty)
}

function sized_context_double_middle_subtree_after(g: struct rb_node*, p: struct rb_node*, n: struct rb_node*, above: struct rb_node*, pv: int32, gv: int32, far: SizedTree, m: struct rb_node*, mv: int32, middle_left: SizedTree, middle_right: SizedTree, nv: int32) -> RbTree {
    RbTree::Node(n, above, Color::Black,
        RbTree::Node(p, n, Color::Red, sized_shape(far), sized_shape(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))),
        RbTree::Node(g, n, Color::Red, RbTree::Empty, RbTree::Empty))
}

function sized_context_double_middle_subtree_expected(phase: SizedInsertContextDoubleMiddleSubtreePhase, node: struct rb_node*) -> RbTree {
    match phase {
        SizedInsertContextDoubleMiddleSubtreePhase::Before(g, p, above, pv, gv, far, m, mv, middle_left, middle_right, nv) => sized_context_double_middle_subtree_after(g, p, node, above, pv, gv, far, m, mv, middle_left, middle_right, nv),
        SizedInsertContextDoubleMiddleSubtreePhase::After(g, p, above, pv, gv, far, m, mv, middle_left, middle_right, nv) => sized_context_double_middle_subtree_after(g, p, node, above, pv, gv, far, m, mv, middle_left, middle_right, nv),
    }
}

resource sized_insert_context_double_middle_subtree_at(node: struct rb_node*, root: struct rb_root*) {
    field phase: SizedInsertContextDoubleMiddleSubtreePhase;
    field model: SizedTree;
    field context: SizedContext;
    field whole_model: SizedTree;
    match phase {
        SizedInsertContextDoubleMiddleSubtreePhase::Before(g, p, above, pv, gv, far, m, mv, middle_left, middle_right, nv) => {
            owns link: sized_link_at(g, root, gv);
            owns tree: sized_at(g);
            fact link.model == context;
            fact above == sized_context_parent(context, 0);
            fact tree.model == model;
            fact model == sized_context_double_middle_subtree_before(g, p, node, above, pv, gv, far, m, mv, middle_left, middle_right, nv);
        },
        SizedInsertContextDoubleMiddleSubtreePhase::After(g, p, above, pv, gv, far, m, mv, middle_left, middle_right, nv) => {
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
    requires RotateTreeRight(augment_rotate);
    requires RotateTreeLeft(augment_rotate);
    owns state: sized_insert_context_double_middle_subtree_at(node, root);
    requires sized_context_double_middle_subtree_pending(state.phase) == 1;
    ensures state.context == old(state.context);
    ensures state.whole_model == sized_plug(old(state.context), state.model);
    ensures state.phase == sized_context_double_middle_subtree_finish(old(state.phase));
    ensures sized_shape(state.model) == sized_context_double_middle_subtree_expected(old(state.phase), node);
} by {
    match state.phase {
        SizedInsertContextDoubleMiddleSubtreePhase::After(g, p, above, pv, gv, far, m, mv, middle_left, middle_right, nv) => {
            have sized_context_double_middle_subtree_pending(state.phase) != 1 by {
                rewrite(state.phase == SizedInsertContextDoubleMiddleSubtreePhase::After(g, p, above, pv, gv, far, m, mv, middle_left, middle_right, nv));
                unfold(sized_context_double_middle_subtree_pending(SizedInsertContextDoubleMiddleSubtreePhase::After(g, p, above, pv, gv, far, m, mv, middle_left, middle_right, nv))); normalize();
            }
            contradiction(sized_context_double_middle_subtree_pending(state.phase) == 1);
        },
        SizedInsertContextDoubleMiddleSubtreePhase::Before(g, p, above, pv, gv, far, m, mv, middle_left, middle_right, nv) => {
            let { tree: tree, link: link } = unfold(state);
            unfold(sized_context_double_middle_subtree_before(g, p, node, above, pv, gv, far, m, mv, middle_left, middle_right, nv));
            have tree.model == SizedTree::Node(g, above, Color::Black, gv, SizedTree::Node(p, g, Color::Red, pv, far, SizedTree::Node(node, p, Color::Red, nv, SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right), SizedTree::Empty)), SizedTree::Empty) by {
                rewrite(tree.model == sized_context_double_middle_subtree_before(g, p, node, above, pv, gv, far, m, mv, middle_left, middle_right, nv));
                unfold(sized_context_double_middle_subtree_before(g, p, node, above, pv, gv, far, m, mv, middle_left, middle_right, nv)); normalize();
            }
            let { metadata: g_size, left: parent_tree, right: g_right } = unfold(tree);
            let { metadata: p_size, left: p_left, right: focus } = unfold(parent_tree);
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
            let { metadata: m_size, left: m_left, right: m_right } = unfold(n_left);
            unfold(n_right);
            have node->rb_left == m by { assumption(); }
            have node->rb_right == 0 by { assumption(); }
            let n_left = fold(sized_at(node->rb_left), { model: SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right) }, { metadata: m_size, left: m_left, right: m_right });
            let n_right = fold(sized_at(node->rb_right), { model: SizedTree::Empty });
            let focus = fold(sized_at(node), { model: SizedTree::Node(node, p, Color::Red, nv, SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right), SizedTree::Empty) }, { metadata: n_size, left: n_left, right: n_right });
            have p->rb_right == node by { assumption(); }
            have p->rb_left != p by {
                assumption();
            }
            have p->rb_right != p by {
                assumption();
            }
            let parent_tree = fold(sized_at(p), { model: SizedTree::Node(p, g, Color::Red, pv, far, SizedTree::Node(node, p, Color::Red, nv, SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right), SizedTree::Empty)) }, { metadata: p_size, left: p_left, right: focus });
            let tree = fold(sized_at(g), { model: old(state.model) }, { metadata: g_size, left: parent_tree, right: g_right });
            let state = fold(sized_insert_context_double_middle_subtree_at(node, root), { phase: SizedInsertContextDoubleMiddleSubtreePhase::Before(g, p, above, pv, gv, far, m, mv, middle_left, middle_right, nv), model: old(state.model), context: old(state.context), whole_model: old(state.whole_model) }, { tree: tree, link: link });
            loop {
                owns state: sized_insert_context_double_middle_subtree_at(node, root);
                decreases 0;
                invariant node == old(node);
                invariant parent == p;
                invariant state.context == old(state.context);
                invariant p == old(g->rb_left);
                invariant m == old(g->rb_left->rb_right->rb_left);
                invariant state.phase == SizedInsertContextDoubleMiddleSubtreePhase::Before(g, p, above, pv, gv, far, m, mv, middle_left, middle_right, nv);
                invariant old(state.phase) == SizedInsertContextDoubleMiddleSubtreePhase::Before(g, p, above, pv, gv, far, m, mv, middle_left, middle_right, nv);
                invariant state.model == sized_context_double_middle_subtree_before(g, p, node, above, pv, gv, far, m, mv, middle_left, middle_right, nv);
                initialize by simp();
                preserve by {
                    let { tree: loop_tree, link: link } = unfold(state);
                    unfold(sized_context_double_middle_subtree_before(g, p, node, above, pv, gv, far, m, mv, middle_left, middle_right, nv));
                    have loop_tree.model == SizedTree::Node(g, above, Color::Black, gv, SizedTree::Node(p, g, Color::Red, pv, far, SizedTree::Node(node, p, Color::Red, nv, SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right), SizedTree::Empty)), SizedTree::Empty) by {
                        rewrite(loop_tree.model == sized_context_double_middle_subtree_before(g, p, node, above, pv, gv, far, m, mv, middle_left, middle_right, nv));
                        unfold(sized_context_double_middle_subtree_before(g, p, node, above, pv, gv, far, m, mv, middle_left, middle_right, nv)); normalize();
                    }
                    let { metadata: g_size, left: parent_tree, right: g_right } = unfold(loop_tree);
                    let { metadata: p_size, left: p_left, right: focus } = unfold(parent_tree);
                    unfold(g_right);
                    let { checked: p_left } = certify_size(p->rb_left, { tree: p_left });
                    let { metadata: n_size, left: n_left, right: n_right } = unfold(focus);
                    let { checked: n_left } = certify_size(node->rb_left, { tree: n_left });
                    unfold(sized_value(SizedTree::Node(node, p, Color::Red, nv, SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right), SizedTree::Empty)));
                    unfold(sized_value(SizedTree::Node(p, g, Color::Red, pv, far, SizedTree::Node(node, p, Color::Red, nv, SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right), SizedTree::Empty))));
                    unfold(sized_value(SizedTree::Empty));
                    have to_integer(nv) == 1 + to_integer(sized_value(SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right))) by {
                        arithmetic() using { to_integer(nv) == 1 + to_integer(sized_value(SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right))) + to_integer(sized_value(SizedTree::Empty)); to_integer(sized_value(SizedTree::Empty)) == 0; };
                    }
                    have to_integer(pv) == 1 + to_integer(sized_value(far)) + to_integer(nv) by {
                        assumption();
                    }
                    have to_integer(gv) == 1 + to_integer(pv) by {
                        arithmetic() using { to_integer(gv) == 1 + to_integer(sized_value(SizedTree::Node(p, g, Color::Red, pv, far, SizedTree::Node(node, p, Color::Red, nv, SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right), SizedTree::Empty)))) + to_integer(sized_value(SizedTree::Empty)); to_integer(sized_value(SizedTree::Node(p, g, Color::Red, pv, far, SizedTree::Node(node, p, Color::Red, nv, SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right), SizedTree::Empty)))) == to_integer(pv); to_integer(sized_value(SizedTree::Empty)) == 0; };
                    }
                    have to_integer(pv) == 2 + to_integer(sized_value(far)) + to_integer(sized_value(SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right))) by {
                        arithmetic() using {
                            to_integer(pv) == 1 + to_integer(sized_value(far)) + to_integer(nv);
                            to_integer(nv) == 1 + to_integer(sized_value(SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right)));
                        };
                    }
                    apply(sized_reparent_observations(SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right), p));
                    unfold(sized_reparent(SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right), p));
                    unfold(sized_value(SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right)));
                    unfold(sized_value(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)));
                    apply(sized_double_middle_bounds(pv, nv, far, SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right)));
                    apply(click::integer::int32_subtract_to_integer(pv, 1));
                    let focus = fold(sized_at(node), { model: SizedTree::Node(node, p, Color::Red, nv, SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right), SizedTree::Empty) }, { metadata: n_size, left: n_left, right: n_right });
                    mark before_inner_rotation;
                    let { metadata: n_size, left: n_left, right: n_right } = unfold(focus);
                    let focus = fold(sized_at(node), { model: SizedTree::Node(node, p, Color::Red, nv, SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right), SizedTree::Empty) }, { metadata: n_size, left: n_left, right: n_right });
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
                    step(); step(); step();
                    have tmp == node by { assumption(); }
                    step();
                    let { metadata: n_size, left: n_left, right: n_right } = unfold(focus);
                    unfold(n_right);
                    let { metadata: m_size, left: m_left, right: m_right } = unfold(n_left);
                    have node->rb_left == m by { assumption(); }
                    have m != 0 by { assumption(); }
                    let n_left = fold(sized_at(node->rb_left), { model: SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right) }, { metadata: m_size, left: m_left, right: m_right });
                    step(); mark before_inner_child_store;
                    have p->rb_left == at(before_inner_rotation, p->rb_left) by {
                        transport(at(before_inner_rotation, p->rb_left) == at(before_inner_rotation, p->rb_left),
                                  p->rb_left == at(before_inner_rotation, p->rb_left)) using { parent == p; };
                    }
                    have p->__rb_parent_color == at(before_inner_rotation, p->__rb_parent_color) by {
                        transport(at(before_inner_rotation, p->__rb_parent_color) == at(before_inner_rotation, p->__rb_parent_color),
                                  p->__rb_parent_color == at(before_inner_rotation, p->__rb_parent_color)) using { parent == p; };
                    }
                    have at(before_inner_rotation, g->rb_left) == parent by { assumption(); }
                    have at(before_inner_rotation, g->rb_left) == old(g->rb_left) by { assumption(); }
                    step(); mark after_inner_child_store;
                    have separate(memory(p->rb_left), memory(parent->rb_right)) by { assumption(); }
                    have p->rb_left == at(before_inner_child_store, p->rb_left) by {
                        transport(at(before_inner_child_store, p->rb_left) == at(before_inner_child_store, p->rb_left),
                                  p->rb_left == at(before_inner_child_store, p->rb_left)) using {
                            parent == p;
                            separate(memory(p->rb_left), memory(parent->rb_right));
                        };
                    }
                    have separate(memory(p->__rb_parent_color), memory(parent->rb_right)) by { assumption(); }
                    have separate(memory(g->rb_left), memory(parent->rb_right)) by { assumption(); }
                    have g->rb_left == at(before_inner_child_store, g->rb_left) by {
                        transport(at(before_inner_child_store, g->rb_left) == at(before_inner_child_store, g->rb_left),
                                  g->rb_left == at(before_inner_child_store, g->rb_left)) using {
                            parent == p;
                            gparent == g;
                            at(before_inner_rotation, g->rb_left) == parent;
                            separate(memory(g->rb_left), memory(parent->rb_right));
                        };
                    }
                    have p->__rb_parent_color == at(before_inner_child_store, p->__rb_parent_color) by {
                        transport(at(before_inner_child_store, p->__rb_parent_color) == at(before_inner_child_store, p->__rb_parent_color),
                                  p->__rb_parent_color == at(before_inner_child_store, p->__rb_parent_color)) using {
                            parent == p;
                            separate(memory(p->__rb_parent_color), memory(parent->rb_right));
                            at(before_inner_rotation, g->rb_left) == parent;
                            at(before_inner_rotation, g->rb_left) == old(g->rb_left);
                            gparent == g;
                            g->rb_left == at(before_inner_child_store, g->rb_left);
                            separate(memory(g->rb_left), memory(parent->rb_right));
                        };
                    }
}
}
}
}
}
