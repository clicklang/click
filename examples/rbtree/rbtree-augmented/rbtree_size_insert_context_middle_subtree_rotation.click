// Left-left insertion rotation moves an arbitrary nonempty black subtree.
// The focused node retains arbitrary child subtrees and the context is owned.
verifying "rb_insert_augmented.c" as insert;
verifying "rbtree_size_rotate.c";
verifying "rbtree_size_copy.c";
verifying "rbtree_size_compute.c";
import "rbtree_size_rotate_model.click";
import "rbtree_size_rotate_set_parents.click";
import "rbtree_size_reparent_call.click";
import "rbtree_size_insert_middle_subtree_model.click";

spec enum SizedInsertContextMiddleSubtreePhase {
    Before(struct rb_node*, struct rb_node*, struct rb_node*, struct rb_node*, int32, int32, int32, int32, SizedTree, SizedTree, SizedTree, SizedTree),
    After(struct rb_node*, struct rb_node*, struct rb_node*, struct rb_node*, int32, int32, int32, int32, SizedTree, SizedTree, SizedTree, SizedTree),
}

function sized_context_middle_subtree_pending(phase: SizedInsertContextMiddleSubtreePhase) -> int32 {
    match phase {
        SizedInsertContextMiddleSubtreePhase::Before(g, p, m, above, nv, pv, gv, mv, left, right, middle_left, middle_right) => 1,
        SizedInsertContextMiddleSubtreePhase::After(g, p, m, above, nv, pv, gv, mv, left, right, middle_left, middle_right) => 0,
    }
}

function sized_context_middle_subtree_finish(phase: SizedInsertContextMiddleSubtreePhase) -> SizedInsertContextMiddleSubtreePhase {
    match phase {
        SizedInsertContextMiddleSubtreePhase::Before(g, p, m, above, nv, pv, gv, mv, left, right, middle_left, middle_right) => SizedInsertContextMiddleSubtreePhase::After(g, p, m, above, nv, pv, gv, mv, left, right, middle_left, middle_right),
        SizedInsertContextMiddleSubtreePhase::After(g, p, m, above, nv, pv, gv, mv, left, right, middle_left, middle_right) => SizedInsertContextMiddleSubtreePhase::After(g, p, m, above, nv, pv, gv, mv, left, right, middle_left, middle_right),
    }
}

function sized_context_middle_subtree_expected(phase: SizedInsertContextMiddleSubtreePhase, node: struct rb_node*) -> RbTree {
    match phase {
        SizedInsertContextMiddleSubtreePhase::Before(g, p, m, above, nv, pv, gv, mv, left, right, middle_left, middle_right) => sized_context_middle_subtree_after(g, p, m, node, above, left, right, middle_left, middle_right),
        SizedInsertContextMiddleSubtreePhase::After(g, p, m, above, nv, pv, gv, mv, left, right, middle_left, middle_right) => sized_context_middle_subtree_after(g, p, m, node, above, left, right, middle_left, middle_right),
    }
}


resource sized_insert_context_middle_subtree_at(node: struct rb_node*, root: struct rb_root*) {
    field phase: SizedInsertContextMiddleSubtreePhase;
    field model: SizedTree;
    field context: SizedContext;
    field whole_model: SizedTree;
    match phase {
        SizedInsertContextMiddleSubtreePhase::Before(g, p, m, above, nv, pv, gv, mv, left, right, middle_left, middle_right) => {
            owns link: sized_link_at(g, root, gv);
            owns tree: sized_at(g);
            fact link.model == context;
            fact above == sized_context_parent(context, 0);
            fact tree.model == model;
            fact model == sized_context_middle_subtree_before(g, p, m, node, above, nv, pv, gv, mv, left, right, middle_left, middle_right);
        },
        SizedInsertContextMiddleSubtreePhase::After(g, p, m, above, nv, pv, gv, mv, left, right, middle_left, middle_right) => {
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
    owns state: sized_insert_context_middle_subtree_at(node, root);
    requires sized_context_middle_subtree_pending(state.phase) == 1;
    ensures state.context == old(state.context);
    ensures state.whole_model == sized_plug(old(state.context), state.model);
    ensures state.phase == sized_context_middle_subtree_finish(old(state.phase));
    ensures sized_shape(state.model) == sized_context_middle_subtree_expected(old(state.phase), node);
} by {
    match state.phase {
        SizedInsertContextMiddleSubtreePhase::After(g, p, m, above, nv, pv, gv, mv, left, right, middle_left, middle_right) => {
            have sized_context_middle_subtree_pending(state.phase) != 1 by {
                rewrite(state.phase == SizedInsertContextMiddleSubtreePhase::After(g, p, m, above, nv, pv, gv, mv, left, right, middle_left, middle_right));
                unfold(sized_context_middle_subtree_pending(SizedInsertContextMiddleSubtreePhase::After(g, p, m, above, nv, pv, gv, mv, left, right, middle_left, middle_right))); normalize();
            }
            contradiction(sized_context_middle_subtree_pending(state.phase) == 1);
        },
        SizedInsertContextMiddleSubtreePhase::Before(g, p, m, above, nv, pv, gv, mv, left, right, middle_left, middle_right) => {
            let { tree: tree, link: link } = unfold(state);
            unfold(sized_context_middle_subtree_before(g, p, m, node, above, nv, pv, gv, mv, left, right, middle_left, middle_right));
            have tree.model == SizedTree::Node(g, above, Color::Black, gv,
                SizedTree::Node(p, g, Color::Red, pv,
                    SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)), SizedTree::Empty) by {
                rewrite(tree.model == sized_context_middle_subtree_before(g, p, m, node, above, nv, pv, gv, mv, left, right, middle_left, middle_right));
                unfold(sized_context_middle_subtree_before(g, p, m, node, above, nv, pv, gv, mv, left, right, middle_left, middle_right)); normalize();
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
            let focus = fold(sized_at(node), { model: SizedTree::Node(node, p, Color::Red, nv, left, right) }, { metadata: n_size, left: n_left, right: n_right });
            have p->rb_left == node by { assumption(); }
            have p->rb_left != p by {
                assumption();
            }
            have p->rb_right != p by {
                assumption();
            }
            let parent_tree = fold(sized_at(p), { model: SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)) }, { metadata: p_size, left: focus, right: p_right });
            let tree = fold(sized_at(g), { model: old(state.model) }, { metadata: g_size, left: parent_tree, right: g_right });
            let state = fold(sized_insert_context_middle_subtree_at(node, root), { phase: SizedInsertContextMiddleSubtreePhase::Before(g, p, m, above, nv, pv, gv, mv, left, right, middle_left, middle_right), model: old(state.model), context: old(state.context), whole_model: old(state.whole_model) }, { tree: tree, link: link });
            loop {
                owns state: sized_insert_context_middle_subtree_at(node, root);
                decreases 0;
                invariant node == old(node);
                invariant parent == p;
                invariant state.context == old(state.context);
                invariant p == old(g->rb_left);
                invariant state.phase == SizedInsertContextMiddleSubtreePhase::Before(g, p, m, above, nv, pv, gv, mv, left, right, middle_left, middle_right);
                invariant old(state.phase) == SizedInsertContextMiddleSubtreePhase::Before(g, p, m, above, nv, pv, gv, mv, left, right, middle_left, middle_right);
                invariant state.model == sized_context_middle_subtree_before(g, p, m, node, above, nv, pv, gv, mv, left, right, middle_left, middle_right);
                initialize by simp();
                preserve by {
                    let { tree: loop_tree, link: link } = unfold(state);
                    unfold(sized_context_middle_subtree_before(g, p, m, node, above, nv, pv, gv, mv, left, right, middle_left, middle_right));
                    have loop_tree.model == SizedTree::Node(g, above, Color::Black, gv,
                        SizedTree::Node(p, g, Color::Red, pv,
                            SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)), SizedTree::Empty) by {
                        rewrite(loop_tree.model == sized_context_middle_subtree_before(g, p, m, node, above, nv, pv, gv, mv, left, right, middle_left, middle_right));
                        unfold(sized_context_middle_subtree_before(g, p, m, node, above, nv, pv, gv, mv, left, right, middle_left, middle_right)); normalize();
                    }
                    let { metadata: g_size, left: parent_tree, right: g_right } = unfold(loop_tree);
                    let { metadata: p_size, left: focus, right: p_right } = unfold(parent_tree);
                    unfold(g_right);
                    let { metadata: m_size, left: m_left, right: m_right } = unfold(p_right);
                    have p->rb_right == m by { assumption(); }
                    let { metadata: n_size, left: n_left, right: n_right } = unfold(focus);
                    have separate(memory(node->__rb_parent_color), memory(m->__rb_parent_color)) by { assumption(); }
                    have m != node by { assumption(); }
                    have separate(memory(m->__rb_parent_color), memory(g->__rb_parent_color)) by { assumption(); }
                    have m != g by { assumption(); }
                    let p_right = fold(sized_at(p->rb_right), { model: SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right) }, { metadata: m_size, left: m_left, right: m_right });
                    let focus = fold(sized_at(node), { model: SizedTree::Node(node, p, Color::Red, nv, left, right) }, { metadata: n_size, left: n_left, right: n_right });
                    let { checked: focus } = certify_size(node, { tree: focus });
                    let { checked: p_right } = certify_size(p->rb_right, { tree: p_right });
                    unfold(sized_value(SizedTree::Node(node, p, Color::Red, nv, left, right)));
                    unfold(sized_value(SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))));
                    unfold(sized_value(SizedTree::Empty));
                    unfold(sized_value(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)));
                    have to_integer(sized_value(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))) == to_integer(mv) by {
                        rewrite(sized_value(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)) == mv); normalize();
                    }
                    have to_integer(gv) == 2 + to_integer(nv) + to_integer(mv) by {
                        arithmetic() using {
                            to_integer(gv) == 1 + to_integer(pv) + to_integer(sized_value(SizedTree::Empty));
                            to_integer(pv) == 1 + to_integer(nv) + to_integer(sized_value(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)));
                            to_integer(sized_value(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))) == to_integer(mv);
                            to_integer(sized_value(SizedTree::Empty)) == 0;
                        };
                    }
                    have rb_subtree_size(sized_shape(SizedTree::Node(node, p, Color::Red, nv, left, right))) == to_integer(nv) by assumption();
                    have rb_subtree_size(sized_shape(left)) + rb_subtree_size(sized_shape(right)) + 1 == to_integer(nv) by {
                        rewrite(to_integer(nv) == rb_subtree_size(sized_shape(SizedTree::Node(node, p, Color::Red, nv, left, right))));
                        unfold(sized_shape(SizedTree::Node(node, p, Color::Red, nv, left, right)));
                        unfold(rb_subtree_size(RbTree::Node(node, p, Color::Red, sized_shape(left), sized_shape(right))));
                        normalize();
                    }
                    have rb_subtree_size(sized_shape(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))) == to_integer(mv) by { assumption(); }
                    have rb_subtree_size(sized_shape(middle_left)) + rb_subtree_size(sized_shape(middle_right)) + 1 == to_integer(mv) by {
                        rewrite(to_integer(mv) == rb_subtree_size(sized_shape(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))));
                        unfold(sized_shape(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)));
                        unfold(rb_subtree_size(RbTree::Node(m, p, Color::Black, sized_shape(middle_left), sized_shape(middle_right)))); normalize();
                    }
                    apply(rb_subtree_size_nonnegative(sized_shape(SizedTree::Node(node, p, Color::Red, nv, left, right))));
                    apply(rb_subtree_size_nonnegative(sized_shape(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))));
                    have 0 <= to_integer(nv) by { arithmetic() using {
                        rb_subtree_size(sized_shape(SizedTree::Node(node, p, Color::Red, nv, left, right))) == to_integer(nv);
                        rb_subtree_size(sized_shape(SizedTree::Node(node, p, Color::Red, nv, left, right))) >= 0;
                    }; }
                    have 0 <= to_integer(mv) by { arithmetic() using {
                        rb_subtree_size(sized_shape(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))) == to_integer(mv);
                        rb_subtree_size(sized_shape(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))) >= 0;
                    }; }
                    apply(click::integer::int32_to_integer_bounds(gv));
                    have 1 + to_integer(mv) + to_integer(0) <= 2147483647 by { arithmetic() using {
                        to_integer(gv) == 2 + to_integer(nv) + to_integer(mv);
                        to_integer(nv) >= 0;
                        to_integer(gv) <= 2147483647;
                    }; }
                    apply(size_children_fit(mv, 0));
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
                    have parent->rb_left == node by { assumption(); }
                    mark before_link_writes;
                    have at(before_link_writes, parent->rb_left == node) by { assumption(); }
                    have at(before_link_writes, g->rb_left) == parent by { assumption(); }
                    step(); step(); step();
                    have tmp == m by { assumption(); }
                    have tmp != 0 by { assumption(); }
                    have tmp != node by { assumption(); }
                    have node != 0 by { assumption(); }
                    step(); step(); step();
                    mark after_left_write;
                    have at(after_left_write, g->rb_left == m) by { assumption(); }
                    have separate(memory(g->rb_left), memory(parent->rb_right)) by { assumption(); }
                    step(); step();
                    let { after: p_right } = step(insert::rb_set_parent_color(tmp, gparent, 1), { tree: p_right });
                    unfold(sized_reparent(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), g));
                    unfold(sized_recolor(SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), Color::Black));
                    have p_right.model == SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right) by { assumption(); }
                    have gparent->__rb_parent_color == address(above) + 1 by { simp(); }
                    unfold(g_size);
                    have sized_context_parent_word(link.model, g->__rb_parent_color) == 1 by {
                        apply(sized_context_parent_word_black(link.model, above, g->__rb_parent_color));
                    }
                    have g->rb_left == m by {
                        transport(at(after_left_write, g->rb_left == m), g->rb_left == m) using {
                            at(after_left_write, g->rb_left == m);
                            separate(memory(g->rb_left), memory(parent->rb_right));
                            at(before_link_writes, g->rb_left) == parent;
                        };
                    }
                    transport(at(before_link_writes, parent->rb_left == node), parent->rb_left == node);
                    have parent->rb_right == gparent by { simp(); }
                    mark before_parent_update;
                    have at(before_parent_update, g->rb_left == m) by { assumption(); }
                    have at(before_parent_update, parent->rb_left == node) by { assumption(); }
                    have at(before_parent_update, parent->rb_right == gparent) by { assumption(); }
                    let { after: link } = step(insert::__rb_rotate_set_parents(gparent, parent, root, 0), { c: link });
                    have parent->__rb_parent_color == at(before_parent_update, gparent->__rb_parent_color) by { assumption(); }
                    have p->__rb_parent_color == at(before_parent_update, g->__rb_parent_color) by { assumption(); }
                    have p->__rb_parent_color == address(above) + (p->__rb_parent_color & 1) by {
                        rewrite(p->__rb_parent_color == at(before_parent_update, g->__rb_parent_color));
                        assumption();
                    }
                    have (p->__rb_parent_color & 1) == color_bit(Color::Black) by {
                        rewrite(p->__rb_parent_color == at(before_parent_update, g->__rb_parent_color));
                        assumption();
                    }
                    let g_size = fold(size_metadata(g), { value: gv });
                    transport(at(before_parent_update, g->rb_left == m), g->rb_left == m);
                    have g->rb_right == 0 by { simp(); }
                    let g_right = fold(sized_at(g->rb_right), { model: SizedTree::Empty });
                    unfold(sized_parent_is(SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), g));
                    let demoted = fold(sized_recompute_at(g), {
                        model: SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Empty)
                    }, { metadata: g_size, left: p_right, right: g_right });
                    transport(at(before_parent_update, parent->rb_left == node), parent->rb_left == node) using {
                        at(before_parent_update, parent->rb_left == node);
                        parent == p;
                        at(before_link_writes, g->rb_left) == parent;
                    };
                    transport(at(before_parent_update, parent->rb_right == gparent), parent->rb_right == gparent) using {
                        at(before_parent_update, parent->rb_right == gparent);
                        parent == p;
                        at(before_link_writes, g->rb_left) == parent;
                    };
                    have p->rb_right == g by { assumption(); }
                    have parent == p by { assumption(); }
                    have sized_parent_is(SizedTree::Node(node, p, Color::Red, nv, left, right), p) == 1 by {
                        unfold(sized_parent_is(SizedTree::Node(node, p, Color::Red, nv, left, right), p)); normalize();
                    }
                    have sized_parent_is(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Empty), p) == 1 by {
                        unfold(sized_parent_is(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Empty), p)); normalize();
                    }
                    have to_integer(sized_value(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Empty))) == 2 + to_integer(sized_value(sized_left(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Empty)))) + to_integer(sized_value(sized_right(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Empty)))) + to_integer(sized_value(SizedTree::Node(node, p, Color::Red, nv, left, right))) by {
                        unfold(sized_value(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Empty)));
                        unfold(sized_left(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Empty)));
                        unfold(sized_right(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Empty)));
                        unfold(sized_value(SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right)));
                        unfold(sized_value(SizedTree::Empty));
                        unfold(sized_value(SizedTree::Node(node, p, Color::Red, nv, left, right)));
                        arithmetic() using { to_integer(gv) == 2 + to_integer(nv) + to_integer(mv); };
                    }
                    let rotated = fold(sized_rotation_right_at(g, p), {
                        model: SizedTree::Node(p, above, Color::Black, pv,
                            SizedTree::Node(node, p, Color::Red, nv, left, right),
                            SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Empty))
                    }, { metadata: p_size, other: focus, demoted: demoted });
                    unfold(sized_right(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Empty))));
                    unfold(sized_left(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Empty)));
                    unfold(sized_right(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Empty)));
                    unfold(sized_value(SizedTree::Empty));
                    have 0 <= sized_value(sized_left(sized_right(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Empty))))) by {
                        rewrite(sized_right(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Empty))) == SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Empty));
                        rewrite(sized_left(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Empty)) == SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right));
                        unfold(sized_value(SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right))); simp();
                    }
                    have 0 <= sized_value(sized_right(sized_right(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Empty))))) by {
                        rewrite(sized_right(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Empty))) == SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Empty));
                        rewrite(sized_right(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Empty)) == SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty) == 0); normalize();
                    }
                    have sized_value(sized_right(sized_right(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Empty))))) <= 2147483646 by {
                        rewrite(sized_right(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Empty))) == SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Empty));
                        rewrite(sized_right(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Empty)) == SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty) == 0); normalize();
                    }
                    have sized_value(sized_left(sized_right(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Empty))))) <= 2147483646 - sized_value(sized_right(sized_right(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Empty))))) by {
                        rewrite(sized_right(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Empty))) == SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Empty));
                        rewrite(sized_left(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Empty)) == SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right));
                        rewrite(sized_right(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Empty)) == SizedTree::Empty);
                        unfold(sized_value(SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right)));
                        rewrite(sized_value(SizedTree::Empty) == 0); simp();
                    }
                    let { checked: checked } = step(RotateTreeRight, { tree: rotated });
                    have sized_shape(checked.model) == sized_context_middle_subtree_after(g, p, m, node, above, left, right, middle_left, middle_right) by {
                        rewrite(sized_shape(checked.model) == sized_shape(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Empty))));
                        unfold(sized_shape(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Empty))));
                        unfold(sized_shape(SizedTree::Node(node, p, Color::Red, nv, left, right)));
                        unfold(sized_shape(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Empty)));
                        unfold(sized_shape(SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right)));
                        unfold(sized_shape(SizedTree::Empty));
                        unfold(sized_context_middle_subtree_after(g, p, m, node, above, left, right, middle_left, middle_right)); normalize();
                    }
                    have rb_subtree_size(sized_context_middle_subtree_after(g, p, m, node, above, left, right, middle_left, middle_right)) == to_integer(gv) by {
                        unfold(sized_context_middle_subtree_after(g, p, m, node, above, left, right, middle_left, middle_right));
                        unfold(rb_subtree_size(RbTree::Node(p, above, Color::Black, RbTree::Node(node, p, Color::Red, sized_shape(left), sized_shape(right)), RbTree::Node(g, p, Color::Red, RbTree::Node(m, g, Color::Black, sized_shape(middle_left), sized_shape(middle_right)), RbTree::Empty))));
                        unfold(rb_subtree_size(RbTree::Node(node, p, Color::Red, sized_shape(left), sized_shape(right))));
                        unfold(rb_subtree_size(RbTree::Node(g, p, Color::Red, RbTree::Node(m, g, Color::Black, sized_shape(middle_left), sized_shape(middle_right)), RbTree::Empty)));
                        unfold(rb_subtree_size(RbTree::Node(m, g, Color::Black, sized_shape(middle_left), sized_shape(middle_right))));
                        unfold(rb_subtree_size(RbTree::Empty));
                        unfold(sized_shape(SizedTree::Node(node, p, Color::Red, nv, left, right)));
                        arithmetic() using {
                            to_integer(gv) == 2 + to_integer(nv) + to_integer(mv);
                            rb_subtree_size(sized_shape(left)) + rb_subtree_size(sized_shape(right)) + 1 == to_integer(nv);
                            rb_subtree_size(sized_shape(middle_left)) + rb_subtree_size(sized_shape(middle_right)) + 1 == to_integer(mv);
                        };
                    }
                    have to_integer(sized_value(checked.model)) == to_integer(gv) by {
                        rewrite(to_integer(sized_value(checked.model)) == rb_subtree_size(sized_shape(checked.model)));
                        rewrite(sized_shape(checked.model) == sized_context_middle_subtree_after(g, p, m, node, above, left, right, middle_left, middle_right));
                        assumption();
                    }
                    have sized_value(checked.model) == gv by {
                        apply(click::integer::int32_to_integer_equal_implies_equal(sized_value(checked.model), gv));
                    }
                    apply(sized_parent_is_shape(checked.model, above));
                    have rb_parent_is(sized_shape(checked.model), above) == 1 by {
                        rewrite(sized_shape(checked.model) == sized_context_middle_subtree_after(g, p, m, node, above, left, right, middle_left, middle_right));
                        unfold(sized_context_middle_subtree_after(g, p, m, node, above, left, right, middle_left, middle_right));
                        unfold(rb_parent_is(RbTree::Node(p, above, Color::Black, RbTree::Node(node, p, Color::Red, sized_shape(left), sized_shape(right)), RbTree::Node(g, p, Color::Red, RbTree::Node(m, g, Color::Black, sized_shape(middle_left), sized_shape(middle_right)), RbTree::Empty)), above)); normalize();
                    }
                    have sized_parent_is(checked.model, above) == 1 by {
                        rewrite(sized_parent_is(checked.model, above) == rb_parent_is(sized_shape(checked.model), above));
                        assumption();
                    }
                    let { frames: path } = unfold(link);
                    have path.model == old(state.context) by { assumption(); }
                    have sized_parent_is(checked.model, sized_context_parent(path.model, 0)) == 1 by {
                        rewrite(path.model == old(state.context));
                        rewrite(sized_context_parent(old(state.context), 0) == above);
                        assumption();
                    }
                    mark before_restore;
                    let { whole: whole } = restore_sized_context(p, root->rb_node, 0, gv, { path: path, sub: checked });
                    have whole.model == sized_plug(old(state.context), at(before_restore, checked.model)) by { assumption(); }
                    let state = fold(sized_insert_context_middle_subtree_at(node, root), {
                        phase: SizedInsertContextMiddleSubtreePhase::After(g, p, m, above, nv, pv, gv, mv, left, right, middle_left, middle_right), model: at(before_restore, checked.model), context: old(state.context), whole_model: whole.model
                    }, { whole: whole });
                    have state.context == old(state.context) by { assumption(); }
                    have state.whole_model == sized_plug(old(state.context), state.model) by { assumption(); }
                    have state.phase == sized_context_middle_subtree_finish(old(state.phase)) by {
                        unfold(sized_context_middle_subtree_finish(SizedInsertContextMiddleSubtreePhase::Before(g, p, m, above, nv, pv, gv, mv, left, right, middle_left, middle_right))); simp();
                    }
                    have sized_shape(state.model) == sized_context_middle_subtree_expected(old(state.phase), node) by {
                        rewrite(old(state.phase) == SizedInsertContextMiddleSubtreePhase::Before(g, p, m, above, nv, pv, gv, mv, left, right, middle_left, middle_right));
                        unfold(sized_context_middle_subtree_expected(SizedInsertContextMiddleSubtreePhase::Before(g, p, m, above, nv, pv, gv, mv, left, right, middle_left, middle_right), node)); simp();
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
    requires RotateTreeRight(augment_rotate);
    owns state: sized_insert_context_middle_subtree_at(node, root);
    requires sized_context_middle_subtree_pending(state.phase) == 1;
    ensures state.context == old(state.context);
    ensures state.whole_model == sized_plug(old(state.context), state.model);
    ensures state.phase == sized_context_middle_subtree_finish(old(state.phase));
    ensures sized_shape(state.model) == sized_context_middle_subtree_expected(old(state.phase), node);
} by {
    step(insert::__rb_insert(node, root, augment_rotate), { state: state });
    execute(); simp();
}

void insert::rb_insert_augmented(struct rb_node* node, struct rb_root* root,
                         const struct rb_augment_callbacks* augment) {
    views augment->rotate;
    requires RotateTreeRight(augment->rotate);
    owns state: sized_insert_context_middle_subtree_at(node, root);
    requires sized_context_middle_subtree_pending(state.phase) == 1;
    ensures state.context == old(state.context);
    ensures state.whole_model == sized_plug(old(state.context), state.model);
    ensures state.phase == sized_context_middle_subtree_finish(old(state.phase));
    ensures sized_shape(state.model) == sized_context_middle_subtree_expected(old(state.phase), node);
} by {
    step(insert::__rb_insert_augmented(node, root, augment->rotate), { state: state });
    execute(); simp();
}
