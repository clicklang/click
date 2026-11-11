// Left-left insertion rotation moves a nonempty black middle leaf.
// The focused node retains arbitrary child subtrees and the context is owned.
verifying "rb_insert_augmented.c" as insert;
verifying "rbtree_size_rotate.c";
verifying "rbtree_size_copy.c";
verifying "rbtree_size_compute.c";
import "rbtree_size_rotate_model.click";
import "rbtree_size_rotate_set_parents.click";
import "rbtree_size_reparent_call.click";
import "rbtree_size_insert_middle_model.click";

spec enum SizedInsertContextMiddlePhase {
    Before(struct rb_node*, struct rb_node*, struct rb_node*, struct rb_node*, int32, int32, int32, SizedTree, SizedTree),
    After(struct rb_node*, struct rb_node*, struct rb_node*, struct rb_node*, int32, int32, int32, SizedTree, SizedTree),
}

function sized_context_middle_pending(phase: SizedInsertContextMiddlePhase) -> int32 {
    match phase {
        SizedInsertContextMiddlePhase::Before(g, p, m, above, nv, pv, gv, left, right) => 1,
        SizedInsertContextMiddlePhase::After(g, p, m, above, nv, pv, gv, left, right) => 0,
    }
}

function sized_context_middle_finish(phase: SizedInsertContextMiddlePhase) -> SizedInsertContextMiddlePhase {
    match phase {
        SizedInsertContextMiddlePhase::Before(g, p, m, above, nv, pv, gv, left, right) => SizedInsertContextMiddlePhase::After(g, p, m, above, nv, pv, gv, left, right),
        SizedInsertContextMiddlePhase::After(g, p, m, above, nv, pv, gv, left, right) => SizedInsertContextMiddlePhase::After(g, p, m, above, nv, pv, gv, left, right),
    }
}

function sized_context_middle_expected(phase: SizedInsertContextMiddlePhase, node: struct rb_node*) -> RbTree {
    match phase {
        SizedInsertContextMiddlePhase::Before(g, p, m, above, nv, pv, gv, left, right) => sized_context_middle_after(g, p, m, node, above, left, right),
        SizedInsertContextMiddlePhase::After(g, p, m, above, nv, pv, gv, left, right) => sized_context_middle_after(g, p, m, node, above, left, right),
    }
}


resource sized_insert_context_middle_at(node: struct rb_node*, root: struct rb_root*) {
    field phase: SizedInsertContextMiddlePhase;
    field model: SizedTree;
    field context: SizedContext;
    field whole_model: SizedTree;
    match phase {
        SizedInsertContextMiddlePhase::Before(g, p, m, above, nv, pv, gv, left, right) => {
            owns link: sized_link_at(g, root, gv);
            owns tree: sized_at(g);
            fact link.model == context;
            fact above == sized_context_parent(context, 0);
            fact tree.model == model;
            fact model == sized_context_middle_before(g, p, m, node, above, nv, pv, gv, left, right);
        },
        SizedInsertContextMiddlePhase::After(g, p, m, above, nv, pv, gv, left, right) => {
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
    owns state: sized_insert_context_middle_at(node, root);
    requires sized_context_middle_pending(state.phase) == 1;
    ensures state.context == old(state.context);
    ensures state.whole_model == sized_plug(old(state.context), state.model);
    ensures state.phase == sized_context_middle_finish(old(state.phase));
    ensures sized_shape(state.model) == sized_context_middle_expected(old(state.phase), node);
} by {
    match state.phase {
        SizedInsertContextMiddlePhase::After(g, p, m, above, nv, pv, gv, left, right) => {
            have sized_context_middle_pending(state.phase) != 1 by {
                rewrite(state.phase == SizedInsertContextMiddlePhase::After(g, p, m, above, nv, pv, gv, left, right));
                unfold(sized_context_middle_pending(SizedInsertContextMiddlePhase::After(g, p, m, above, nv, pv, gv, left, right))); normalize();
            }
            contradiction(sized_context_middle_pending(state.phase) == 1);
        },
        SizedInsertContextMiddlePhase::Before(g, p, m, above, nv, pv, gv, left, right) => {
            let { tree: tree, link: link } = unfold(state);
            unfold(sized_context_middle_before(g, p, m, node, above, nv, pv, gv, left, right));
            have tree.model == SizedTree::Node(g, above, Color::Black, gv,
                SizedTree::Node(p, g, Color::Red, pv,
                    SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(m, p, Color::Black, 1, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty) by {
                rewrite(tree.model == sized_context_middle_before(g, p, m, node, above, nv, pv, gv, left, right));
                unfold(sized_context_middle_before(g, p, m, node, above, nv, pv, gv, left, right)); normalize();
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
            have p->rb_left == node by { assumption(); }
            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == p by { assumption(); }
            have p->rb_right != p by { assumption(); }
            have ((p->__rb_parent_color & ~3) as (struct rb_node *)) == g by { assumption(); }
            have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above by { assumption(); }
            mark m0; step();
            have *((&node->__rb_parent_color) as (int32 **)) == at(m0, *((&node->__rb_parent_color) as (int32 **))) by solve();
            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == p by { assumption(); }
            have *((&p->rb_left) as (int32 **)) == at(m0, *((&p->rb_left) as (int32 **))) by solve();
            have p->rb_left == node by { assumption(); }
            have *((&p->rb_right) as (int32 **)) == at(m0, *((&p->rb_right) as (int32 **))) by solve();
            have p->rb_right != p by { assumption(); }
            have *((&p->__rb_parent_color) as (int32 **)) == at(m0, *((&p->__rb_parent_color) as (int32 **))) by solve();
            have ((p->__rb_parent_color & ~3) as (struct rb_node *)) == g by { assumption(); }
            have *((&g->__rb_parent_color) as (int32 **)) == at(m0, *((&g->__rb_parent_color) as (int32 **))) by solve();
            have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above by { assumption(); }
            mark m1; step();
            have *((&node->__rb_parent_color) as (int32 **)) == at(m1, *((&node->__rb_parent_color) as (int32 **))) by solve();
            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == p by { assumption(); }
            have *((&p->rb_left) as (int32 **)) == at(m1, *((&p->rb_left) as (int32 **))) by solve();
            have p->rb_left == node by { assumption(); }
            have *((&p->rb_right) as (int32 **)) == at(m1, *((&p->rb_right) as (int32 **))) by solve();
            have p->rb_right != p by { assumption(); }
            have *((&p->__rb_parent_color) as (int32 **)) == at(m1, *((&p->__rb_parent_color) as (int32 **))) by solve();
            have ((p->__rb_parent_color & ~3) as (struct rb_node *)) == g by { assumption(); }
            have *((&g->__rb_parent_color) as (int32 **)) == at(m1, *((&g->__rb_parent_color) as (int32 **))) by solve();
            have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above by { assumption(); }
            mark m2; step();
            have *((&node->__rb_parent_color) as (int32 **)) == at(m2, *((&node->__rb_parent_color) as (int32 **))) by solve();
            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == p by { assumption(); }
            have *((&p->rb_left) as (int32 **)) == at(m2, *((&p->rb_left) as (int32 **))) by solve();
            have p->rb_left == node by { assumption(); }
            have *((&p->rb_right) as (int32 **)) == at(m2, *((&p->rb_right) as (int32 **))) by solve();
            have p->rb_right != p by { assumption(); }
            have *((&p->__rb_parent_color) as (int32 **)) == at(m2, *((&p->__rb_parent_color) as (int32 **))) by solve();
            have ((p->__rb_parent_color & ~3) as (struct rb_node *)) == g by { assumption(); }
            have *((&g->__rb_parent_color) as (int32 **)) == at(m2, *((&g->__rb_parent_color) as (int32 **))) by solve();
            have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above by { assumption(); }
            mark m3; step();
            have *((&node->__rb_parent_color) as (int32 **)) == at(m3, *((&node->__rb_parent_color) as (int32 **))) by solve();
            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == p by { assumption(); }
            have *((&p->rb_left) as (int32 **)) == at(m3, *((&p->rb_left) as (int32 **))) by solve();
            have p->rb_left == node by { assumption(); }
            have *((&p->rb_right) as (int32 **)) == at(m3, *((&p->rb_right) as (int32 **))) by solve();
            have p->rb_right != p by { assumption(); }
            have *((&p->__rb_parent_color) as (int32 **)) == at(m3, *((&p->__rb_parent_color) as (int32 **))) by solve();
            have ((p->__rb_parent_color & ~3) as (struct rb_node *)) == g by { assumption(); }
            have *((&g->__rb_parent_color) as (int32 **)) == at(m3, *((&g->__rb_parent_color) as (int32 **))) by solve();
            have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above by { assumption(); }
            let focus = fold(sized_at(node), { model: SizedTree::Node(node, p, Color::Red, nv, left, right) }, { metadata: n_size, left: n_left, right: n_right });
            have p->rb_left == node by { assumption(); }
            have p->rb_left != p by {
                assumption();
            }
            have p->rb_right != p by {
                assumption();
            }
            let parent_tree = fold(sized_at(p), { model: SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(m, p, Color::Black, 1, SizedTree::Empty, SizedTree::Empty)) }, { metadata: p_size, left: focus, right: p_right });
            let tree = fold(sized_at(g), { model: old(state.model) }, { metadata: g_size, left: parent_tree, right: g_right });
            let state = fold(sized_insert_context_middle_at(node, root), { phase: SizedInsertContextMiddlePhase::Before(g, p, m, above, nv, pv, gv, left, right), model: old(state.model), context: old(state.context), whole_model: old(state.whole_model) }, { tree: tree, link: link });
            loop {
                owns state: sized_insert_context_middle_at(node, root);
                decreases 0;
                invariant node == old(node);
                invariant parent == p;
                invariant state.context == old(state.context);
                invariant p == old(g->rb_left);
                invariant state.phase == SizedInsertContextMiddlePhase::Before(g, p, m, above, nv, pv, gv, left, right);
                invariant old(state.phase) == SizedInsertContextMiddlePhase::Before(g, p, m, above, nv, pv, gv, left, right);
                invariant state.model == sized_context_middle_before(g, p, m, node, above, nv, pv, gv, left, right);
                initialize by solve();
                preserve by {
                    let { tree: loop_tree, link: link } = unfold(state);
                    unfold(sized_context_middle_before(g, p, m, node, above, nv, pv, gv, left, right));
                    have loop_tree.model == SizedTree::Node(g, above, Color::Black, gv,
                        SizedTree::Node(p, g, Color::Red, pv,
                            SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(m, p, Color::Black, 1, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty) by {
                        rewrite(loop_tree.model == sized_context_middle_before(g, p, m, node, above, nv, pv, gv, left, right));
                        unfold(sized_context_middle_before(g, p, m, node, above, nv, pv, gv, left, right)); normalize();
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
                    let p_right = fold(sized_at(p->rb_right), { model: SizedTree::Node(m, p, Color::Black, 1, SizedTree::Empty, SizedTree::Empty) }, { metadata: m_size, left: m_left, right: m_right });
                    let focus = fold(sized_at(node), { model: SizedTree::Node(node, p, Color::Red, nv, left, right) }, { metadata: n_size, left: n_left, right: n_right });
                    let { checked: focus } = certify_size(node, { tree: focus });
                    unfold(sized_value(SizedTree::Node(node, p, Color::Red, nv, left, right)));
                    unfold(sized_value(SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(m, p, Color::Black, 1, SizedTree::Empty, SizedTree::Empty))));
                    unfold(sized_value(SizedTree::Empty));
                    unfold(sized_value(SizedTree::Node(m, p, Color::Black, 1, SizedTree::Empty, SizedTree::Empty)));
                    have to_integer(sized_value(SizedTree::Node(m, p, Color::Black, 1, SizedTree::Empty, SizedTree::Empty))) == 1 by {
                        rewrite(sized_value(SizedTree::Node(m, p, Color::Black, 1, SizedTree::Empty, SizedTree::Empty)) == 1); normalize();
                    }
                    have to_integer(gv) == 3 + to_integer(nv) by {
                        solve() using {
                            to_integer(gv) == 1 + to_integer(pv) + to_integer(sized_value(SizedTree::Empty));
                            to_integer(pv) == 1 + to_integer(nv) + to_integer(sized_value(SizedTree::Node(m, p, Color::Black, 1, SizedTree::Empty, SizedTree::Empty)));
                            to_integer(sized_value(SizedTree::Node(m, p, Color::Black, 1, SizedTree::Empty, SizedTree::Empty))) == 1;
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
                    have p->rb_left == node by { assumption(); }
                    have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above by { assumption(); }
                    have g->rb_left == p by { assumption(); }
                    have g->rb_right == 0 by { assumption(); }
                    mark l0; step();
                    have *((&g->rb_right) as (int32 **)) == at(l0, *((&g->rb_right) as (int32 **))) by solve();
                    have g->rb_right == 0 by { assumption(); }
                    have *((&p->rb_left) as (int32 **)) == at(l0, *((&p->rb_left) as (int32 **))) by solve();
                    have p->rb_left == node by { assumption(); }
                    have *((&g->__rb_parent_color) as (int32 **)) == at(l0, *((&g->__rb_parent_color) as (int32 **))) by solve();
                    have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above by { assumption(); }
                    have *((&g->rb_left) as (int32 **)) == at(l0, *((&g->rb_left) as (int32 **))) by solve();
                    have g->rb_left == p by { assumption(); }
                    mark l1; step();
                    have *((&g->rb_right) as (int32 **)) == at(l1, *((&g->rb_right) as (int32 **))) by solve();
                    have g->rb_right == 0 by { assumption(); }
                    have *((&p->rb_left) as (int32 **)) == at(l1, *((&p->rb_left) as (int32 **))) by solve();
                    have p->rb_left == node by { assumption(); }
                    have *((&g->__rb_parent_color) as (int32 **)) == at(l1, *((&g->__rb_parent_color) as (int32 **))) by solve();
                    have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above by { assumption(); }
                    have *((&g->rb_left) as (int32 **)) == at(l1, *((&g->rb_left) as (int32 **))) by solve();
                    have g->rb_left == p by { assumption(); }
                    mark l2; step();
                    have *((&g->rb_right) as (int32 **)) == at(l2, *((&g->rb_right) as (int32 **))) by solve();
                    have g->rb_right == 0 by { assumption(); }
                    have *((&p->rb_left) as (int32 **)) == at(l2, *((&p->rb_left) as (int32 **))) by solve();
                    have p->rb_left == node by { assumption(); }
                    have *((&g->__rb_parent_color) as (int32 **)) == at(l2, *((&g->__rb_parent_color) as (int32 **))) by solve();
                    have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above by { assumption(); }
                    have *((&g->rb_left) as (int32 **)) == at(l2, *((&g->rb_left) as (int32 **))) by solve();
                    have g->rb_left == p by { assumption(); }
                    mark l3; step();
                    have *((&g->rb_right) as (int32 **)) == at(l3, *((&g->rb_right) as (int32 **))) by solve();
                    have g->rb_right == 0 by { assumption(); }
                    have *((&p->rb_left) as (int32 **)) == at(l3, *((&p->rb_left) as (int32 **))) by solve();
                    have p->rb_left == node by { assumption(); }
                    have *((&g->__rb_parent_color) as (int32 **)) == at(l3, *((&g->__rb_parent_color) as (int32 **))) by solve();
                    have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above by { assumption(); }
                    have *((&g->rb_left) as (int32 **)) == at(l3, *((&g->rb_left) as (int32 **))) by solve();
                    have g->rb_left == p by { assumption(); }
                    mark l4; step();
                    have *((&g->rb_right) as (int32 **)) == at(l4, *((&g->rb_right) as (int32 **))) by solve();
                    have g->rb_right == 0 by { assumption(); }
                    have *((&p->rb_left) as (int32 **)) == at(l4, *((&p->rb_left) as (int32 **))) by solve();
                    have p->rb_left == node by { assumption(); }
                    have *((&g->__rb_parent_color) as (int32 **)) == at(l4, *((&g->__rb_parent_color) as (int32 **))) by solve();
                    have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above by { assumption(); }
                    have *((&g->rb_left) as (int32 **)) == at(l4, *((&g->rb_left) as (int32 **))) by solve();
                    have g->rb_left == p by { assumption(); }
                    mark l5; step();
                    have *((&g->rb_right) as (int32 **)) == at(l5, *((&g->rb_right) as (int32 **))) by solve();
                    have g->rb_right == 0 by { assumption(); }
                    have *((&p->rb_left) as (int32 **)) == at(l5, *((&p->rb_left) as (int32 **))) by solve();
                    have p->rb_left == node by { assumption(); }
                    have *((&g->__rb_parent_color) as (int32 **)) == at(l5, *((&g->__rb_parent_color) as (int32 **))) by solve();
                    have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above by { assumption(); }
                    have *((&g->rb_left) as (int32 **)) == at(l5, *((&g->rb_left) as (int32 **))) by solve();
                    have g->rb_left == p by { assumption(); }
                    mark l6; step();
                    have *((&g->rb_right) as (int32 **)) == at(l6, *((&g->rb_right) as (int32 **))) by solve();
                    have g->rb_right == 0 by { assumption(); }
                    have *((&p->rb_left) as (int32 **)) == at(l6, *((&p->rb_left) as (int32 **))) by solve();
                    have p->rb_left == node by { assumption(); }
                    have *((&g->__rb_parent_color) as (int32 **)) == at(l6, *((&g->__rb_parent_color) as (int32 **))) by solve();
                    have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above by { assumption(); }
                    have *((&g->rb_left) as (int32 **)) == at(l6, *((&g->rb_left) as (int32 **))) by solve();
                    have g->rb_left == p by { assumption(); }
                    have gparent == g by { assumption(); }
                    have parent == p by { assumption(); }
                    have parent->rb_left == node by { assumption(); }
                    mark before_link_writes;
                    have at(before_link_writes, ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above) by assumption();
                    have at(before_link_writes, parent->rb_left == node) by { assumption(); }
                    have at(before_link_writes, g->rb_left) == parent by { assumption(); }
                    mark w0; step();
                    have *((&g->rb_right) as (int32 **)) == at(w0, *((&g->rb_right) as (int32 **))) by solve();
                    have g->rb_right == 0 by { assumption(); }
                    have *((&p->rb_left) as (int32 **)) == at(w0, *((&p->rb_left) as (int32 **))) by solve();
                    have p->rb_left == node by { assumption(); }
                    have *((&g->__rb_parent_color) as (int32 **)) == at(w0, *((&g->__rb_parent_color) as (int32 **))) by solve();
                    have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above by { assumption(); }
                    mark w1; step();
                    have *((&g->rb_right) as (int32 **)) == at(w1, *((&g->rb_right) as (int32 **))) by solve();
                    have g->rb_right == 0 by { assumption(); }
                    have *((&p->rb_left) as (int32 **)) == at(w1, *((&p->rb_left) as (int32 **))) by solve();
                    have p->rb_left == node by { assumption(); }
                    have *((&g->__rb_parent_color) as (int32 **)) == at(w1, *((&g->__rb_parent_color) as (int32 **))) by solve();
                    have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above by { assumption(); }
                    mark w2; step();
                    have *((&g->rb_right) as (int32 **)) == at(w2, *((&g->rb_right) as (int32 **))) by solve();
                    have g->rb_right == 0 by { assumption(); }
                    have *((&p->rb_left) as (int32 **)) == at(w2, *((&p->rb_left) as (int32 **))) by solve();
                    have p->rb_left == node by { assumption(); }
                    have *((&g->__rb_parent_color) as (int32 **)) == at(w2, *((&g->__rb_parent_color) as (int32 **))) by solve();
                    have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above by { assumption(); }
                    have tmp == m by { assumption(); }
                    have tmp != 0 by { assumption(); }
                    have tmp != node by { assumption(); }
                    have node != 0 by { assumption(); }
                    mark w3; step();
                    have *((&g->rb_right) as (int32 **)) == at(w3, *((&g->rb_right) as (int32 **))) by solve();
                    have g->rb_right == 0 by { assumption(); }
                    have *((&p->rb_left) as (int32 **)) == at(w3, *((&p->rb_left) as (int32 **))) by solve();
                    have p->rb_left == node by { assumption(); }
                    have *((&g->__rb_parent_color) as (int32 **)) == at(w3, *((&g->__rb_parent_color) as (int32 **))) by solve();
                    have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above by { assumption(); }
                    mark w4; step();
                    have *((&g->rb_right) as (int32 **)) == at(w4, *((&g->rb_right) as (int32 **))) by solve();
                    have g->rb_right == 0 by { assumption(); }
                    have *((&p->rb_left) as (int32 **)) == at(w4, *((&p->rb_left) as (int32 **))) by solve();
                    have p->rb_left == node by { assumption(); }
                    have *((&g->__rb_parent_color) as (int32 **)) == at(w4, *((&g->__rb_parent_color) as (int32 **))) by solve();
                    have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above by { assumption(); }
                    have separate(memory(g->rb_left), memory(p->rb_left)) by solve();
                    have separate(memory(g->rb_left), memory(g->__rb_parent_color)) by solve();
                    have separate(memory(g->rb_left->rb_right), memory(p->rb_left)) by solve();
                    have separate(memory(g->rb_left->rb_right), memory(g->__rb_parent_color)) by solve();
                    have separate(memory(g->rb_left->rb_right), memory(g->rb_left)) by solve();
                    have separate(memory(g->rb_left), memory(g->rb_right)) by solve();
                    have separate(memory(g->rb_left->rb_right), memory(g->rb_right)) by solve();
                    mark w5;
                    have at(w5, separate(memory(g->rb_left->rb_right), memory(g->rb_right))) by { assumption(); }
                    have at(w5, separate(memory(g->rb_left->rb_right), memory(g->rb_left))) by { assumption(); }
                    have at(w5, separate(memory(g->rb_left->rb_right), memory(p->rb_left))) by { assumption(); }
                    have at(w5, separate(memory(g->rb_left->rb_right), memory(g->__rb_parent_color))) by { assumption(); }
                    step();
                    have separate(statement(1).statement(4).statement(3).footprint, memory(p->rb_left)) by {
                        normalize() using { separate(memory(g->rb_left), memory(p->rb_left)); };
                    }
                    have p->rb_left == at(w5, p->rb_left) by {
                        transport_certificate {
                            premise 0: separate(statement(1).statement(4).statement(3).footprint, memory(p->rb_left)) => separate(statement(1).statement(4).statement(3).footprint, memory(p->rb_left));
                            preserve 0 => p->rb_left == at(w5, p->rb_left);
                            conclusion 1;
                        }
                    }
                    have p->rb_left == node by { rewrite(p->rb_left == at(w5, p->rb_left)); assumption(); }
                    have separate(statement(1).statement(4).statement(3).footprint, memory(g->__rb_parent_color)) by {
                        normalize() using { separate(memory(g->rb_left), memory(g->__rb_parent_color)); };
                    }
                    have g->__rb_parent_color == at(w5, g->__rb_parent_color) by {
                        transport_certificate {
                            premise 0: separate(statement(1).statement(4).statement(3).footprint, memory(g->__rb_parent_color)) => separate(statement(1).statement(4).statement(3).footprint, memory(g->__rb_parent_color));
                            preserve 0 => g->__rb_parent_color == at(w5, g->__rb_parent_color);
                            conclusion 1;
                        }
                    }
                    have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above by { rewrite(g->__rb_parent_color == at(w5, g->__rb_parent_color)); assumption(); }
                    have separate(statement(1).statement(4).statement(3).footprint, memory(g->rb_right)) by {
                        normalize() using { separate(memory(g->rb_left), memory(g->rb_right)); };
                    }
                    have g->rb_right == at(w5, g->rb_right) by {
                        transport_certificate {
                            premise 0: separate(statement(1).statement(4).statement(3).footprint, memory(g->rb_right)) => separate(statement(1).statement(4).statement(3).footprint, memory(g->rb_right));
                            preserve 0 => g->rb_right == at(w5, g->rb_right);
                            conclusion 1;
                        }
                    }
                    have g->rb_right == 0 by { rewrite(g->rb_right == at(w5, g->rb_right)); assumption(); }
                    mark after_left_write;
                    have at(after_left_write, g->rb_left == m) by { assumption(); }
                    have separate(memory(g->rb_left), memory(parent->rb_right)) by { assumption(); }
                    have g->rb_left == m by { assumption(); }
                    mark w6; step();
                    have separate(statement(1).statement(4).statement(4).footprint, memory(p->rb_left)) by {
                        normalize() using { at(w5, separate(memory(g->rb_left->rb_right), memory(p->rb_left))); };
                    }
                    have p->rb_left == at(w6, p->rb_left) by {
                        transport_certificate {
                            premise 0: separate(statement(1).statement(4).statement(4).footprint, memory(p->rb_left)) => separate(statement(1).statement(4).statement(4).footprint, memory(p->rb_left));
                            preserve 0 => p->rb_left == at(w6, p->rb_left);
                            conclusion 1;
                        }
                    }
                    have p->rb_left == node by { rewrite(p->rb_left == at(w6, p->rb_left)); assumption(); }
                    have separate(statement(1).statement(4).statement(4).footprint, memory(g->__rb_parent_color)) by {
                        normalize() using { at(w5, separate(memory(g->rb_left->rb_right), memory(g->__rb_parent_color))); };
                    }
                    have g->__rb_parent_color == at(w6, g->__rb_parent_color) by {
                        transport_certificate {
                            premise 0: separate(statement(1).statement(4).statement(4).footprint, memory(g->__rb_parent_color)) => separate(statement(1).statement(4).statement(4).footprint, memory(g->__rb_parent_color));
                            preserve 0 => g->__rb_parent_color == at(w6, g->__rb_parent_color);
                            conclusion 1;
                        }
                    }
                    have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above by { rewrite(g->__rb_parent_color == at(w6, g->__rb_parent_color)); assumption(); }
                    have separate(statement(1).statement(4).statement(4).footprint, memory(g->rb_left)) by {
                        normalize() using { at(w5, separate(memory(g->rb_left->rb_right), memory(g->rb_left))); };
                    }
                    have g->rb_left == at(w6, g->rb_left) by {
                        transport_certificate {
                            premise 0: separate(statement(1).statement(4).statement(4).footprint, memory(g->rb_left)) => separate(statement(1).statement(4).statement(4).footprint, memory(g->rb_left));
                            preserve 0 => g->rb_left == at(w6, g->rb_left);
                            conclusion 1;
                        }
                    }
                    have g->rb_left == m by { rewrite(g->rb_left == at(w6, g->rb_left)); assumption(); }
                    have separate(statement(1).statement(4).statement(4).footprint, memory(g->rb_right)) by {
                        normalize() using { at(w5, separate(memory(g->rb_left->rb_right), memory(g->rb_right))); };
                    }
                    have g->rb_right == at(w6, g->rb_right) by {
                        transport_certificate {
                            premise 0: separate(statement(1).statement(4).statement(4).footprint, memory(g->rb_right)) => separate(statement(1).statement(4).statement(4).footprint, memory(g->rb_right));
                            preserve 0 => g->rb_right == at(w6, g->rb_right);
                            conclusion 1;
                        }
                    }
                    have g->rb_right == 0 by { rewrite(g->rb_right == at(w6, g->rb_right)); assumption(); }
                    have parent->rb_right == gparent by { assumption(); }
                    mark w7; step();
                    have *((&g->rb_right) as (int32 **)) == at(w7, *((&g->rb_right) as (int32 **))) by solve();
                    have g->rb_right == 0 by { assumption(); }
                    have *((&parent->rb_right) as (int32 **)) == at(w7, *((&parent->rb_right) as (int32 **))) by solve();
                    have parent->rb_right == gparent by { assumption(); }
                    have *((&p->rb_left) as (int32 **)) == at(w7, *((&p->rb_left) as (int32 **))) by solve();
                    have p->rb_left == node by { assumption(); }
                    have *((&g->__rb_parent_color) as (int32 **)) == at(w7, *((&g->__rb_parent_color) as (int32 **))) by solve();
                    have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above by { assumption(); }
                    have *((&g->rb_left) as (int32 **)) == at(w7, *((&g->rb_left) as (int32 **))) by solve();
                    have g->rb_left == m by { assumption(); }
                    mark before_reparent;
                    have at(before_reparent, g->rb_right == 0) by { assumption(); }
                    have at(before_reparent, parent->rb_right == gparent) by { assumption(); }
                    have at(before_reparent, parent->rb_left == node) by { assumption(); }
                    let { after: p_right } = step(insert::rb_set_parent_color, { tree: p_right });
                    unfold(sized_reparent(SizedTree::Node(m, p, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), g));
                    unfold(sized_recolor(SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), Color::Black));
                    have p_right.model == SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty) by { assumption(); }
                    have gparent->__rb_parent_color == address(above) + 1 by { solve(); }
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
                    transport(at(before_reparent, parent->rb_left == node), parent->rb_left == node);
                    transport(at(before_reparent, parent->rb_right == gparent), parent->rb_right == gparent);
                    transport(at(before_reparent, g->rb_right == 0), g->rb_right == 0);
                    mark before_parent_update;
                    have at(before_parent_update, g->rb_right == 0) by { assumption(); }
                    have at(before_parent_update, g->rb_left == m) by { assumption(); }
                    have at(before_parent_update, parent->rb_left == node) by { assumption(); }
                    have at(before_parent_update, parent->rb_right == gparent) by { assumption(); }
                    have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above by {
                        transport(at(before_link_writes, ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above),
                            ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above);
                    }
                    have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == sized_context_parent(link.model, 0) by {
                        rewrite(sized_context_parent(link.model, 0) == above); assumption();
                    }
                    let { after: link } = step(insert::__rb_rotate_set_parents, { c: link });
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
                    transport(at(before_parent_update, g->rb_right == 0), g->rb_right == 0);
                    let g_right = fold(sized_at(g->rb_right), { model: SizedTree::Empty });
                    unfold(sized_parent_is(SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), g));
                    let demoted = fold(sized_recompute_at(g), {
                        model: SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty)
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
                    have sized_parent_is(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty), p) == 1 by {
                        unfold(sized_parent_is(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty), p)); normalize();
                    }
                    have to_integer(sized_value(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty))) == 2 + to_integer(sized_value(sized_left(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty)))) + to_integer(sized_value(sized_right(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty)))) + to_integer(sized_value(SizedTree::Node(node, p, Color::Red, nv, left, right))) by {
                        unfold(sized_value(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty)));
                        unfold(sized_left(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty)));
                        unfold(sized_right(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty)));
                        unfold(sized_value(SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty)));
                        unfold(sized_value(SizedTree::Empty));
                        unfold(sized_value(SizedTree::Node(node, p, Color::Red, nv, left, right)));
                    }
                    let rotated = fold(sized_rotation_right_at(g, p), {
                        model: SizedTree::Node(p, above, Color::Black, pv,
                            SizedTree::Node(node, p, Color::Red, nv, left, right),
                            SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty))
                    }, { metadata: p_size, other: focus, demoted: demoted });
                    unfold(sized_right(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty))));
                    unfold(sized_left(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty)));
                    unfold(sized_right(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty)));
                    unfold(sized_value(SizedTree::Empty));
                    have 0 <= sized_value(sized_left(sized_right(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty))))) by {
                        rewrite(sized_right(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty))) == SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty));
                        rewrite(sized_left(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty)) == SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty));
                        unfold(sized_value(SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty))); normalize();
                    }
                    have 0 <= sized_value(sized_right(sized_right(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty))))) by {
                        rewrite(sized_right(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty))) == SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty));
                        rewrite(sized_right(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty)) == SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty) == 0); normalize();
                    }
                    have sized_value(sized_right(sized_right(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty))))) <= 2147483646 by {
                        rewrite(sized_right(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty))) == SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty));
                        rewrite(sized_right(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty)) == SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty) == 0); normalize();
                    }
                    have sized_value(sized_left(sized_right(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty))))) <= 2147483646 - sized_value(sized_right(sized_right(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty))))) by {
                        rewrite(sized_right(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty))) == SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty));
                        rewrite(sized_left(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty)) == SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty));
                        rewrite(sized_right(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty)) == SizedTree::Empty);
                        unfold(sized_value(SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty)));
                        rewrite(sized_value(SizedTree::Empty) == 0); normalize();
                    }
                    let { checked: checked } = step(RotateTreeRight, { tree: rotated });
                    have sized_shape(checked.model) == sized_context_middle_after(g, p, m, node, above, left, right) by {
                        rewrite(sized_shape(checked.model) == sized_shape(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty))));
                        unfold(sized_shape(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty))));
                        unfold(sized_shape(SizedTree::Node(node, p, Color::Red, nv, left, right)));
                        unfold(sized_shape(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty)));
                        unfold(sized_shape(SizedTree::Node(m, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty)));
                        unfold(sized_shape(SizedTree::Empty));
                        unfold(sized_context_middle_after(g, p, m, node, above, left, right)); normalize();
                    }
                    have rb_subtree_size(sized_context_middle_after(g, p, m, node, above, left, right)) == to_integer(gv) by {
                        unfold(sized_context_middle_after(g, p, m, node, above, left, right));
                        unfold(rb_subtree_size(RbTree::Node(p, above, Color::Black, RbTree::Node(node, p, Color::Red, sized_shape(left), sized_shape(right)), RbTree::Node(g, p, Color::Red, RbTree::Node(m, g, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Empty))));
                        unfold(rb_subtree_size(RbTree::Node(node, p, Color::Red, sized_shape(left), sized_shape(right))));
                        unfold(rb_subtree_size(RbTree::Node(g, p, Color::Red, RbTree::Node(m, g, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Empty)));
                        unfold(rb_subtree_size(RbTree::Node(m, g, Color::Black, RbTree::Empty, RbTree::Empty)));
                        unfold(rb_subtree_size(RbTree::Empty));
                        unfold(sized_shape(SizedTree::Node(node, p, Color::Red, nv, left, right)));
                        solve() using {
                            to_integer(gv) == 3 + to_integer(nv);
                            rb_subtree_size(sized_shape(left)) + rb_subtree_size(sized_shape(right)) + 1 == to_integer(nv);
                        };
                    }
                    have to_integer(sized_value(checked.model)) == to_integer(gv) by {
                        rewrite(to_integer(sized_value(checked.model)) == rb_subtree_size(sized_shape(checked.model)));
                        rewrite(sized_shape(checked.model) == sized_context_middle_after(g, p, m, node, above, left, right));
                        assumption();
                    }
                    have sized_value(checked.model) == gv;
                    apply(sized_parent_is_shape(checked.model, above));
                    have rb_parent_is(sized_shape(checked.model), above) == 1 by {
                        rewrite(sized_shape(checked.model) == sized_context_middle_after(g, p, m, node, above, left, right));
                        unfold(sized_context_middle_after(g, p, m, node, above, left, right));
                        unfold(rb_parent_is(RbTree::Node(p, above, Color::Black, RbTree::Node(node, p, Color::Red, sized_shape(left), sized_shape(right)), RbTree::Node(g, p, Color::Red, RbTree::Node(m, g, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Empty)), above)); normalize();
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
                    let state = fold(sized_insert_context_middle_at(node, root), {
                        phase: SizedInsertContextMiddlePhase::After(g, p, m, above, nv, pv, gv, left, right), model: at(before_restore, checked.model), context: old(state.context), whole_model: whole.model
                    }, { whole: whole });
                    have state.context == old(state.context) by { assumption(); }
                    have state.whole_model == sized_plug(old(state.context), state.model) by { assumption(); }
                    have state.phase == sized_context_middle_finish(old(state.phase)) by {
                        unfold(sized_context_middle_finish(SizedInsertContextMiddlePhase::Before(g, p, m, above, nv, pv, gv, left, right))); solve();
                    }
                    have sized_shape(state.model) == sized_context_middle_expected(old(state.phase), node) by {
                        rewrite(old(state.phase) == SizedInsertContextMiddlePhase::Before(g, p, m, above, nv, pv, gv, left, right));
                        unfold(sized_context_middle_expected(SizedInsertContextMiddlePhase::Before(g, p, m, above, nv, pv, gv, left, right), node)); solve();
                    }
                    step();
                }
            }
            have node == old(node) by { assumption(); }
            step_until(function.exit);
        },
    }
}

void insert::__rb_insert_augmented(struct rb_node* node, struct rb_root* root,
                  void (*augment_rotate)(struct rb_node*, struct rb_node*)) {
    requires RotateTreeRight(augment_rotate);
    owns state: sized_insert_context_middle_at(node, root);
    requires sized_context_middle_pending(state.phase) == 1;
    ensures state.context == old(state.context);
    ensures state.whole_model == sized_plug(old(state.context), state.model);
    ensures state.phase == sized_context_middle_finish(old(state.phase));
    ensures sized_shape(state.model) == sized_context_middle_expected(old(state.phase), node);
} by {
    step(insert::__rb_insert, { state: state });
}

void insert::rb_insert_augmented(struct rb_node* node, struct rb_root* root,
                         const struct rb_augment_callbacks* augment) {
    views augment->rotate;
    requires RotateTreeRight(augment->rotate);
    owns state: sized_insert_context_middle_at(node, root);
    requires sized_context_middle_pending(state.phase) == 1;
    ensures state.context == old(state.context);
    ensures state.whole_model == sized_plug(old(state.context), state.model);
    ensures state.phase == sized_context_middle_finish(old(state.phase));
    ensures sized_shape(state.model) == sized_context_middle_expected(old(state.phase), node);
} by {
    step(insert::__rb_insert_augmented, { state: state });
}
