// Left-left rotation with nonempty black middle and uncle subtrees.
// The focused node retains arbitrary child subtrees and the context is owned.
verifying "rb_insert_augmented.c" as insert;
verifying "rbtree_size_rotate.c";
verifying "rbtree_size_copy.c";
verifying "rbtree_size_compute.c";
import "rbtree_size_rotate_model.click";
import "rbtree_size_rotate_set_parents.click";
import "rbtree_size_reparent_call.click";
import "rbtree_size_insert_uncle_model.click";

spec enum SizedInsertContextUnclePhase {
    Before(struct rb_node*, struct rb_node*, struct rb_node*, struct rb_node*, struct rb_node*, int32, int32, int32, int32, int32, SizedTree, SizedTree, SizedTree, SizedTree, SizedTree, SizedTree),
    After(struct rb_node*, struct rb_node*, struct rb_node*, struct rb_node*, struct rb_node*, int32, int32, int32, int32, int32, SizedTree, SizedTree, SizedTree, SizedTree, SizedTree, SizedTree),
}

function sized_context_uncle_pending(phase: SizedInsertContextUnclePhase) -> int32 {
    match phase {
        SizedInsertContextUnclePhase::Before(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right) => 1,
        SizedInsertContextUnclePhase::After(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right) => 0,
    }
}

function sized_context_uncle_finish(phase: SizedInsertContextUnclePhase) -> SizedInsertContextUnclePhase {
    match phase {
        SizedInsertContextUnclePhase::Before(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right) => SizedInsertContextUnclePhase::After(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right),
        SizedInsertContextUnclePhase::After(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right) => SizedInsertContextUnclePhase::After(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right),
    }
}

function sized_context_uncle_expected(phase: SizedInsertContextUnclePhase, node: struct rb_node*) -> RbTree {
    match phase {
        SizedInsertContextUnclePhase::Before(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right) => sized_context_uncle_after(g, p, m, u, node, above, left, right, middle_left, middle_right, uncle_left, uncle_right),
        SizedInsertContextUnclePhase::After(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right) => sized_context_uncle_after(g, p, m, u, node, above, left, right, middle_left, middle_right, uncle_left, uncle_right),
    }
}


resource sized_insert_context_uncle_at(node: struct rb_node*, root: struct rb_root*) {
    field phase: SizedInsertContextUnclePhase;
    field model: SizedTree;
    field context: SizedContext;
    field whole_model: SizedTree;
    match phase {
        SizedInsertContextUnclePhase::Before(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right) => {
            owns link: sized_link_at(g, root, gv);
            owns tree: sized_at(g);
            fact link.model == context;
            fact above == sized_context_parent(context, 0);
            fact tree.model == model;
            fact model == sized_context_uncle_before(g, p, m, u, node, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right);
        },
        SizedInsertContextUnclePhase::After(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right) => {
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
    owns state: sized_insert_context_uncle_at(node, root);
    requires sized_context_uncle_pending(state.phase) == 1;
    ensures state.context == old(state.context);
    ensures state.whole_model == sized_plug(old(state.context), state.model);
    ensures state.phase == sized_context_uncle_finish(old(state.phase));
    ensures sized_shape(state.model) == sized_context_uncle_expected(old(state.phase), node);
} by {
    match state.phase {
        SizedInsertContextUnclePhase::After(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right) => {
            have sized_context_uncle_pending(state.phase) != 1 by {
                rewrite(state.phase == SizedInsertContextUnclePhase::After(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right));
                unfold(sized_context_uncle_pending(SizedInsertContextUnclePhase::After(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right))); normalize();
            }
            contradiction(sized_context_uncle_pending(state.phase) == 1);
        },
        SizedInsertContextUnclePhase::Before(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right) => {
            let { tree: tree, link: link } = unfold(state);
            unfold(sized_context_uncle_before(g, p, m, u, node, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right));
            have tree.model == SizedTree::Node(g, above, Color::Black, gv,
                SizedTree::Node(p, g, Color::Red, pv,
                    SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)) by {
                rewrite(tree.model == sized_context_uncle_before(g, p, m, u, node, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right));
                unfold(sized_context_uncle_before(g, p, m, u, node, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right)); normalize();
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
            have ((p->__rb_parent_color & ~3) as (struct rb_node *)) == g by { assumption(); }
            have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above by { assumption(); }
            have p->rb_right != p by { assumption(); }
            have p->rb_left == node by { assumption(); }
            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == p by { assumption(); }
            mark m0; step();
            have *((&node->__rb_parent_color) as (int32 **)) == at(m0, *((&node->__rb_parent_color) as (int32 **))) by solve();
            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == p by { assumption(); }
            have p->rb_left == at(m0, p->rb_left) by solve();
            have p->rb_left == node by { rewrite(p->rb_left == at(m0, p->rb_left)); assumption(); }
            have p->rb_right == at(m0, p->rb_right) by solve();
            have p->rb_right != p by { rewrite(p->rb_right == at(m0, p->rb_right)); assumption(); }
            have *((&p->__rb_parent_color) as (int32 **)) == at(m0, *((&p->__rb_parent_color) as (int32 **))) by solve();
            have ((p->__rb_parent_color & ~3) as (struct rb_node *)) == g by { assumption(); }
            have *((&g->__rb_parent_color) as (int32 **)) == at(m0, *((&g->__rb_parent_color) as (int32 **))) by solve();
            have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above by { assumption(); }
            mark m1; step();
            have *((&node->__rb_parent_color) as (int32 **)) == at(m1, *((&node->__rb_parent_color) as (int32 **))) by solve();
            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == p by { assumption(); }
            have p->rb_left == at(m1, p->rb_left) by solve();
            have p->rb_left == node by { rewrite(p->rb_left == at(m1, p->rb_left)); assumption(); }
            have p->rb_right == at(m1, p->rb_right) by solve();
            have p->rb_right != p by { rewrite(p->rb_right == at(m1, p->rb_right)); assumption(); }
            have *((&p->__rb_parent_color) as (int32 **)) == at(m1, *((&p->__rb_parent_color) as (int32 **))) by solve();
            have ((p->__rb_parent_color & ~3) as (struct rb_node *)) == g by { assumption(); }
            have *((&g->__rb_parent_color) as (int32 **)) == at(m1, *((&g->__rb_parent_color) as (int32 **))) by solve();
            have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above by { assumption(); }
            mark m2; step();
            have *((&node->__rb_parent_color) as (int32 **)) == at(m2, *((&node->__rb_parent_color) as (int32 **))) by solve();
            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == p by { assumption(); }
            have p->rb_left == at(m2, p->rb_left) by solve();
            have p->rb_left == node by { rewrite(p->rb_left == at(m2, p->rb_left)); assumption(); }
            have p->rb_right == at(m2, p->rb_right) by solve();
            have p->rb_right != p by { rewrite(p->rb_right == at(m2, p->rb_right)); assumption(); }
            have *((&p->__rb_parent_color) as (int32 **)) == at(m2, *((&p->__rb_parent_color) as (int32 **))) by solve();
            have ((p->__rb_parent_color & ~3) as (struct rb_node *)) == g by { assumption(); }
            have *((&g->__rb_parent_color) as (int32 **)) == at(m2, *((&g->__rb_parent_color) as (int32 **))) by solve();
            have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above by { assumption(); }
            mark m3; step();
            have *((&node->__rb_parent_color) as (int32 **)) == at(m3, *((&node->__rb_parent_color) as (int32 **))) by solve();
            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == p by { assumption(); }
            have p->rb_left == at(m3, p->rb_left) by solve();
            have p->rb_left == node by { rewrite(p->rb_left == at(m3, p->rb_left)); assumption(); }
            have p->rb_right == at(m3, p->rb_right) by solve();
            have p->rb_right != p by { rewrite(p->rb_right == at(m3, p->rb_right)); assumption(); }
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
            let parent_tree = fold(sized_at(p), { model: SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)) }, { metadata: p_size, left: focus, right: p_right });
            let tree = fold(sized_at(g), { model: old(state.model) }, { metadata: g_size, left: parent_tree, right: g_right });
            let state = fold(sized_insert_context_uncle_at(node, root), { phase: SizedInsertContextUnclePhase::Before(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right), model: old(state.model), context: old(state.context), whole_model: old(state.whole_model) }, { tree: tree, link: link });
            loop {
                owns state: sized_insert_context_uncle_at(node, root);
                decreases 0;
                invariant node == old(node);
                invariant parent == p;
                invariant state.context == old(state.context);
                invariant p == old(g->rb_left);
                invariant state.phase == SizedInsertContextUnclePhase::Before(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right);
                invariant old(state.phase) == SizedInsertContextUnclePhase::Before(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right);
                invariant state.model == sized_context_uncle_before(g, p, m, u, node, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right);
                initialize by solve();
                preserve by {
                    let { tree: loop_tree, link: link } = unfold(state);
                    unfold(sized_context_uncle_before(g, p, m, u, node, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right));
                    have loop_tree.model == SizedTree::Node(g, above, Color::Black, gv,
                        SizedTree::Node(p, g, Color::Red, pv,
                            SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)) by {
                        rewrite(loop_tree.model == sized_context_uncle_before(g, p, m, u, node, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right));
                        unfold(sized_context_uncle_before(g, p, m, u, node, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right)); normalize();
                    }
                    let { metadata: g_size, left: parent_tree, right: g_right } = unfold(loop_tree);
                    let { metadata: p_size, left: focus, right: p_right } = unfold(parent_tree);
                    let { metadata: u_size, left: u_left, right: u_right } = unfold(g_right);
                    have g->rb_right == u by { assumption(); }
                    have separate(memory(p->__rb_parent_color), memory(u->__rb_parent_color)) by { assumption(); }
                    have p != u by { assumption(); }
                    unfold(color_bit(Color::Black));
                    have (u->__rb_parent_color & 1) == 1 by {
                        rewrite((u->__rb_parent_color & 1) == color_bit(Color::Black));
                        rewrite(color_bit(Color::Black) == 1); normalize();
                    }
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
                    let g_right = fold(sized_at(g->rb_right), { model: SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right) }, { metadata: u_size, left: u_left, right: u_right });
                    let { checked: g_right } = certify_size(g->rb_right, { tree: g_right });
                    unfold(sized_value(SizedTree::Node(node, p, Color::Red, nv, left, right)));
                    unfold(sized_value(SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))));
                    unfold(sized_value(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)));
                    have to_integer(sized_value(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))) == to_integer(uv) by {
                        rewrite(sized_value(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)) == uv); solve();
                    }
                    unfold(sized_value(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)));
                    have to_integer(sized_value(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))) == to_integer(mv) by {
                        rewrite(sized_value(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)) == mv); normalize();
                    }
                    have to_integer(gv) == 2 + to_integer(nv) + to_integer(mv) + to_integer(uv) by {
                        solve() using {
                            to_integer(gv) == 1 + to_integer(pv) + to_integer(sized_value(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)));
                            to_integer(pv) == 1 + to_integer(nv) + to_integer(sized_value(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)));
                            to_integer(sized_value(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))) == to_integer(mv);
                            to_integer(sized_value(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))) == to_integer(uv);
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
                    have 0 <= to_integer(nv) by { solve() using {
                        rb_subtree_size(sized_shape(SizedTree::Node(node, p, Color::Red, nv, left, right))) == to_integer(nv);
                        rb_subtree_size(sized_shape(SizedTree::Node(node, p, Color::Red, nv, left, right))) >= 0;
                    }; }
                    have 0 <= to_integer(mv) by { solve() using {
                        rb_subtree_size(sized_shape(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))) == to_integer(mv);
                        rb_subtree_size(sized_shape(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))) >= 0;
                    }; }
                    have rb_subtree_size(sized_shape(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))) == to_integer(uv) by { assumption(); }
                    have rb_subtree_size(sized_shape(uncle_left)) + rb_subtree_size(sized_shape(uncle_right)) + 1 == to_integer(uv) by {
                        rewrite(to_integer(uv) == rb_subtree_size(sized_shape(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))));
                        unfold(sized_shape(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)));
                        unfold(rb_subtree_size(RbTree::Node(u, g, Color::Black, sized_shape(uncle_left), sized_shape(uncle_right)))); normalize();
                    }
                    apply(rb_subtree_size_nonnegative(sized_shape(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))));
                    have 0 <= to_integer(uv) by { solve() using {
                        rb_subtree_size(sized_shape(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))) == to_integer(uv);
                        rb_subtree_size(sized_shape(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))) >= 0;
                    }; }
                    have -2147483648 <= to_integer(gv);
                    have to_integer(gv) <= 2147483647;
                    have 1 + to_integer(mv) + to_integer(uv) <= 2147483647 by { solve() using {
                        to_integer(gv) == 2 + to_integer(nv) + to_integer(mv) + to_integer(uv);
                        to_integer(nv) >= 0;
                        to_integer(gv) <= 2147483647;
                    }; }
                    apply(size_children_fit(mv, uv));
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
                    let { metadata: u_size, left: u_left, right: u_right } = unfold(g_right);
                    have p->rb_left == node by { assumption(); }
                    have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above by { assumption(); }
                    have g->rb_left == p by { assumption(); }
                    have g->rb_right == u by { assumption(); }
                    have ((u->__rb_parent_color & ~3) as (struct rb_node *)) == g by { assumption(); }
                    mark u0; step();
                    have *((&u->__rb_parent_color) as (int32 **)) == at(u0, *((&u->__rb_parent_color) as (int32 **))) by solve();
                    have ((u->__rb_parent_color & ~3) as (struct rb_node *)) == g by { assumption(); }
                    have g->rb_right == at(u0, g->rb_right) by solve();
                    have g->rb_right == u by { rewrite(g->rb_right == at(u0, g->rb_right)); assumption(); }
                    have g->rb_left == at(u0, g->rb_left) by solve();
                    have g->rb_left == p by { rewrite(g->rb_left == at(u0, g->rb_left)); assumption(); }
                    have *((&g->__rb_parent_color) as (int32 **)) == at(u0, *((&g->__rb_parent_color) as (int32 **))) by solve();
                    have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above by { assumption(); }
                    have p->rb_left == at(u0, p->rb_left) by solve();
                    have p->rb_left == node by { rewrite(p->rb_left == at(u0, p->rb_left)); assumption(); }
                    mark u1; step();
                    have *((&u->__rb_parent_color) as (int32 **)) == at(u1, *((&u->__rb_parent_color) as (int32 **))) by solve();
                    have ((u->__rb_parent_color & ~3) as (struct rb_node *)) == g by { assumption(); }
                    have g->rb_right == at(u1, g->rb_right) by solve();
                    have g->rb_right == u by { rewrite(g->rb_right == at(u1, g->rb_right)); assumption(); }
                    have g->rb_left == at(u1, g->rb_left) by solve();
                    have g->rb_left == p by { rewrite(g->rb_left == at(u1, g->rb_left)); assumption(); }
                    have *((&g->__rb_parent_color) as (int32 **)) == at(u1, *((&g->__rb_parent_color) as (int32 **))) by solve();
                    have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above by { assumption(); }
                    have p->rb_left == at(u1, p->rb_left) by solve();
                    have p->rb_left == node by { rewrite(p->rb_left == at(u1, p->rb_left)); assumption(); }
                    mark u2; step();
                    have *((&u->__rb_parent_color) as (int32 **)) == at(u2, *((&u->__rb_parent_color) as (int32 **))) by solve();
                    have ((u->__rb_parent_color & ~3) as (struct rb_node *)) == g by { assumption(); }
                    have g->rb_right == at(u2, g->rb_right) by solve();
                    have g->rb_right == u by { rewrite(g->rb_right == at(u2, g->rb_right)); assumption(); }
                    have g->rb_left == at(u2, g->rb_left) by solve();
                    have g->rb_left == p by { rewrite(g->rb_left == at(u2, g->rb_left)); assumption(); }
                    have *((&g->__rb_parent_color) as (int32 **)) == at(u2, *((&g->__rb_parent_color) as (int32 **))) by solve();
                    have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above by { assumption(); }
                    have p->rb_left == at(u2, p->rb_left) by solve();
                    have p->rb_left == node by { rewrite(p->rb_left == at(u2, p->rb_left)); assumption(); }
                    mark u3; step();
                    have *((&u->__rb_parent_color) as (int32 **)) == at(u3, *((&u->__rb_parent_color) as (int32 **))) by solve();
                    have ((u->__rb_parent_color & ~3) as (struct rb_node *)) == g by { assumption(); }
                    have g->rb_right == at(u3, g->rb_right) by solve();
                    have g->rb_right == u by { rewrite(g->rb_right == at(u3, g->rb_right)); assumption(); }
                    have g->rb_left == at(u3, g->rb_left) by solve();
                    have g->rb_left == p by { rewrite(g->rb_left == at(u3, g->rb_left)); assumption(); }
                    have *((&g->__rb_parent_color) as (int32 **)) == at(u3, *((&g->__rb_parent_color) as (int32 **))) by solve();
                    have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above by { assumption(); }
                    have p->rb_left == at(u3, p->rb_left) by solve();
                    have p->rb_left == node by { rewrite(p->rb_left == at(u3, p->rb_left)); assumption(); }
                    mark u4; step();
                    have *((&u->__rb_parent_color) as (int32 **)) == at(u4, *((&u->__rb_parent_color) as (int32 **))) by solve();
                    have ((u->__rb_parent_color & ~3) as (struct rb_node *)) == g by { assumption(); }
                    have g->rb_right == at(u4, g->rb_right) by solve();
                    have g->rb_right == u by { rewrite(g->rb_right == at(u4, g->rb_right)); assumption(); }
                    have g->rb_left == at(u4, g->rb_left) by solve();
                    have g->rb_left == p by { rewrite(g->rb_left == at(u4, g->rb_left)); assumption(); }
                    have *((&g->__rb_parent_color) as (int32 **)) == at(u4, *((&g->__rb_parent_color) as (int32 **))) by solve();
                    have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above by { assumption(); }
                    have p->rb_left == at(u4, p->rb_left) by solve();
                    have p->rb_left == node by { rewrite(p->rb_left == at(u4, p->rb_left)); assumption(); }
                    mark u5; step();
                    have *((&u->__rb_parent_color) as (int32 **)) == at(u5, *((&u->__rb_parent_color) as (int32 **))) by solve();
                    have ((u->__rb_parent_color & ~3) as (struct rb_node *)) == g by { assumption(); }
                    have g->rb_right == at(u5, g->rb_right) by solve();
                    have g->rb_right == u by { rewrite(g->rb_right == at(u5, g->rb_right)); assumption(); }
                    have g->rb_left == at(u5, g->rb_left) by solve();
                    have g->rb_left == p by { rewrite(g->rb_left == at(u5, g->rb_left)); assumption(); }
                    have *((&g->__rb_parent_color) as (int32 **)) == at(u5, *((&g->__rb_parent_color) as (int32 **))) by solve();
                    have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above by { assumption(); }
                    have p->rb_left == at(u5, p->rb_left) by solve();
                    have p->rb_left == node by { rewrite(p->rb_left == at(u5, p->rb_left)); assumption(); }
                    mark u6; step();
                    have *((&u->__rb_parent_color) as (int32 **)) == at(u6, *((&u->__rb_parent_color) as (int32 **))) by solve();
                    have ((u->__rb_parent_color & ~3) as (struct rb_node *)) == g by { assumption(); }
                    have g->rb_right == at(u6, g->rb_right) by solve();
                    have g->rb_right == u by { rewrite(g->rb_right == at(u6, g->rb_right)); assumption(); }
                    have g->rb_left == at(u6, g->rb_left) by solve();
                    have g->rb_left == p by { rewrite(g->rb_left == at(u6, g->rb_left)); assumption(); }
                    have *((&g->__rb_parent_color) as (int32 **)) == at(u6, *((&g->__rb_parent_color) as (int32 **))) by solve();
                    have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above by { assumption(); }
                    have p->rb_left == at(u6, p->rb_left) by solve();
                    have p->rb_left == node by { rewrite(p->rb_left == at(u6, p->rb_left)); assumption(); }
                    let g_right = fold(sized_at(g->rb_right), { model: SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right) }, { metadata: u_size, left: u_left, right: u_right });
                    have gparent == g by { assumption(); }
                    have parent == p by { assumption(); }
                    have parent->rb_left == node by { assumption(); }
                    mark before_link_writes;
                    have at(before_link_writes, ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above) by assumption();
                    have at(before_link_writes, parent->rb_left == node) by { assumption(); }
                    have at(before_link_writes, g->rb_left) == parent by { assumption(); }
                    have at(before_link_writes, g->rb_right) == u by { assumption(); }
                    mark w0; step();
                    have p->rb_left == at(w0, p->rb_left) by solve();
                    have p->rb_left == node by { rewrite(p->rb_left == at(w0, p->rb_left)); assumption(); }
                    have g->rb_right == at(w0, g->rb_right) by solve();
                    have g->rb_right == u by { rewrite(g->rb_right == at(w0, g->rb_right)); assumption(); }
                    have *((&g->__rb_parent_color) as (int32 **)) == at(w0, *((&g->__rb_parent_color) as (int32 **))) by solve();
                    have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above by { assumption(); }
                    mark w1; step();
                    have p->rb_left == at(w1, p->rb_left) by solve();
                    have p->rb_left == node by { rewrite(p->rb_left == at(w1, p->rb_left)); assumption(); }
                    have g->rb_right == at(w1, g->rb_right) by solve();
                    have g->rb_right == u by { rewrite(g->rb_right == at(w1, g->rb_right)); assumption(); }
                    have *((&g->__rb_parent_color) as (int32 **)) == at(w1, *((&g->__rb_parent_color) as (int32 **))) by solve();
                    have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above by { assumption(); }
                    mark w2; step();
                    have p->rb_left == at(w2, p->rb_left) by solve();
                    have p->rb_left == node by { rewrite(p->rb_left == at(w2, p->rb_left)); assumption(); }
                    have g->rb_right == at(w2, g->rb_right) by solve();
                    have g->rb_right == u by { rewrite(g->rb_right == at(w2, g->rb_right)); assumption(); }
                    have *((&g->__rb_parent_color) as (int32 **)) == at(w2, *((&g->__rb_parent_color) as (int32 **))) by solve();
                    have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above by { assumption(); }
                    have tmp == m by { assumption(); }
                    have tmp != 0 by { assumption(); }
                    have tmp != node by { assumption(); }
                    have node != 0 by { assumption(); }
                    mark w3; step();
                    have p->rb_left == at(w3, p->rb_left) by solve();
                    have p->rb_left == node by { rewrite(p->rb_left == at(w3, p->rb_left)); assumption(); }
                    have g->rb_right == at(w3, g->rb_right) by solve();
                    have g->rb_right == u by { rewrite(g->rb_right == at(w3, g->rb_right)); assumption(); }
                    have *((&g->__rb_parent_color) as (int32 **)) == at(w3, *((&g->__rb_parent_color) as (int32 **))) by solve();
                    have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above by { assumption(); }
                    mark w4; step();
                    have p->rb_left == at(w4, p->rb_left) by solve();
                    have p->rb_left == node by { rewrite(p->rb_left == at(w4, p->rb_left)); assumption(); }
                    have g->rb_right == at(w4, g->rb_right) by solve();
                    have g->rb_right == u by { rewrite(g->rb_right == at(w4, g->rb_right)); assumption(); }
                    have *((&g->__rb_parent_color) as (int32 **)) == at(w4, *((&g->__rb_parent_color) as (int32 **))) by solve();
                    have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above by { assumption(); }
                    have separate(memory(g->rb_left->rb_right), memory(p->rb_left)) by solve();
                    have separate(memory(g->rb_left->rb_right), memory(g->__rb_parent_color)) by solve();
                    have separate(memory(g->rb_left->rb_right), memory(g->rb_left)) by solve();
                    have separate(memory(g->rb_left->rb_right), memory(g->rb_right)) by solve();
                    mark w5;
                    have at(w5, separate(memory(g->rb_left->rb_right), memory(g->rb_right))) by { assumption(); }
                    have at(w5, separate(memory(g->rb_left->rb_right), memory(g->rb_left))) by { assumption(); }
                    have at(w5, separate(memory(g->rb_left->rb_right), memory(g->__rb_parent_color))) by { assumption(); }
                    have at(w5, separate(memory(g->rb_left->rb_right), memory(p->rb_left))) by { assumption(); }
                    step();
                    have separate(memory(g->rb_left), memory(p->rb_left)) by solve();
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
                    have separate(memory(g->rb_left), memory(g->rb_right)) by solve();
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
                    have g->rb_right == u by { rewrite(g->rb_right == at(w5, g->rb_right)); assumption(); }
                    have separate(memory(g->rb_left), memory(g->__rb_parent_color)) by solve();
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
                    mark after_left_write;
                    have at(after_left_write, g->rb_left == m) by { assumption(); }
                    have g->rb_left == m by { assumption(); }
                    have separate(memory(g->rb_left), memory(parent->rb_right)) by { assumption(); }
                    mark w6; step();
                    have parent->rb_right == gparent by { assumption(); }
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
                    have g->rb_right == u by { rewrite(g->rb_right == at(w6, g->rb_right)); assumption(); }
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
                    mark w7; step();
                    have p->rb_left == at(w7, p->rb_left) by solve();
                    have p->rb_left == node by { rewrite(p->rb_left == at(w7, p->rb_left)); assumption(); }
                    have g->rb_right == at(w7, g->rb_right) by solve();
                    have g->rb_right == u by { rewrite(g->rb_right == at(w7, g->rb_right)); assumption(); }
                    have *((&g->__rb_parent_color) as (int32 **)) == at(w7, *((&g->__rb_parent_color) as (int32 **))) by solve();
                    have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above by { assumption(); }
                    have g->rb_left == at(w7, g->rb_left) by solve();
                    have g->rb_left == m by { rewrite(g->rb_left == at(w7, g->rb_left)); assumption(); }
                    have parent->rb_right == at(w7, parent->rb_right) by solve();
                    have parent->rb_right == gparent by { rewrite(parent->rb_right == at(w7, parent->rb_right)); assumption(); }
                    mark wc;
                    let { after: p_right } = step(insert::rb_set_parent_color, { tree: p_right });
                    have parent->rb_right == at(wc, parent->rb_right) by solve();
                    have parent->rb_right == gparent by { rewrite(parent->rb_right == at(wc, parent->rb_right)); assumption(); }
                    have p->rb_left == at(wc, p->rb_left) by solve();
                    have p->rb_left == node by { rewrite(p->rb_left == at(wc, p->rb_left)); assumption(); }
                    have g->rb_right == at(wc, g->rb_right) by solve();
                    have g->rb_right == u by { rewrite(g->rb_right == at(wc, g->rb_right)); assumption(); }
                    have g->__rb_parent_color == at(wc, g->__rb_parent_color) by solve();
                    have ((g->__rb_parent_color & ~3) as (struct rb_node *)) == above by { rewrite(g->__rb_parent_color == at(wc, g->__rb_parent_color)); assumption(); }
                    unfold(sized_reparent(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), g));
                    unfold(sized_recolor(SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), Color::Black));
                    have p_right.model == SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right) by { assumption(); }
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
                    transport(at(before_link_writes, parent->rb_left == node), parent->rb_left == node);
                    have parent->rb_right == gparent by { solve(); }
                    mark before_parent_update;
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
                    have g->rb_right == at(before_parent_update, g->rb_right) by solve();
                    have g->rb_right == u by { rewrite(g->rb_right == at(before_parent_update, g->rb_right)); assumption(); }

                    unfold(sized_parent_is(SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), g));
                    let demoted = fold(sized_recompute_at(g), {
                        model: SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))
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
                    have sized_parent_is(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)), p) == 1 by {
                        unfold(sized_parent_is(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)), p)); normalize();
                    }
                    have to_integer(sized_value(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)))) == 2 + to_integer(sized_value(sized_left(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))))) + to_integer(sized_value(sized_right(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))))) + to_integer(sized_value(SizedTree::Node(node, p, Color::Red, nv, left, right))) by {
                        unfold(sized_value(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))));
                        unfold(sized_left(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))));
                        unfold(sized_right(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))));
                        unfold(sized_value(SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right)));
                        unfold(sized_value(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)));
                        unfold(sized_value(SizedTree::Node(node, p, Color::Red, nv, left, right)));
                        solve() using { to_integer(gv) == 2 + to_integer(nv) + to_integer(mv) + to_integer(uv); };
                    }
                    let rotated = fold(sized_rotation_right_at(g, p), {
                        model: SizedTree::Node(p, above, Color::Black, pv,
                            SizedTree::Node(node, p, Color::Red, nv, left, right),
                            SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)))
                    }, { metadata: p_size, other: focus, demoted: demoted });
                    unfold(sized_right(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)))));
                    unfold(sized_left(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))));
                    unfold(sized_right(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))));
                    unfold(sized_value(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)));
                    have 0 <= sized_value(sized_left(sized_right(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)))))) by {
                        rewrite(sized_right(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)))) == SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)));
                        rewrite(sized_left(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))) == SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right));
                        unfold(sized_value(SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right))); solve();
                    }
                    have 0 <= sized_value(sized_right(sized_right(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)))))) by {
                        rewrite(sized_right(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)))) == SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)));
                        rewrite(sized_right(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))) == SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right));
                        rewrite(sized_value(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)) == uv); solve();
                    }
                    have sized_value(sized_right(sized_right(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)))))) <= 2147483646 by {
                        rewrite(sized_right(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)))) == SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)));
                        rewrite(sized_right(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))) == SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right));
                        rewrite(sized_value(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)) == uv); solve();
                    }
                    have sized_value(sized_left(sized_right(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)))))) <= 2147483646 - sized_value(sized_right(sized_right(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)))))) by {
                        rewrite(sized_right(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)))) == SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)));
                        rewrite(sized_left(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))) == SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right));
                        rewrite(sized_right(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))) == SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right));
                        unfold(sized_value(SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right)));
                        rewrite(sized_value(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)) == uv); solve();
                    }
                    let { checked: checked } = step(RotateTreeRight, { tree: rotated });
                    have sized_shape(checked.model) == sized_context_uncle_after(g, p, m, u, node, above, left, right, middle_left, middle_right, uncle_left, uncle_right) by {
                        rewrite(sized_shape(checked.model) == sized_shape(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)))));
                        unfold(sized_shape(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)))));
                        unfold(sized_shape(SizedTree::Node(node, p, Color::Red, nv, left, right)));
                        unfold(sized_shape(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))));
                        unfold(sized_shape(SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right)));
                        unfold(sized_shape(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)));
                        unfold(sized_context_uncle_after(g, p, m, u, node, above, left, right, middle_left, middle_right, uncle_left, uncle_right)); normalize();
                    }
                    have rb_subtree_size(sized_context_uncle_after(g, p, m, u, node, above, left, right, middle_left, middle_right, uncle_left, uncle_right)) == to_integer(gv) by {
                        unfold(sized_context_uncle_after(g, p, m, u, node, above, left, right, middle_left, middle_right, uncle_left, uncle_right));
                        unfold(rb_subtree_size(RbTree::Node(p, above, Color::Black, RbTree::Node(node, p, Color::Red, sized_shape(left), sized_shape(right)), RbTree::Node(g, p, Color::Red, RbTree::Node(m, g, Color::Black, sized_shape(middle_left), sized_shape(middle_right)), RbTree::Node(u, g, Color::Black, sized_shape(uncle_left), sized_shape(uncle_right))))));
                        unfold(rb_subtree_size(RbTree::Node(node, p, Color::Red, sized_shape(left), sized_shape(right))));
                        unfold(rb_subtree_size(RbTree::Node(g, p, Color::Red, RbTree::Node(m, g, Color::Black, sized_shape(middle_left), sized_shape(middle_right)), RbTree::Node(u, g, Color::Black, sized_shape(uncle_left), sized_shape(uncle_right)))));
                        unfold(rb_subtree_size(RbTree::Node(m, g, Color::Black, sized_shape(middle_left), sized_shape(middle_right))));
                        unfold(rb_subtree_size(RbTree::Node(u, g, Color::Black, sized_shape(uncle_left), sized_shape(uncle_right))));
                        unfold(sized_shape(SizedTree::Node(node, p, Color::Red, nv, left, right)));
                        solve() using {
                            to_integer(gv) == 2 + to_integer(nv) + to_integer(mv) + to_integer(uv);
                            rb_subtree_size(sized_shape(left)) + rb_subtree_size(sized_shape(right)) + 1 == to_integer(nv);
                            rb_subtree_size(sized_shape(middle_left)) + rb_subtree_size(sized_shape(middle_right)) + 1 == to_integer(mv);
                            rb_subtree_size(sized_shape(uncle_left)) + rb_subtree_size(sized_shape(uncle_right)) + 1 == to_integer(uv);
                        };
                    }
                    have to_integer(sized_value(checked.model)) == to_integer(gv) by {
                        rewrite(to_integer(sized_value(checked.model)) == rb_subtree_size(sized_shape(checked.model)));
                        rewrite(sized_shape(checked.model) == sized_context_uncle_after(g, p, m, u, node, above, left, right, middle_left, middle_right, uncle_left, uncle_right));
                        assumption();
                    }
                    have sized_value(checked.model) == gv;
                    apply(sized_parent_is_shape(checked.model, above));
                    have rb_parent_is(sized_shape(checked.model), above) == 1 by {
                        rewrite(sized_shape(checked.model) == sized_context_uncle_after(g, p, m, u, node, above, left, right, middle_left, middle_right, uncle_left, uncle_right));
                        unfold(sized_context_uncle_after(g, p, m, u, node, above, left, right, middle_left, middle_right, uncle_left, uncle_right));
                        unfold(rb_parent_is(RbTree::Node(p, above, Color::Black, RbTree::Node(node, p, Color::Red, sized_shape(left), sized_shape(right)), RbTree::Node(g, p, Color::Red, RbTree::Node(m, g, Color::Black, sized_shape(middle_left), sized_shape(middle_right)), RbTree::Node(u, g, Color::Black, sized_shape(uncle_left), sized_shape(uncle_right)))), above)); normalize();
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
                    let state = fold(sized_insert_context_uncle_at(node, root), {
                        phase: SizedInsertContextUnclePhase::After(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right), model: at(before_restore, checked.model), context: old(state.context), whole_model: whole.model
                    }, { whole: whole });
                    have state.context == old(state.context) by { assumption(); }
                    have state.whole_model == sized_plug(old(state.context), state.model) by { assumption(); }
                    have state.phase == sized_context_uncle_finish(old(state.phase)) by {
                        unfold(sized_context_uncle_finish(SizedInsertContextUnclePhase::Before(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right))); solve();
                    }
                    have sized_shape(state.model) == sized_context_uncle_expected(old(state.phase), node) by {
                        rewrite(old(state.phase) == SizedInsertContextUnclePhase::Before(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right));
                        unfold(sized_context_uncle_expected(SizedInsertContextUnclePhase::Before(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right), node)); solve();
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
    owns state: sized_insert_context_uncle_at(node, root);
    requires sized_context_uncle_pending(state.phase) == 1;
    ensures state.context == old(state.context);
    ensures state.whole_model == sized_plug(old(state.context), state.model);
    ensures state.phase == sized_context_uncle_finish(old(state.phase));
    ensures sized_shape(state.model) == sized_context_uncle_expected(old(state.phase), node);
} by {
    step(insert::__rb_insert, { state: state });
}

void insert::rb_insert_augmented(struct rb_node* node, struct rb_root* root,
                         const struct rb_augment_callbacks* augment) {
    views augment->rotate;
    requires RotateTreeRight(augment->rotate);
    owns state: sized_insert_context_uncle_at(node, root);
    requires sized_context_uncle_pending(state.phase) == 1;
    ensures state.context == old(state.context);
    ensures state.whole_model == sized_plug(old(state.context), state.model);
    ensures state.phase == sized_context_uncle_finish(old(state.phase));
    ensures sized_shape(state.model) == sized_context_uncle_expected(old(state.phase), node);
} by {
    step(insert::__rb_insert_augmented, { state: state });
}
