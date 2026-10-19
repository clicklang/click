// Right-right rotation with nonempty black middle and uncle subtrees.
// The focused node retains arbitrary child subtrees and the context is owned.
verifying "rb_insert_augmented.c" as insert;
verifying "rbtree_size_rotate.c";
verifying "rbtree_size_copy.c";
verifying "rbtree_size_compute.c";
import "rbtree_size_rotate_model.click";
import "rbtree_size_rotate_set_parents.click";
import "rbtree_size_reparent_call.click";
import "rbtree_size_insert_mirrored_uncle_model.click";

spec enum SizedInsertMirroredContextUnclePhase {
    Before(struct rb_node*, struct rb_node*, struct rb_node*, struct rb_node*, struct rb_node*, int32, int32, int32, int32, int32, SizedTree, SizedTree, SizedTree, SizedTree, SizedTree, SizedTree),
    After(struct rb_node*, struct rb_node*, struct rb_node*, struct rb_node*, struct rb_node*, int32, int32, int32, int32, int32, SizedTree, SizedTree, SizedTree, SizedTree, SizedTree, SizedTree),
}

function sized_mirrored_context_uncle_pending(phase: SizedInsertMirroredContextUnclePhase) -> int32 {
    match phase {
        SizedInsertMirroredContextUnclePhase::Before(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right) => 1,
        SizedInsertMirroredContextUnclePhase::After(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right) => 0,
    }
}

function sized_mirrored_context_uncle_finish(phase: SizedInsertMirroredContextUnclePhase) -> SizedInsertMirroredContextUnclePhase {
    match phase {
        SizedInsertMirroredContextUnclePhase::Before(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right) => SizedInsertMirroredContextUnclePhase::After(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right),
        SizedInsertMirroredContextUnclePhase::After(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right) => SizedInsertMirroredContextUnclePhase::After(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right),
    }
}

function sized_mirrored_context_uncle_expected(phase: SizedInsertMirroredContextUnclePhase, node: struct rb_node*) -> RbTree {
    match phase {
        SizedInsertMirroredContextUnclePhase::Before(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right) => sized_mirrored_context_uncle_after(g, p, m, u, node, above, left, right, middle_left, middle_right, uncle_left, uncle_right),
        SizedInsertMirroredContextUnclePhase::After(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right) => sized_mirrored_context_uncle_after(g, p, m, u, node, above, left, right, middle_left, middle_right, uncle_left, uncle_right),
    }
}


resource sized_insert_mirrored_context_uncle_at(node: struct rb_node*, root: struct rb_root*) {
    field phase: SizedInsertMirroredContextUnclePhase;
    field model: SizedTree;
    field context: SizedContext;
    field whole_model: SizedTree;
    match phase {
        SizedInsertMirroredContextUnclePhase::Before(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right) => {
            owns link: sized_link_at(g, root, gv);
            owns tree: sized_at(g);
            fact link.model == context;
            fact above == sized_context_parent(context, 0);
            fact tree.model == model;
            fact model == sized_mirrored_context_uncle_before(g, p, m, u, node, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right);
        },
        SizedInsertMirroredContextUnclePhase::After(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right) => {
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
    owns state: sized_insert_mirrored_context_uncle_at(node, root);
    requires sized_mirrored_context_uncle_pending(state.phase) == 1;
    ensures state.context == old(state.context);
    ensures state.whole_model == sized_plug(old(state.context), state.model);
    ensures state.phase == sized_mirrored_context_uncle_finish(old(state.phase));
    ensures sized_shape(state.model) == sized_mirrored_context_uncle_expected(old(state.phase), node);
} by {
    match state.phase {
        SizedInsertMirroredContextUnclePhase::After(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right) => {
            have sized_mirrored_context_uncle_pending(state.phase) != 1 by {
                rewrite(state.phase == SizedInsertMirroredContextUnclePhase::After(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right));
                unfold(sized_mirrored_context_uncle_pending(SizedInsertMirroredContextUnclePhase::After(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right))); normalize();
            }
            contradiction(sized_mirrored_context_uncle_pending(state.phase) == 1);
        },
        SizedInsertMirroredContextUnclePhase::Before(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right) => {
            let { tree: tree, link: link } = unfold(state);
            unfold(sized_mirrored_context_uncle_before(g, p, m, u, node, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right));
            have tree.model == SizedTree::Node(g, above, Color::Black, gv, SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right), SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), SizedTree::Node(node, p, Color::Red, nv, left, right))) by {
                rewrite(tree.model == sized_mirrored_context_uncle_before(g, p, m, u, node, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right));
                unfold(sized_mirrored_context_uncle_before(g, p, m, u, node, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right)); normalize();
            }
            let { metadata: g_size, right: parent_tree, left: g_left } = unfold(tree);
            let { metadata: p_size, right: focus, left: p_left } = unfold(parent_tree);
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
            have p->rb_right == node by { assumption(); }
            have p->rb_right != p by {
                assumption();
            }
            have p->rb_left != p by {
                assumption();
            }
            let parent_tree = fold(sized_at(p), { model: SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), SizedTree::Node(node, p, Color::Red, nv, left, right)) }, { metadata: p_size, right: focus, left: p_left });
            let tree = fold(sized_at(g), { model: old(state.model) }, { metadata: g_size, right: parent_tree, left: g_left });
            let state = fold(sized_insert_mirrored_context_uncle_at(node, root), { phase: SizedInsertMirroredContextUnclePhase::Before(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right), model: old(state.model), context: old(state.context), whole_model: old(state.whole_model) }, { tree: tree, link: link });
            loop {
                owns state: sized_insert_mirrored_context_uncle_at(node, root);
                decreases 0;
                invariant node == old(node);
                invariant parent == p;
                invariant state.context == old(state.context);
                invariant p == old(g->rb_right);
                invariant state.phase == SizedInsertMirroredContextUnclePhase::Before(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right);
                invariant old(state.phase) == SizedInsertMirroredContextUnclePhase::Before(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right);
                invariant state.model == sized_mirrored_context_uncle_before(g, p, m, u, node, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right);
                initialize by simp();
                preserve by {
                    let { tree: loop_tree, link: link } = unfold(state);
                    unfold(sized_mirrored_context_uncle_before(g, p, m, u, node, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right));
                    have loop_tree.model == SizedTree::Node(g, above, Color::Black, gv, SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right), SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), SizedTree::Node(node, p, Color::Red, nv, left, right))) by {
                        rewrite(loop_tree.model == sized_mirrored_context_uncle_before(g, p, m, u, node, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right));
                        unfold(sized_mirrored_context_uncle_before(g, p, m, u, node, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right)); normalize();
                    }
                    let { metadata: g_size, right: parent_tree, left: g_left } = unfold(loop_tree);
                    let { metadata: p_size, right: focus, left: p_left } = unfold(parent_tree);
                    let { metadata: u_size, left: u_left, right: u_right } = unfold(g_left);
                    have g->rb_left == u by { assumption(); }
                    have separate(memory(p->__rb_parent_color), memory(u->__rb_parent_color)) by { assumption(); }
                    have p != u by { assumption(); }
                    unfold(color_bit(Color::Black));
                    have (u->__rb_parent_color & 1) == 1 by {
                        rewrite((u->__rb_parent_color & 1) == color_bit(Color::Black));
                        rewrite(color_bit(Color::Black) == 1); normalize();
                    }
                    let { metadata: m_size, left: m_left, right: m_right } = unfold(p_left);
                    have p->rb_left == m by { assumption(); }
                    let { metadata: n_size, left: n_left, right: n_right } = unfold(focus);
                    have separate(memory(node->__rb_parent_color), memory(m->__rb_parent_color)) by { assumption(); }
                    have m != node by { assumption(); }
                    have separate(memory(m->__rb_parent_color), memory(g->__rb_parent_color)) by { assumption(); }
                    have m != g by { assumption(); }
                    let p_left = fold(sized_at(p->rb_left), { model: SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right) }, { metadata: m_size, left: m_left, right: m_right });
                    let focus = fold(sized_at(node), { model: SizedTree::Node(node, p, Color::Red, nv, left, right) }, { metadata: n_size, left: n_left, right: n_right });
                    let { checked: focus } = certify_size(node, { tree: focus });
                    let { checked: p_left } = certify_size(p->rb_left, { tree: p_left });
                    let g_left = fold(sized_at(g->rb_left), { model: SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right) }, { metadata: u_size, left: u_left, right: u_right });
                    let { checked: g_left } = certify_size(g->rb_left, { tree: g_left });
                    unfold(sized_value(SizedTree::Node(node, p, Color::Red, nv, left, right)));
                    unfold(sized_value(SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), SizedTree::Node(node, p, Color::Red, nv, left, right))));
                    unfold(sized_value(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)));
                    have to_integer(sized_value(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))) == to_integer(uv) by {
                        rewrite(sized_value(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)) == uv); simp();
                    }
                    unfold(sized_value(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)));
                    have to_integer(sized_value(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))) == to_integer(mv) by {
                        rewrite(sized_value(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)) == mv); normalize();
                    }
                    have to_integer(gv) == 2 + to_integer(nv) + to_integer(mv) + to_integer(uv) by {
                        arithmetic() using {
                            to_integer(gv) == 1 + to_integer(sized_value(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))) + to_integer(pv);
                            to_integer(pv) == 1 + to_integer(sized_value(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))) + to_integer(nv);
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
                    have 0 <= to_integer(nv) by { arithmetic() using {
                        rb_subtree_size(sized_shape(SizedTree::Node(node, p, Color::Red, nv, left, right))) == to_integer(nv);
                        rb_subtree_size(sized_shape(SizedTree::Node(node, p, Color::Red, nv, left, right))) >= 0;
                    }; }
                    have 0 <= to_integer(mv) by { arithmetic() using {
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
                    have 0 <= to_integer(uv) by { arithmetic() using {
                        rb_subtree_size(sized_shape(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))) == to_integer(uv);
                        rb_subtree_size(sized_shape(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))) >= 0;
                    }; }
                    apply(click::integer::int32_to_integer_bounds(gv));
                    have 1 + to_integer(mv) + to_integer(uv) <= 2147483647 by { arithmetic() using {
                        to_integer(gv) == 2 + to_integer(nv) + to_integer(mv) + to_integer(uv);
                        to_integer(nv) >= 0;
                        to_integer(gv) <= 2147483647;
                    }; }
                    apply(size_children_fit(mv, uv));
                    apply(size_children_fit(uv, mv));
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
                    let { metadata: u_size, left: u_left, right: u_right } = unfold(g_left);
                    step(); step(); step(); step(); step(); step(); step(); step();
                    let g_left = fold(sized_at(g->rb_left), { model: SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right) }, { metadata: u_size, left: u_left, right: u_right });
                    have gparent == g by { assumption(); }
                    have parent == p by { assumption(); }
                    have parent->rb_right == node by { assumption(); }
                    mark before_link_writes;
                    have at(before_link_writes, parent->rb_right == node) by { assumption(); }
                    have at(before_link_writes, g->rb_right) == parent by { assumption(); }
                    step(); step(); step();
                    have tmp == m by { assumption(); }
                    have tmp != 0 by { assumption(); }
                    have tmp != node by { assumption(); }
                    have node != 0 by { assumption(); }
                    step(); step(); step();
                    mark after_right_write;
                    have at(after_right_write, g->rb_right == m) by { assumption(); }
                    have separate(memory(g->rb_right), memory(parent->rb_left)) by { assumption(); }
                    step(); step();
                    let { after: p_left } = step(insert::rb_set_parent_color(tmp, gparent, 1), { tree: p_left });
                    unfold(sized_reparent(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), g));
                    unfold(sized_recolor(SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), Color::Black));
                    have p_left.model == SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right) by { assumption(); }
                    have gparent->__rb_parent_color == address(above) + 1 by { simp(); }
                    unfold(g_size);
                    have sized_context_parent_word(link.model, g->__rb_parent_color) == 1 by {
                        apply(sized_context_parent_word_black(link.model, above, g->__rb_parent_color));
                    }
                    have g->rb_right == m by {
                        transport(at(after_right_write, g->rb_right == m), g->rb_right == m) using {
                            at(after_right_write, g->rb_right == m);
                            separate(memory(g->rb_right), memory(parent->rb_left));
                            at(before_link_writes, g->rb_right) == parent;
                        };
                    }
                    transport(at(before_link_writes, parent->rb_right == node), parent->rb_right == node);
                    have parent->rb_left == gparent by { simp(); }
                    mark before_parent_update;
                    have at(before_parent_update, g->rb_right == m) by { assumption(); }
                    have at(before_parent_update, parent->rb_right == node) by { assumption(); }
                    have at(before_parent_update, parent->rb_left == gparent) by { assumption(); }
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
                    transport(at(before_parent_update, g->rb_right == m), g->rb_right == m);
                    have g->rb_left == u by { simp(); }

                    unfold(sized_parent_is(SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), g));
                    let demoted = fold(sized_recompute_at(g), {
                        model: SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right), SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right))
                    }, { metadata: g_size, right: p_left, left: g_left });
                    transport(at(before_parent_update, parent->rb_right == node), parent->rb_right == node) using {
                        at(before_parent_update, parent->rb_right == node);
                        parent == p;
                        at(before_link_writes, g->rb_right) == parent;
                    };
                    transport(at(before_parent_update, parent->rb_left == gparent), parent->rb_left == gparent) using {
                        at(before_parent_update, parent->rb_left == gparent);
                        parent == p;
                        at(before_link_writes, g->rb_right) == parent;
                    };
                    have p->rb_left == g by { assumption(); }
                    have parent == p by { assumption(); }
                    have sized_parent_is(SizedTree::Node(node, p, Color::Red, nv, left, right), p) == 1 by {
                        unfold(sized_parent_is(SizedTree::Node(node, p, Color::Red, nv, left, right), p)); normalize();
                    }
                    have sized_parent_is(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right), SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right)), p) == 1 by {
                        unfold(sized_parent_is(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right), SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right)), p)); normalize();
                    }
                    have to_integer(sized_value(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right), SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right)))) == 2 + to_integer(sized_value(sized_left(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right), SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right))))) + to_integer(sized_value(sized_right(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right), SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right))))) + to_integer(sized_value(SizedTree::Node(node, p, Color::Red, nv, left, right))) by {
                        unfold(sized_value(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right), SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right))));
                        unfold(sized_right(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right), SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right))));
                        unfold(sized_left(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right), SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right))));
                        unfold(sized_value(SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right)));
                        unfold(sized_value(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)));
                        unfold(sized_value(SizedTree::Node(node, p, Color::Red, nv, left, right)));
                        arithmetic() using { to_integer(gv) == 2 + to_integer(nv) + to_integer(mv) + to_integer(uv); };
                    }
                    let rotated = fold(sized_rotation_left_at(g, p), {
                        model: SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right), SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right)), SizedTree::Node(node, p, Color::Red, nv, left, right))
                    }, { metadata: p_size, other: focus, demoted: demoted });
                    unfold(sized_left(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right), SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right)), SizedTree::Node(node, p, Color::Red, nv, left, right))));
                    unfold(sized_right(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right), SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right))));
                    unfold(sized_left(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right), SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right))));
                    unfold(sized_value(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)));
                    unfold(sized_value(SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right)));
                    have 0 <= sized_value(sized_left(sized_left(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right), SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right)), SizedTree::Node(node, p, Color::Red, nv, left, right))))) by {
                        rewrite(sized_left(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right), SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right)), SizedTree::Node(node, p, Color::Red, nv, left, right))) == SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right), SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right)));
                        rewrite(sized_left(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right), SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right))) == SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right));
                        rewrite(sized_value(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)) == uv);
                        assumption();
                    }
                    have 0 <= sized_value(sized_right(sized_left(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right), SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right)), SizedTree::Node(node, p, Color::Red, nv, left, right))))) by {
                        rewrite(sized_left(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right), SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right)), SizedTree::Node(node, p, Color::Red, nv, left, right))) == SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right), SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right)));
                        rewrite(sized_right(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right), SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right))) == SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right));
                        rewrite(sized_value(SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right)) == mv);
                        assumption();
                    }
                    have sized_value(sized_right(sized_left(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right), SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right)), SizedTree::Node(node, p, Color::Red, nv, left, right))))) <= 2147483646 by {
                        rewrite(sized_left(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right), SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right)), SizedTree::Node(node, p, Color::Red, nv, left, right))) == SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right), SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right)));
                        rewrite(sized_right(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right), SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right))) == SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right));
                        rewrite(sized_value(SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right)) == mv);
                        assumption();
                    }
                    have sized_value(sized_left(sized_left(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right), SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right)), SizedTree::Node(node, p, Color::Red, nv, left, right))))) <= 2147483646 - sized_value(sized_right(sized_left(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right), SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right)), SizedTree::Node(node, p, Color::Red, nv, left, right))))) by {
                        rewrite(sized_left(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right), SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right)), SizedTree::Node(node, p, Color::Red, nv, left, right))) == SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right), SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right)));
                        rewrite(sized_left(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right), SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right))) == SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right));
                        rewrite(sized_right(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right), SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right))) == SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right));
                        rewrite(sized_value(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)) == uv);
                        rewrite(sized_value(SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right)) == mv);
                        assumption();
                    }
                    let { checked: checked } = step(RotateTreeLeft, { tree: rotated });
                    have sized_shape(checked.model) == sized_mirrored_context_uncle_after(g, p, m, u, node, above, left, right, middle_left, middle_right, uncle_left, uncle_right) by {
                        rewrite(sized_shape(checked.model) == sized_shape(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right), SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right)), SizedTree::Node(node, p, Color::Red, nv, left, right))));
                        unfold(sized_shape(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right), SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right)), SizedTree::Node(node, p, Color::Red, nv, left, right))));
                        unfold(sized_shape(SizedTree::Node(node, p, Color::Red, nv, left, right)));
                        unfold(sized_shape(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right), SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right))));
                        unfold(sized_shape(SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right)));
                        unfold(sized_shape(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)));
                        unfold(sized_mirrored_context_uncle_after(g, p, m, u, node, above, left, right, middle_left, middle_right, uncle_left, uncle_right)); normalize();
                    }
                    have rb_subtree_size(sized_mirrored_context_uncle_after(g, p, m, u, node, above, left, right, middle_left, middle_right, uncle_left, uncle_right)) == to_integer(gv) by {
                        unfold(sized_mirrored_context_uncle_after(g, p, m, u, node, above, left, right, middle_left, middle_right, uncle_left, uncle_right));
                        unfold(rb_subtree_size(RbTree::Node(p, above, Color::Black, RbTree::Node(g, p, Color::Red, RbTree::Node(u, g, Color::Black, sized_shape(uncle_left), sized_shape(uncle_right)), RbTree::Node(m, g, Color::Black, sized_shape(middle_left), sized_shape(middle_right))), RbTree::Node(node, p, Color::Red, sized_shape(left), sized_shape(right)))));
                        unfold(rb_subtree_size(RbTree::Node(node, p, Color::Red, sized_shape(left), sized_shape(right))));
                        unfold(rb_subtree_size(RbTree::Node(g, p, Color::Red, RbTree::Node(u, g, Color::Black, sized_shape(uncle_left), sized_shape(uncle_right)), RbTree::Node(m, g, Color::Black, sized_shape(middle_left), sized_shape(middle_right)))));
                        unfold(rb_subtree_size(RbTree::Node(m, g, Color::Black, sized_shape(middle_left), sized_shape(middle_right))));
                        unfold(rb_subtree_size(RbTree::Node(u, g, Color::Black, sized_shape(uncle_left), sized_shape(uncle_right))));
                        unfold(sized_shape(SizedTree::Node(node, p, Color::Red, nv, left, right)));
                        arithmetic() using {
                            to_integer(gv) == 2 + to_integer(nv) + to_integer(mv) + to_integer(uv);
                            rb_subtree_size(sized_shape(left)) + rb_subtree_size(sized_shape(right)) + 1 == to_integer(nv);
                            rb_subtree_size(sized_shape(middle_left)) + rb_subtree_size(sized_shape(middle_right)) + 1 == to_integer(mv);
                            rb_subtree_size(sized_shape(uncle_left)) + rb_subtree_size(sized_shape(uncle_right)) + 1 == to_integer(uv);
                        };
                    }
                    have to_integer(sized_value(checked.model)) == to_integer(gv) by {
                        rewrite(to_integer(sized_value(checked.model)) == rb_subtree_size(sized_shape(checked.model)));
                        rewrite(sized_shape(checked.model) == sized_mirrored_context_uncle_after(g, p, m, u, node, above, left, right, middle_left, middle_right, uncle_left, uncle_right));
                        assumption();
                    }
                    have sized_value(checked.model) == gv by {
                        apply(click::integer::int32_to_integer_equal_implies_equal(sized_value(checked.model), gv));
                    }
                    apply(sized_parent_is_shape(checked.model, above));
                    have rb_parent_is(sized_shape(checked.model), above) == 1 by {
                        rewrite(sized_shape(checked.model) == sized_mirrored_context_uncle_after(g, p, m, u, node, above, left, right, middle_left, middle_right, uncle_left, uncle_right));
                        unfold(sized_mirrored_context_uncle_after(g, p, m, u, node, above, left, right, middle_left, middle_right, uncle_left, uncle_right));
                        unfold(rb_parent_is(RbTree::Node(p, above, Color::Black, RbTree::Node(g, p, Color::Red, RbTree::Node(u, g, Color::Black, sized_shape(uncle_left), sized_shape(uncle_right)), RbTree::Node(m, g, Color::Black, sized_shape(middle_left), sized_shape(middle_right))), RbTree::Node(node, p, Color::Red, sized_shape(left), sized_shape(right))), above)); normalize();
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
                    let state = fold(sized_insert_mirrored_context_uncle_at(node, root), {
                        phase: SizedInsertMirroredContextUnclePhase::After(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right), model: at(before_restore, checked.model), context: old(state.context), whole_model: whole.model
                    }, { whole: whole });
                    have state.context == old(state.context) by { assumption(); }
                    have state.whole_model == sized_plug(old(state.context), state.model) by { assumption(); }
                    have state.phase == sized_mirrored_context_uncle_finish(old(state.phase)) by {
                        unfold(sized_mirrored_context_uncle_finish(SizedInsertMirroredContextUnclePhase::Before(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right))); simp();
                    }
                    have sized_shape(state.model) == sized_mirrored_context_uncle_expected(old(state.phase), node) by {
                        rewrite(old(state.phase) == SizedInsertMirroredContextUnclePhase::Before(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right));
                        unfold(sized_mirrored_context_uncle_expected(SizedInsertMirroredContextUnclePhase::Before(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right), node)); simp();
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
    owns state: sized_insert_mirrored_context_uncle_at(node, root);
    requires sized_mirrored_context_uncle_pending(state.phase) == 1;
    ensures state.context == old(state.context);
    ensures state.whole_model == sized_plug(old(state.context), state.model);
    ensures state.phase == sized_mirrored_context_uncle_finish(old(state.phase));
    ensures sized_shape(state.model) == sized_mirrored_context_uncle_expected(old(state.phase), node);
} by {
    step(insert::__rb_insert(node, root, augment_rotate), { state: state });
    execute(); simp();
}

void insert::rb_insert_augmented(struct rb_node* node, struct rb_root* root,
                         const struct rb_augment_callbacks* augment) {
    views augment->rotate;
    requires RotateTreeLeft(augment->rotate);
    owns state: sized_insert_mirrored_context_uncle_at(node, root);
    requires sized_mirrored_context_uncle_pending(state.phase) == 1;
    ensures state.context == old(state.context);
    ensures state.whole_model == sized_plug(old(state.context), state.model);
    ensures state.phase == sized_mirrored_context_uncle_finish(old(state.phase));
    ensures sized_shape(state.model) == sized_mirrored_context_uncle_expected(old(state.phase), node);
} by {
    step(insert::__rb_insert_augmented(node, root, augment->rotate), { state: state });
    execute(); simp();
}
