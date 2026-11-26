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

// Retain complete node observations through read-only C steps.
resource context_uncle_node_frame(p: struct rb_node*, up: struct rb_node*) {
    field color: Color;
    field word: uint64;
    field left: int32*;
    field right: int32*;
    owns p->__rb_parent_color;
    fact p->__rb_parent_color == word;
    fact p->__rb_parent_color == address(up) + (p->__rb_parent_color & 1);
    fact ((p->__rb_parent_color & ~3) as (struct rb_node*)) == up;
    fact (p->__rb_parent_color & 1) == color_bit(color);
    owns p->rb_left;
    owns p->rb_right;
    fact p->rb_left == left;
    fact p->rb_right == right;
    fact p->rb_left != p;
    fact p->rb_right != p;
}

resource context_uncle_tag(p: struct rb_node*, up: struct rb_node*) {
    field color: Color;
    field word: uint64;
    owns p->__rb_parent_color;
    fact p->__rb_parent_color == word;
    fact p->__rb_parent_color == address(up) + (p->__rb_parent_color & 1);
    fact ((p->__rb_parent_color & ~3) as (struct rb_node*)) == up;
    fact (p->__rb_parent_color & 1) == color_bit(color);
}

resource context_uncle_link(slot: struct rb_node**) {
    field child: int32*;
    owns *slot;
    fact *slot == child;
}

void insert::__rb_insert(struct rb_node* node, struct rb_root* root,
                  void (*augment_rotate)(struct rb_node*, struct rb_node*)) {
    requires RotateTreeRight(augment_rotate);
    owns state: sized_insert_context_uncle_at(node, root);
    requires sized_context_uncle_pending(state.phase) == 1;
    requires node->rb_left != node;
    requires node->rb_right != node;
    ensures state.context == old(state.context);
    ensures state.whole_model == sized_plug(old(state.context), state.model);
    ensures state.phase == sized_context_uncle_finish(old(state.phase));
    ensures sized_shape(state.model) == sized_context_uncle_expected(old(state.phase), node);
} by {
    match state.phase {
        SizedInsertContextUnclePhase::After(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right) => {
            have sized_context_uncle_pending(state.phase) != 1 by {
                rewrite(state.phase, SizedInsertContextUnclePhase::After(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right));
                unfold(sized_context_uncle_pending(SizedInsertContextUnclePhase::After(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right))); close();
            }
            close();
        },
        SizedInsertContextUnclePhase::Before(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right) => {
            let { tree: tree, link: link } = unfold(state);
            unfold(sized_context_uncle_before(g, p, m, u, node, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right));
            have tree.model == SizedTree::Node(g, above, Color::Black, gv,
                SizedTree::Node(p, g, Color::Red, pv,
                    SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)) by {
                rewrite(tree.model, sized_context_uncle_before(g, p, m, u, node, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right));
                unfold(sized_context_uncle_before(g, p, m, u, node, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right)); close();
            }
            let { metadata: g_size, left: parent_tree, right: g_right } = unfold(tree);
            let { metadata: p_size, left: focus, right: p_right } = unfold(parent_tree);
            let { metadata: n_size, left: n_left, right: n_right } = unfold(focus);
            unfold(color_bit(Color::Red));
            have (node->__rb_parent_color & 1) == 0 by {
                rewrite((node->__rb_parent_color & 1), color_bit(Color::Red));
                rewrite(color_bit(Color::Red), 0); close();
            }
            have node->__rb_parent_color == address(p) by {
                rewrite(node->__rb_parent_color, address(p) + (node->__rb_parent_color & 1));
                rewrite((node->__rb_parent_color & 1), 0); close();
            }
            have node->rb_left != node by close();
            have node->rb_right != node by close();
            let initial_focus = fold(context_uncle_node_frame(node, p), { color: Color::Red, word: node->__rb_parent_color, left: node->rb_left, right: node->rb_right });
            have p == g->rb_left by close();
            have p->__rb_parent_color == address(g) + (p->__rb_parent_color & 1) by {
                rewrite(p, g->rb_left);
                close();
            }
            have ((p->__rb_parent_color & ~3) as (struct rb_node *)) == g by {
                rewrite(p, g->rb_left);
                close();
            }
            have (p->__rb_parent_color & 1) == color_bit(Color::Red) by {
                rewrite(p, g->rb_left);
                close();
            }
            let initial_parent = fold(context_uncle_node_frame(p, g), { color: Color::Red, word: p->__rb_parent_color, left: p->rb_left, right: p->rb_right });
            let initial_grandparent = fold(context_uncle_node_frame(g, above), { color: Color::Black, word: g->__rb_parent_color, left: g->rb_left, right: g->rb_right });
            step(); step(); step(); step();
            unfold(initial_grandparent); unfold(initial_parent); unfold(initial_focus);
            let focus = fold(sized_at(node), { model: SizedTree::Node(node, p, Color::Red, nv, left, right), metadata: n_size, left: n_left, right: n_right });
            have p->rb_left == node by { close(); }
            have p->rb_left != p by {
                close();
            }
            have p->rb_right != p by {
                close();
            }
            let parent_tree = fold(sized_at(p), { model: SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)), metadata: p_size, left: focus, right: p_right });
            have ((g->__rb_parent_color & ~3) as (struct rb_node*)) == above by close();
            let tree = fold(sized_at(g), { model: SizedTree::Node(g, above, Color::Black, gv, SizedTree::Node(p, g, Color::Red, pv,     SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)), metadata: g_size, left: parent_tree, right: g_right });
            have tree.model == old(state.model) by close();
            let state = fold(sized_insert_context_uncle_at(node, root), { phase: SizedInsertContextUnclePhase::Before(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right), model: old(state.model), context: old(state.context), whole_model: old(state.whole_model), tree: tree, link: link });
            step(); // Declare tmp before the C loop.
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
                initialize by close();
                maintain by {
                    let { tree: loop_tree, link: link } = unfold(state);
                    unfold(sized_context_uncle_before(g, p, m, u, node, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right));
                    have loop_tree.model == SizedTree::Node(g, above, Color::Black, gv,
                        SizedTree::Node(p, g, Color::Red, pv,
                            SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)) by {
                        rewrite(loop_tree.model, sized_context_uncle_before(g, p, m, u, node, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right));
                        unfold(sized_context_uncle_before(g, p, m, u, node, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right)); close();
                    }
                    let { metadata: g_size, left: parent_tree, right: g_right } = unfold(loop_tree);
                    let { metadata: p_size, left: focus, right: p_right } = unfold(parent_tree);
                    let { metadata: u_size, left: u_left, right: u_right } = unfold(g_right);
                    have g->rb_right == u by { close(); }
                    have separate(memory(p->__rb_parent_color), memory(u->__rb_parent_color)) by { close(); }
                    have p != u by { close(); }
                    unfold(color_bit(Color::Black));
                    have (u->__rb_parent_color & 1) == 1 by {
                        rewrite((u->__rb_parent_color & 1), color_bit(Color::Black));
                        rewrite(color_bit(Color::Black), 1); close();
                    }
                    let { metadata: m_size, left: m_left, right: m_right } = unfold(p_right);
                    have p->rb_right == m by { close(); }
                    let { metadata: n_size, left: n_left, right: n_right } = unfold(focus);
                    have separate(memory(node->__rb_parent_color), memory(m->__rb_parent_color)) by { close(); }
                    have m != node by { close(); }
                    have separate(memory(m->__rb_parent_color), memory(g->__rb_parent_color)) by { close(); }
                    have m != g by { close(); }
                    let p_right = fold(sized_at(m), { model: SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), metadata: m_size, left: m_left, right: m_right });
                    let focus = fold(sized_at(node), { model: SizedTree::Node(node, p, Color::Red, nv, left, right), metadata: n_size, left: n_left, right: n_right });
                    let { checked: focus } = certify_size(node, { tree: focus });
                    let { checked: p_right } = certify_size(m, { tree: p_right });
                    let g_right = fold(sized_at(u), { model: SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right), metadata: u_size, left: u_left, right: u_right });
                    let { checked: g_right } = certify_size(u, { tree: g_right });
                    unfold(sized_value(SizedTree::Node(node, p, Color::Red, nv, left, right)));
                    unfold(sized_value(SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))));
                    unfold(sized_value(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)));
                    have to_integer(sized_value(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))) == to_integer(uv) by {
                        rewrite(sized_value(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)), uv); close();
                    }
                    unfold(sized_value(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)));
                    have to_integer(sized_value(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))) == to_integer(mv) by {
                        rewrite(sized_value(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)), mv); close();
                    }
                    have to_integer(gv) == 2 + to_integer(nv) + to_integer(mv) + to_integer(uv) by {
                        close() using {
                            to_integer(gv) == 1 + to_integer(pv) + to_integer(sized_value(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)));
                            to_integer(pv) == 1 + to_integer(nv) + to_integer(sized_value(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)));
                            to_integer(sized_value(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))) == to_integer(mv);
                            to_integer(sized_value(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))) == to_integer(uv);
                        };
                    }
                    have rb_subtree_size(sized_shape(SizedTree::Node(node, p, Color::Red, nv, left, right))) == to_integer(nv) by close();
                    have rb_subtree_size(sized_shape(left)) + rb_subtree_size(sized_shape(right)) + 1 == to_integer(nv) by {
                        rewrite(to_integer(nv), rb_subtree_size(sized_shape(SizedTree::Node(node, p, Color::Red, nv, left, right))));
                        unfold(sized_shape(SizedTree::Node(node, p, Color::Red, nv, left, right)));
                        unfold(rb_subtree_size(RbTree::Node(node, p, Color::Red, sized_shape(left), sized_shape(right))));
                        close();
                    }
                    have rb_subtree_size(sized_shape(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))) == to_integer(mv) by { close(); }
                    have rb_subtree_size(sized_shape(middle_left)) + rb_subtree_size(sized_shape(middle_right)) + 1 == to_integer(mv) by {
                        rewrite(to_integer(mv), rb_subtree_size(sized_shape(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))));
                        unfold(sized_shape(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)));
                        unfold(rb_subtree_size(RbTree::Node(m, p, Color::Black, sized_shape(middle_left), sized_shape(middle_right)))); close();
                    }
                    apply(rb_subtree_size_nonnegative(sized_shape(SizedTree::Node(node, p, Color::Red, nv, left, right))));
                    apply(rb_subtree_size_nonnegative(sized_shape(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))));
                    have 0 <= to_integer(nv) by { close() using {
                        rb_subtree_size(sized_shape(SizedTree::Node(node, p, Color::Red, nv, left, right))) == to_integer(nv);
                        rb_subtree_size(sized_shape(SizedTree::Node(node, p, Color::Red, nv, left, right))) >= 0;
                    }; }
                    have 0 <= to_integer(mv) by { close() using {
                        rb_subtree_size(sized_shape(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))) == to_integer(mv);
                        rb_subtree_size(sized_shape(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))) >= 0;
                    }; }
                    have rb_subtree_size(sized_shape(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))) == to_integer(uv) by { close(); }
                    have rb_subtree_size(sized_shape(uncle_left)) + rb_subtree_size(sized_shape(uncle_right)) + 1 == to_integer(uv) by {
                        rewrite(to_integer(uv), rb_subtree_size(sized_shape(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))));
                        unfold(sized_shape(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)));
                        unfold(rb_subtree_size(RbTree::Node(u, g, Color::Black, sized_shape(uncle_left), sized_shape(uncle_right)))); close();
                    }
                    apply(rb_subtree_size_nonnegative(sized_shape(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))));
                    have 0 <= to_integer(uv) by { close() using {
                        rb_subtree_size(sized_shape(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))) == to_integer(uv);
                        rb_subtree_size(sized_shape(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))) >= 0;
                    }; }
                    have -2147483648 <= to_integer(gv);
                    have to_integer(gv) <= 2147483647;
                    have 1 + to_integer(mv) + to_integer(uv) <= 2147483647 by { close() using {
                        to_integer(gv) == 2 + to_integer(nv) + to_integer(mv) + to_integer(uv);
                        to_integer(nv) >= 0;
                        to_integer(gv) <= 2147483647;
                    }; }
                    apply(size_children_fit(mv, uv));
                    unfold(color_bit(Color::Red)); unfold(color_bit(Color::Black));
                    have p->__rb_parent_color == address(g) by {
                        rewrite(p->__rb_parent_color, address(g) + (p->__rb_parent_color & 1));
                        rewrite((p->__rb_parent_color & 1), color_bit(Color::Red));
                        rewrite(color_bit(Color::Red), 0); close();
                    }
                    have g->__rb_parent_color == address(above) + 1 by {
                        rewrite(g->__rb_parent_color, address(above) + (g->__rb_parent_color & 1));
                        rewrite((g->__rb_parent_color & 1), color_bit(Color::Black));
                        rewrite(color_bit(Color::Black), 1); close();
                    }
                    let loop_parent = fold(context_uncle_node_frame(p, g), { color: Color::Red, word: p->__rb_parent_color, left: node, right: m });
                    let loop_grandparent = fold(context_uncle_node_frame(g, above), { color: Color::Black, word: g->__rb_parent_color, left: p, right: u });
                    let { metadata: u_size, left: u_left, right: u_right } = unfold(g_right);
                    let loop_uncle = fold(context_uncle_node_frame(u, g), { color: Color::Black, word: u->__rb_parent_color, left: u->rb_left, right: u->rb_right });
                    step(); step(); step(); step(); step(); step(); step();
                    unfold(loop_grandparent); unfold(loop_parent);
                    have gparent == g by close();
                    have parent == p by close();
                    have p->rb_left == node by close();
                    have parent->rb_left == node by { rewrite(parent, p); close(); }
                    have p->rb_right == m by close();
                    have parent->rb_right == m by { rewrite(parent, p); close(); }
                    have g->rb_right == u by close();
                    let rotating_tag = fold(context_uncle_tag(g, above), { color: Color::Black, word: g->__rb_parent_color });
                    let kept_g_right = fold(context_uncle_link(&g->rb_right), { child: u });
                    let kept_p_left = fold(context_uncle_link(&p->rb_left), { child: node });
                    unfold(loop_uncle);
                    unfold(color_bit(Color::Black));
                    have (u->__rb_parent_color & 1) == 1 by {
                        rewrite((u->__rb_parent_color & 1), color_bit(Color::Black));
                        rewrite(color_bit(Color::Black), 1); close();
                    }
                    let uncle_observation = fold(context_uncle_node_frame(u, g), { color: Color::Black, word: u->__rb_parent_color, left: u->rb_left, right: u->rb_right });
                    step(); step(); step(); // Read the black uncle and skip the color flip.
                    unfold(uncle_observation);
                    let g_right = fold(sized_at(u), { model: SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right), metadata: u_size, left: u_left, right: u_right });
                    step(); step(); step(); // Load the nonempty middle child and skip the inner rotation.
                    have tmp == m by close();
                    have tmp != 0 by close();
                    have tmp != node by { rewrite(tmp, m); close(); }
                    step(); // Transfer the middle child to the grandparent.
                    have g->rb_left == m by close();
                    let kept_g_left = fold(context_uncle_link(&g->rb_left), { child: m });
                    step(); // Put the old grandparent under the promoted parent.
                    have p->rb_right == g by close();
                    let kept_p_right = fold(context_uncle_link(&p->rb_right), { child: g });
                    step(); // Enter the nonnull middle-child branch.
                    let { after: p_right } = step(insert::rb_set_parent_color, { tree: p_right });
                    unfold(sized_reparent(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), g));
                    unfold(sized_recolor(SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), Color::Black));
                    have p_right.model == SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right) by close();
                    unfold(rotating_tag);
                    have g->__rb_parent_color == address(above) + 1 by close();
                    unfold(g_size);
                    have sized_context_parent_word(link.model, g->__rb_parent_color) == 1 by {
                        apply(sized_context_parent_word_black(link.model, above, g->__rb_parent_color));
                    }
                    mark before_parent_update;
                    have ((g->__rb_parent_color & ~3) as (struct rb_node*)) == above by close();
                    have ((g->__rb_parent_color & ~3) as (struct rb_node*)) == sized_context_parent(link.model, 0) by {
                        rewrite(sized_context_parent(link.model, 0), above); close();
                    }
                    let { after: link } = step(insert::__rb_rotate_set_parents, { c: link });
                    have p->__rb_parent_color == at(before_parent_update, g->__rb_parent_color) by { close(); }
                    have p->__rb_parent_color == address(above) + (p->__rb_parent_color & 1) by {
                        rewrite(p->__rb_parent_color, at(before_parent_update, g->__rb_parent_color)); close();
                    }
                    have (p->__rb_parent_color & 1) == color_bit(Color::Black) by {
                        rewrite(p->__rb_parent_color, at(before_parent_update, g->__rb_parent_color)); close();
                    }
                    let g_size = fold(size_metadata(g), { value: gv });
                    unfold(kept_g_left); unfold(kept_g_right);
                    unfold(kept_p_left); unfold(kept_p_right);
                    have g->rb_left == m by close();
                    have g->rb_right == u by close();
                    unfold(sized_parent_is(SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), g));
                    let demoted = fold(sized_recompute_at(g), {
                        model: SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)),
                        metadata: g_size, left: p_right, right: g_right
                    });
                    have p->rb_left == node by close();
                    have p->rb_right == g by close();
                    have parent == p by close();
                    have sized_parent_is(SizedTree::Node(node, p, Color::Red, nv, left, right), p) == 1 by {
                        unfold(sized_parent_is(SizedTree::Node(node, p, Color::Red, nv, left, right), p)); close();
                    }
                    have sized_parent_is(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)), p) == 1 by {
                        unfold(sized_parent_is(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)), p)); close();
                    }
                    have to_integer(sized_value(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)))) == 2 + to_integer(sized_value(sized_left(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))))) + to_integer(sized_value(sized_right(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))))) + to_integer(sized_value(SizedTree::Node(node, p, Color::Red, nv, left, right))) by {
                        unfold(sized_value(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))));
                        unfold(sized_left(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))));
                        unfold(sized_right(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))));
                        unfold(sized_value(SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right)));
                        unfold(sized_value(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)));
                        unfold(sized_value(SizedTree::Node(node, p, Color::Red, nv, left, right)));
                        close() using { to_integer(gv) == 2 + to_integer(nv) + to_integer(mv) + to_integer(uv); };
                    }
                    let rotated = fold(sized_rotation_right_at(g, p), {
                        model: SizedTree::Node(p, above, Color::Black, pv,
                            SizedTree::Node(node, p, Color::Red, nv, left, right),
                            SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))),
                        metadata: p_size, other: focus, demoted: demoted
                    });
                    unfold(sized_right(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)))));
                    unfold(sized_left(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))));
                    unfold(sized_right(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))));
                    unfold(sized_value(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)));
                    have 0 <= sized_value(sized_left(sized_right(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)))))) by {
                        rewrite(sized_right(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)))), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)));
                        rewrite(sized_left(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))), SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right));
                        unfold(sized_value(SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right))); close();
                    }
                    have 0 <= sized_value(sized_right(sized_right(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)))))) by {
                        rewrite(sized_right(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)))), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)));
                        rewrite(sized_right(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right));
                        rewrite(sized_value(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)), uv); close();
                    }
                    have sized_value(sized_right(sized_right(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)))))) <= 2147483646 by {
                        rewrite(sized_right(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)))), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)));
                        rewrite(sized_right(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right));
                        rewrite(sized_value(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)), uv); close();
                    }
                    have sized_value(sized_left(sized_right(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)))))) <= 2147483646 - sized_value(sized_right(sized_right(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)))))) by {
                        rewrite(sized_right(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)))), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)));
                        rewrite(sized_left(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))), SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right));
                        rewrite(sized_right(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right));
                        unfold(sized_value(SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right)));
                        rewrite(sized_value(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)), uv); close();
                    }
                    let { checked: checked } = step(RotateTreeRight, { tree: rotated });
                    have sized_shape(checked.model) == sized_context_uncle_after(g, p, m, u, node, above, left, right, middle_left, middle_right, uncle_left, uncle_right) by {
                        rewrite(sized_shape(checked.model), sized_shape(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)))));
                        unfold(sized_shape(SizedTree::Node(p, above, Color::Black, pv, SizedTree::Node(node, p, Color::Red, nv, left, right), SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)))));
                        unfold(sized_shape(SizedTree::Node(node, p, Color::Red, nv, left, right)));
                        unfold(sized_shape(SizedTree::Node(g, p, Color::Red, gv, SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right), SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right))));
                        unfold(sized_shape(SizedTree::Node(m, g, Color::Black, mv, middle_left, middle_right)));
                        unfold(sized_shape(SizedTree::Node(u, g, Color::Black, uv, uncle_left, uncle_right)));
                        unfold(sized_context_uncle_after(g, p, m, u, node, above, left, right, middle_left, middle_right, uncle_left, uncle_right)); close();
                    }
                    have rb_subtree_size(sized_context_uncle_after(g, p, m, u, node, above, left, right, middle_left, middle_right, uncle_left, uncle_right)) == to_integer(gv) by {
                        unfold(sized_context_uncle_after(g, p, m, u, node, above, left, right, middle_left, middle_right, uncle_left, uncle_right));
                        unfold(rb_subtree_size(RbTree::Node(p, above, Color::Black, RbTree::Node(node, p, Color::Red, sized_shape(left), sized_shape(right)), RbTree::Node(g, p, Color::Red, RbTree::Node(m, g, Color::Black, sized_shape(middle_left), sized_shape(middle_right)), RbTree::Node(u, g, Color::Black, sized_shape(uncle_left), sized_shape(uncle_right))))));
                        unfold(rb_subtree_size(RbTree::Node(node, p, Color::Red, sized_shape(left), sized_shape(right))));
                        unfold(rb_subtree_size(RbTree::Node(g, p, Color::Red, RbTree::Node(m, g, Color::Black, sized_shape(middle_left), sized_shape(middle_right)), RbTree::Node(u, g, Color::Black, sized_shape(uncle_left), sized_shape(uncle_right)))));
                        unfold(rb_subtree_size(RbTree::Node(m, g, Color::Black, sized_shape(middle_left), sized_shape(middle_right))));
                        unfold(rb_subtree_size(RbTree::Node(u, g, Color::Black, sized_shape(uncle_left), sized_shape(uncle_right))));
                        unfold(sized_shape(SizedTree::Node(node, p, Color::Red, nv, left, right)));
                        close() using {
                            to_integer(gv) == 2 + to_integer(nv) + to_integer(mv) + to_integer(uv);
                            rb_subtree_size(sized_shape(left)) + rb_subtree_size(sized_shape(right)) + 1 == to_integer(nv);
                            rb_subtree_size(sized_shape(middle_left)) + rb_subtree_size(sized_shape(middle_right)) + 1 == to_integer(mv);
                            rb_subtree_size(sized_shape(uncle_left)) + rb_subtree_size(sized_shape(uncle_right)) + 1 == to_integer(uv);
                        };
                    }
                    have to_integer(sized_value(checked.model)) == to_integer(gv) by {
                        rewrite(to_integer(sized_value(checked.model)), rb_subtree_size(sized_shape(checked.model)));
                        rewrite(sized_shape(checked.model), sized_context_uncle_after(g, p, m, u, node, above, left, right, middle_left, middle_right, uncle_left, uncle_right));
                        close();
                    }
                    have sized_value(checked.model) == gv;
                    apply(sized_parent_is_shape(checked.model, above));
                    have rb_parent_is(sized_shape(checked.model), above) == 1 by {
                        rewrite(sized_shape(checked.model), sized_context_uncle_after(g, p, m, u, node, above, left, right, middle_left, middle_right, uncle_left, uncle_right));
                        unfold(sized_context_uncle_after(g, p, m, u, node, above, left, right, middle_left, middle_right, uncle_left, uncle_right));
                        unfold(rb_parent_is(RbTree::Node(p, above, Color::Black, RbTree::Node(node, p, Color::Red, sized_shape(left), sized_shape(right)), RbTree::Node(g, p, Color::Red, RbTree::Node(m, g, Color::Black, sized_shape(middle_left), sized_shape(middle_right)), RbTree::Node(u, g, Color::Black, sized_shape(uncle_left), sized_shape(uncle_right)))), above)); close();
                    }
                    have sized_parent_is(checked.model, above) == 1 by {
                        rewrite(sized_parent_is(checked.model, above), rb_parent_is(sized_shape(checked.model), above));
                        close();
                    }
                    let { frames: path } = unfold(link);
                    have path.model == old(state.context) by { close(); }
                    have sized_parent_is(checked.model, sized_context_parent(path.model, 0)) == 1 by {
                        rewrite(path.model, old(state.context));
                        rewrite(sized_context_parent(old(state.context), 0), above);
                        close();
                    }
                    mark before_restore;
                    let { whole: whole } = restore_sized_context(p, root->rb_node, 0, gv, { path: path, sub: checked });
                    have whole.model == sized_plug(old(state.context), at(before_restore, checked.model)) by { close(); }
                    let state = fold(sized_insert_context_uncle_at(node, root), {
                        phase: SizedInsertContextUnclePhase::After(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right), model: at(before_restore, checked.model), context: old(state.context), whole_model: whole.model,
                        whole: whole
                    });
                    have state.context == old(state.context) by { close(); }
                    have state.whole_model == sized_plug(old(state.context), state.model) by { close(); }
                    have state.phase == sized_context_uncle_finish(old(state.phase)) by {
                        unfold(sized_context_uncle_finish(SizedInsertContextUnclePhase::Before(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right))); close();
                    }
                    have sized_shape(state.model) == sized_context_uncle_expected(old(state.phase), node) by {
                        rewrite(old(state.phase), SizedInsertContextUnclePhase::Before(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right));
                        unfold(sized_context_uncle_expected(SizedInsertContextUnclePhase::Before(g, p, m, u, above, nv, pv, gv, mv, uv, left, right, middle_left, middle_right, uncle_left, uncle_right), node)); close();
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
    requires RotateTreeRight(augment_rotate);
    owns state: sized_insert_context_uncle_at(node, root);
    requires sized_context_uncle_pending(state.phase) == 1;
    requires node->rb_left != node;
    requires node->rb_right != node;
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
    requires node->rb_left != node;
    requires node->rb_right != node;
    ensures state.context == old(state.context);
    ensures state.whole_model == sized_plug(old(state.context), state.model);
    ensures state.phase == sized_context_uncle_finish(old(state.phase));
    ensures sized_shape(state.model) == sized_context_uncle_expected(old(state.phase), node);
} by {
    have separate(state, memory(augment->rotate)) by close();
    step(insert::__rb_insert_augmented, { state: state });
}
