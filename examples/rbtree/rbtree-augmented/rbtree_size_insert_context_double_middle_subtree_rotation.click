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

// The transferred subtree retains its identities and in-order sequence.
theorem sized_context_double_middle_subtree_preserves_inorder(g: struct rb_node*, p: struct rb_node*, node: struct rb_node*,
    above: struct rb_node*, pv: int32, gv: int32, far: SizedTree, m: struct rb_node*, mv: int32,
    middle_left: SizedTree, middle_right: SizedTree, nv: int32) {
    ensures rb_inorder(sized_context_double_middle_subtree_after(g, p, node, above, pv, gv, far, m, mv, middle_left, middle_right, nv))
        == rb_inorder(sized_shape(sized_context_double_middle_subtree_before(g, p, node, above, pv, gv, far, m, mv, middle_left, middle_right, nv))) by {
        apply(sized_context_double_subtree_preserves_inorder(g, p, node, above, nv, pv, gv, far, SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right), SizedTree::Empty, SizedTree::Empty));
        unfold(sized_context_double_middle_subtree_before(g, p, node, above, pv, gv, far, m, mv, middle_left, middle_right, nv));
        unfold(sized_context_double_subtree_before(g, p, node, above, nv, pv, gv, far, SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right), SizedTree::Empty, SizedTree::Empty));
        unfold(sized_context_double_middle_subtree_after(g, p, node, above, pv, gv, far, m, mv, middle_left, middle_right, nv));
        unfold(sized_context_double_subtree_after(g, p, node, above, far, SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right), SizedTree::Empty, SizedTree::Empty));
        unfold(sized_shape(SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right)));
        unfold(sized_shape(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)));
        unfold(rb_reparent(RbTree::Node(m, node, Color::Black, sized_shape(middle_left), sized_shape(middle_right)), p));
        unfold(sized_shape(SizedTree::Empty));
        unfold(rb_reparent(RbTree::Empty, g));
        close();
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

// Retain complete node observations through read-only C steps.
resource context_double_middle_node_frame(p: struct rb_node*, up: struct rb_node*) {
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

resource context_double_middle_tag(p: struct rb_node*, up: struct rb_node*) {
    field color: Color;
    field word: uint64;
    owns p->__rb_parent_color;
    fact p->__rb_parent_color == word;
    fact p->__rb_parent_color == address(up) + (p->__rb_parent_color & 1);
    fact ((p->__rb_parent_color & ~3) as (struct rb_node*)) == up;
    fact (p->__rb_parent_color & 1) == color_bit(color);
}

resource context_double_middle_link(slot: struct rb_node**) {
    field child: int32*;
    owns *slot;
    fact *slot == child;
}

void insert::__rb_insert(struct rb_node* node, struct rb_root* root,
                  void (*augment_rotate)(struct rb_node*, struct rb_node*)) {
    requires RotateTreeRight(augment_rotate);
    requires RotateTreeLeft(augment_rotate);
    owns state: sized_insert_context_double_middle_subtree_at(node, root);
    requires sized_context_double_middle_subtree_pending(state.phase) == 1;
    requires node->rb_left != node;
    requires node->rb_right != node;
    ensures state.context == old(state.context);
    ensures state.whole_model == sized_plug(old(state.context), state.model);
    ensures state.phase == sized_context_double_middle_subtree_finish(old(state.phase));
    ensures sized_shape(state.model) == sized_context_double_middle_subtree_expected(old(state.phase), node);
} by {
    match state.phase {
        SizedInsertContextDoubleMiddleSubtreePhase::After(g, p, above, pv, gv, far, m, mv, middle_left, middle_right, nv) => {
            have sized_context_double_middle_subtree_pending(state.phase) != 1 by {
                rewrite(state.phase, SizedInsertContextDoubleMiddleSubtreePhase::After(g, p, above, pv, gv, far, m, mv, middle_left, middle_right, nv));
                unfold(sized_context_double_middle_subtree_pending(SizedInsertContextDoubleMiddleSubtreePhase::After(g, p, above, pv, gv, far, m, mv, middle_left, middle_right, nv))); normalize();
            }
            contradiction(sized_context_double_middle_subtree_pending(state.phase) == 1);
        },
        SizedInsertContextDoubleMiddleSubtreePhase::Before(g, p, above, pv, gv, far, m, mv, middle_left, middle_right, nv) => {
            let { tree: tree, link: link } = unfold(state);
            unfold(sized_context_double_middle_subtree_before(g, p, node, above, pv, gv, far, m, mv, middle_left, middle_right, nv));
            have tree.model == SizedTree::Node(g, above, Color::Black, gv, SizedTree::Node(p, g, Color::Red, pv, far, SizedTree::Node(node, p, Color::Red, nv, SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right), SizedTree::Empty)), SizedTree::Empty) by {
                rewrite(tree.model, sized_context_double_middle_subtree_before(g, p, node, above, pv, gv, far, m, mv, middle_left, middle_right, nv));
                unfold(sized_context_double_middle_subtree_before(g, p, node, above, pv, gv, far, m, mv, middle_left, middle_right, nv)); normalize();
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
            let { metadata: m_size, left: m_left, right: m_right } = unfold(n_left);
            have node == g->rb_left->rb_right by close();
            have node->rb_left == m by {
                rewrite(node, g->rb_left->rb_right);
                close();
            }
            have m == old(g->rb_left->rb_right->rb_left) by close();
            let n_left = fold(sized_at(m), { model: SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right), metadata: m_size, left: m_left, right: m_right });
            have node->rb_left != node by close();
            have node->rb_right != node by close();
            let initial_focus = fold(context_double_middle_node_frame(node, p), { color: Color::Red, word: node->__rb_parent_color, left: node->rb_left, right: node->rb_right });
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
            let initial_parent = fold(context_double_middle_node_frame(p, g), { color: Color::Red, word: p->__rb_parent_color, left: p->rb_left, right: p->rb_right });
            let initial_grandparent = fold(context_double_middle_node_frame(g, above), { color: Color::Black, word: g->__rb_parent_color, left: g->rb_left, right: g->rb_right });
            step(); step(); step(); step();
            unfold(initial_grandparent); unfold(initial_parent);
            unfold(initial_focus);
            let focus = fold(sized_at(node), { model: SizedTree::Node(node, p, Color::Red, nv, SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right), SizedTree::Empty), metadata: n_size, left: n_left, right: n_right });
            have p->rb_right == node by { close(); }
            have p->rb_left != p by {
                close();
            }
            have p->rb_right != p by {
                close();
            }
            let parent_tree = fold(sized_at(p), { model: SizedTree::Node(p, g, Color::Red, pv, far, SizedTree::Node(node, p, Color::Red, nv, SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right), SizedTree::Empty)), metadata: p_size, left: p_left, right: focus });
            have ((g->__rb_parent_color & ~3) as (struct rb_node*)) == above by close();
            let tree = fold(sized_at(g), { model: SizedTree::Node(g, above, Color::Black, gv, SizedTree::Node(p, g, Color::Red, pv, far, SizedTree::Node(node, p, Color::Red, nv, SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right), SizedTree::Empty)), SizedTree::Empty), metadata: g_size, left: parent_tree, right: g_right });
            have tree.model == old(state.model) by close();
            let state = fold(sized_insert_context_double_middle_subtree_at(node, root), { phase: SizedInsertContextDoubleMiddleSubtreePhase::Before(g, p, above, pv, gv, far, m, mv, middle_left, middle_right, nv), model: old(state.model), context: old(state.context), whole_model: old(state.whole_model), tree: tree, link: link });
            step(); // Declare tmp before the C loop.
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
                initialize by close();
                maintain by {
                    let { tree: loop_tree, link: link } = unfold(state);
                    unfold(sized_context_double_middle_subtree_before(g, p, node, above, pv, gv, far, m, mv, middle_left, middle_right, nv));
                    have loop_tree.model == SizedTree::Node(g, above, Color::Black, gv, SizedTree::Node(p, g, Color::Red, pv, far, SizedTree::Node(node, p, Color::Red, nv, SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right), SizedTree::Empty)), SizedTree::Empty) by {
                        rewrite(loop_tree.model, sized_context_double_middle_subtree_before(g, p, node, above, pv, gv, far, m, mv, middle_left, middle_right, nv));
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
                        close() using { to_integer(nv) == 1 + to_integer(sized_value(SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right))) + to_integer(sized_value(SizedTree::Empty)); to_integer(sized_value(SizedTree::Empty)) == 0; };
                    }
                    have to_integer(pv) == 1 + to_integer(sized_value(far)) + to_integer(nv) by {
                        close();
                    }
                    have to_integer(gv) == 1 + to_integer(pv) by {
                        close() using { to_integer(gv) == 1 + to_integer(sized_value(SizedTree::Node(p, g, Color::Red, pv, far, SizedTree::Node(node, p, Color::Red, nv, SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right), SizedTree::Empty)))) + to_integer(sized_value(SizedTree::Empty)); to_integer(sized_value(SizedTree::Node(p, g, Color::Red, pv, far, SizedTree::Node(node, p, Color::Red, nv, SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right), SizedTree::Empty)))) == to_integer(pv); to_integer(sized_value(SizedTree::Empty)) == 0; };
                    }
                    have to_integer(pv) == 2 + to_integer(sized_value(far)) + to_integer(sized_value(SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right))) by {
                        close() using {
                            to_integer(pv) == 1 + to_integer(sized_value(far)) + to_integer(nv);
                            to_integer(nv) == 1 + to_integer(sized_value(SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right)));
                        };
                    }
                    apply(sized_reparent_observations(SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right), p));
                    unfold(sized_reparent(SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right), p));
                    unfold(sized_value(SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right)));
                    unfold(sized_value(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)));
                    apply(sized_double_middle_bounds(pv, nv, far, SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right)));
                    have to_integer(pv - 1) == to_integer(pv) - to_integer(1);
                    let focus = fold(sized_at(node), { model: SizedTree::Node(node, p, Color::Red, nv, SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right), SizedTree::Empty), metadata: n_size, left: n_left, right: n_right });
                    have node->__rb_parent_color == address(p) + (node->__rb_parent_color & 1) by { close(); }
                    let { metadata: n_size, left: n_left, right: n_right } = unfold(focus);
                    have separate(memory(g->__rb_parent_color), memory(node->__rb_parent_color)) by close();
                    have g != node by close();
                    let focus = fold(sized_at(node), { model: SizedTree::Node(node, p, Color::Red, nv, SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right), SizedTree::Empty), metadata: n_size, left: n_left, right: n_right });
                    unfold(color_bit(Color::Red)); unfold(color_bit(Color::Black));
                    have p->__rb_parent_color == address(g) by {
                        rewrite(p->__rb_parent_color, address(g) + (p->__rb_parent_color & 1));
                        rewrite((p->__rb_parent_color & 1), color_bit(Color::Red));
                        rewrite(color_bit(Color::Red), 0); normalize();
                    }
                    have g->__rb_parent_color == address(above) + 1 by {
                        rewrite(g->__rb_parent_color, address(above) + (g->__rb_parent_color & 1));
                        rewrite((g->__rb_parent_color & 1), color_bit(Color::Black));
                        rewrite(color_bit(Color::Black), 1); normalize();
                    }
                    let loop_parent = fold(context_double_middle_node_frame(p, g), { color: Color::Red, word: p->__rb_parent_color, left: p->rb_left, right: p->rb_right });
                    let loop_grandparent = fold(context_double_middle_node_frame(g, above), { color: Color::Black, word: g->__rb_parent_color, left: g->rb_left, right: g->rb_right });
                    step(); step(); step(); step(); step(); step(); step();
                    unfold(loop_grandparent);
                    have gparent == g by close();
                    have parent == p by close();
                    let grandparent_tag = fold(context_double_middle_tag(g, above), { color: Color::Black, word: g->__rb_parent_color });
                    let grandparent_left = fold(context_double_middle_link(&g->rb_left), { child: g->rb_left });
                    let grandparent_right = fold(context_double_middle_link(&g->rb_right), { child: g->rb_right });
                    step(); step(); step();
                    step(); // Load the inner pivot into tmp.
                    unfold(loop_parent);
                    have p->rb_right == node by close();
                    have tmp == node by close();
                    step();
                    let { metadata: n_size, left: n_left, right: n_right } = unfold(focus);
                    unfold(n_right);
                    let { metadata: m_size, left: m_left, right: m_right } = unfold(n_left);
                    have node->rb_left == m by { close(); }
                    have m != 0 by { close(); }
                    have separate(memory(p->__rb_parent_color), memory(m->__rb_parent_color)) by { close(); }
                    have m != p by { close(); }
                    have to_integer(mv) == 1 + to_integer(sized_value(middle_left)) + to_integer(sized_value(middle_right)) by { close(); }
                    let n_left = fold(sized_recompute_at(m), { model: SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right), metadata: m_size, left: m_left, right: m_right });
                    have node->rb_right == 0 by close();
                    let node_tag = fold(context_double_middle_tag(node, p), { color: Color::Red, word: node->__rb_parent_color });
                    let parent_tag = fold(context_double_middle_tag(p, g), { color: Color::Red, word: p->__rb_parent_color });
                    let outer_right = fold(context_double_middle_link(&node->rb_right), { child: node->rb_right });
                    let parent_left = fold(context_double_middle_link(&p->rb_left), { child: p->rb_left });
                    step(); // Read the transferred subtree.
                    have tmp == m by close();
                    step(); // Install it as the parent's right child.
                    have p->rb_right == m by close();
                    let parent_right = fold(context_double_middle_link(&p->rb_right), { child: m });
                    step(); // Put the old parent under the pivot.
                    have node->rb_left == p by close();
                    let inner_left = fold(context_double_middle_link(&node->rb_left), { child: p });
                    step(); // Enter the nonnull transferred-child branch.
                    unfold(sized_root_color_bit(SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right)));
                    have 1 == sized_root_color_bit(n_left.model) by close();
                    let { after: dirty_middle } = step(insert::rb_set_parent_color, { tree: n_left });
                    unfold(sized_reparent(SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right), p));
                    have dirty_middle.model == SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right) by close();
                    let { metadata: m_size, left: m_left, right: m_right } = unfold(dirty_middle);
                    let p_right = fold(sized_at(m), { model: SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), metadata: m_size, left: m_left, right: m_right });
                    unfold(parent_tag); unfold(parent_left); unfold(parent_right);
                    have p->rb_right == m by close();
                    have sized_parent_is(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), p) == 1 by {
                        unfold(sized_parent_is(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), p)); normalize();
                    }
                    let before_parent_update = fold(sized_recompute_at(p), { model: SizedTree::Node(p, g, Color::Red, pv, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)), metadata: p_size, left: p_left, right: p_right });
                    unfold(sized_root_color_bit(SizedTree::Node(p, g, Color::Red, pv, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))));
                    have 0 == sized_root_color_bit(before_parent_update.model) by close();
                    let { after: demoted } = step(insert::rb_set_parent_color, { tree: before_parent_update });
                    unfold(sized_reparent(SizedTree::Node(p, g, Color::Red, pv, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)), node));
                    have demoted.model == SizedTree::Node(p, node, Color::Red, pv, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)) by close();
                    unfold(outer_right); unfold(inner_left); unfold(node_tag);
                    have node->rb_right == 0 by close();
                    have node->rb_left == p by close();
                    let other = fold(sized_at(0), { model: SizedTree::Empty });
                    have sized_parent_is(SizedTree::Node(p, node, Color::Red, pv, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)), node) == 1 by { unfold(sized_parent_is(SizedTree::Node(p, node, Color::Red, pv, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)), node)); normalize(); }
                    have sized_parent_is(SizedTree::Empty, node) == 1 by { unfold(sized_parent_is(SizedTree::Empty, node)); normalize(); }
                    unfold(sized_value(SizedTree::Node(p, node, Color::Red, pv, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))));
                    unfold(sized_left(SizedTree::Node(p, node, Color::Red, pv, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))));
                    unfold(sized_right(SizedTree::Node(p, node, Color::Red, pv, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))));
                    unfold(sized_value(SizedTree::Empty));
                    have to_integer(sized_value(SizedTree::Node(p, node, Color::Red, pv, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)))) == 2 + to_integer(sized_value(sized_left(SizedTree::Node(p, node, Color::Red, pv, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))))) + to_integer(sized_value(sized_right(SizedTree::Node(p, node, Color::Red, pv, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))))) + to_integer(sized_value(SizedTree::Empty)) by {
                        rewrite(sized_value(SizedTree::Node(p, node, Color::Red, pv, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))), pv);
                        rewrite(sized_left(SizedTree::Node(p, node, Color::Red, pv, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))), far);
                        rewrite(sized_right(SizedTree::Node(p, node, Color::Red, pv, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))), SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right));
                        rewrite(sized_value(SizedTree::Empty), 0); close();
                    }
                    let rotated = fold(sized_rotation_left_at(p, node), { model: SizedTree::Node(node, p, Color::Red, nv, SizedTree::Node(p, node, Color::Red, pv, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)), SizedTree::Empty), metadata: n_size, demoted: demoted, other: other });
                    unfold(sized_left(SizedTree::Node(node, p, Color::Red, nv, SizedTree::Node(p, node, Color::Red, pv, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)), SizedTree::Empty)));
                    let { checked: first } = step(RotateTreeLeft, { tree: rotated });
                    let { checked: first } = certify_size(node, { tree: first });
                    apply(sized_double_middle_valid(p, node, pv, far, SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right)));
                    unfold(sized_reparent(SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right), p));
                    unfold(sized_recolor(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), Color::Black));
                    have sized_shape(first.model) == sized_shape(SizedTree::Node(node, p, Color::Red, pv, SizedTree::Node(p, node, Color::Red, pv - 1, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)), SizedTree::Empty)) by {
                        rewrite(sized_shape(first.model), sized_shape(SizedTree::Node(node, p, Color::Red, nv, SizedTree::Node(p, node, Color::Red, pv, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)), SizedTree::Empty)));
                        unfold(sized_shape(SizedTree::Node(node, p, Color::Red, nv, SizedTree::Node(p, node, Color::Red, pv, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)), SizedTree::Empty)));
                        unfold(sized_shape(SizedTree::Node(node, p, Color::Red, pv, SizedTree::Node(p, node, Color::Red, pv - 1, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)), SizedTree::Empty)));
                        unfold(sized_shape(SizedTree::Node(p, node, Color::Red, pv, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))));
                        unfold(sized_shape(SizedTree::Node(p, node, Color::Red, pv - 1, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)))); normalize();
                    }
                    apply(sized_model_unique(first.model, SizedTree::Node(node, p, Color::Red, pv, SizedTree::Node(p, node, Color::Red, pv - 1, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)), SizedTree::Empty)));
                    have first.model == SizedTree::Node(node, p, Color::Red, pv, SizedTree::Node(p, node, Color::Red, pv - 1, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)), SizedTree::Empty) by { close(); }
                    let { metadata: n_size, left: parent_subtree, right: outer_empty } = unfold(first);
                    unfold(outer_empty);
                    let { metadata: p_size, left: far_subtree, right: middle_subtree } = unfold(parent_subtree);
                    have node->rb_left == p by close();
                    let parent_subtree = fold(sized_at(p), { model: SizedTree::Node(p, node, Color::Red, pv - 1, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)), metadata: p_size, left: far_subtree, right: middle_subtree });
                    let kept_left = fold(context_double_middle_link(&node->rb_left), { child: p });
                    unfold(grandparent_left);
                    step(); step(); step(); // Select the pivot and store the null outer middle child.
                    have parent == node by close();
                    have g->rb_left == 0 by close();
                    let kept_g_left = fold(context_double_middle_link(&g->rb_left), { child: g->rb_left });
                    step(); // Put the grandparent under the promoted pivot.
                    have node->rb_right == g by close();
                    let kept_right = fold(context_double_middle_link(&node->rb_right), { child: node->rb_right });
                    step(); step(); // The outer middle child is null.
                    unfold(grandparent_tag);
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
                    let g_size = fold(size_metadata(g), { value: gv });
                    unfold(kept_g_left); unfold(grandparent_right);
                    unfold(kept_left); unfold(kept_right);
                    have g->rb_left == 0 by close();
                    have g->rb_right == 0 by close();
                    let g_left = fold(sized_at(0), { model: SizedTree::Empty });
                    let g_right = fold(sized_at(0), { model: SizedTree::Empty });
                    let demoted = fold(sized_recompute_at(g), {
                        model: SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty),
                        metadata: g_size, left: g_left, right: g_right
                    });
                    have node->rb_left == p by close();
                    have node->rb_right == g by close();
                    have parent == node by close();
                    have node->__rb_parent_color == at(before_parent_update, g->__rb_parent_color) by { close(); }
                    have node->__rb_parent_color == address(above) + (node->__rb_parent_color & 1) by {
                        rewrite(node->__rb_parent_color, at(before_parent_update, g->__rb_parent_color));
                        close();
                    }
                    have (node->__rb_parent_color & 1) == color_bit(Color::Black) by {
                        rewrite(node->__rb_parent_color, at(before_parent_update, g->__rb_parent_color));
                        close();
                    }
                    have sized_parent_is(SizedTree::Node(p, node, Color::Red, pv - 1, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)), node) == 1 by {
                        unfold(sized_parent_is(SizedTree::Node(p, node, Color::Red, pv - 1, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)), node)); normalize();
                    }
                    have sized_parent_is(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty), node) == 1 by {
                        unfold(sized_parent_is(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty), node)); normalize();
                    }
                    unfold(sized_value(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)));
                    unfold(sized_left(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)));
                    unfold(sized_right(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)));
                    unfold(sized_value(SizedTree::Node(p, node, Color::Red, pv - 1, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))));
                    have to_integer(sized_value(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty))) == 2 + to_integer(sized_value(sized_left(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)))) + to_integer(sized_value(sized_right(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)))) + to_integer(sized_value(SizedTree::Node(p, node, Color::Red, pv - 1, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)))) by {
                        rewrite(sized_value(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)), gv);
                        rewrite(sized_left(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty);
                        rewrite(sized_right(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Node(p, node, Color::Red, pv - 1, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))), pv - 1);
                        rewrite(sized_value(SizedTree::Empty), 0);
                        close() using {
                            to_integer(gv) == 1 + to_integer(pv);
                            to_integer(pv - 1) == to_integer(pv) - to_integer(1);
                        };
                    }
                    let second_rotated = fold(sized_rotation_right_at(g, node), {
                        model: SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(p, node, Color::Red, pv - 1, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)), SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)),
                        metadata: n_size, other: parent_subtree, demoted: demoted
                    });
                    unfold(sized_right(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(p, node, Color::Red, pv - 1, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)), SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty))));
                    unfold(sized_left(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)));
                    unfold(sized_right(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)));
                    unfold(sized_value(SizedTree::Empty));
                    have 0 <= sized_value(sized_left(sized_right(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(p, node, Color::Red, pv - 1, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)), SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty))))) by {
                        rewrite(sized_right(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(p, node, Color::Red, pv - 1, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)), SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty))), SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty));
                        rewrite(sized_left(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty), 0); normalize();
                    }
                    have 0 <= sized_value(sized_right(sized_right(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(p, node, Color::Red, pv - 1, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)), SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty))))) by {
                        rewrite(sized_right(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(p, node, Color::Red, pv - 1, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)), SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty))), SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty));
                        rewrite(sized_right(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty), 0); normalize();
                    }
                    have sized_value(sized_right(sized_right(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(p, node, Color::Red, pv - 1, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)), SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty))))) <= 2147483646 by {
                        rewrite(sized_right(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(p, node, Color::Red, pv - 1, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)), SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty))), SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty));
                        rewrite(sized_right(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty), 0); normalize();
                    }
                    have sized_value(sized_left(sized_right(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(p, node, Color::Red, pv - 1, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)), SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty))))) <= 2147483646 - sized_value(sized_right(sized_right(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(p, node, Color::Red, pv - 1, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)), SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty))))) by {
                        rewrite(sized_right(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(p, node, Color::Red, pv - 1, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)), SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty))), SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty));
                        rewrite(sized_left(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty);
                        rewrite(sized_right(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty), 0); normalize();
                    }
                    let { checked: second } = step(RotateTreeRight, { tree: second_rotated });
                    have sized_shape(second.model) == sized_context_double_middle_subtree_after(g, p, node, above, pv, gv, far, m, mv, middle_left, middle_right, nv) by {
                        rewrite(sized_shape(second.model), sized_shape(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(p, node, Color::Red, pv - 1, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)), SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty))));
                        unfold(sized_shape(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(p, node, Color::Red, pv - 1, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)), SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty))));
                        unfold(sized_shape(SizedTree::Node(p, node, Color::Red, pv - 1, far, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))));
                        unfold(sized_shape(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)));
                        unfold(sized_shape(SizedTree::Empty));
                        unfold(sized_context_double_middle_subtree_after(g, p, node, above, pv, gv, far, m, mv, middle_left, middle_right, nv)); normalize();
                    }
                    have rb_subtree_size(sized_context_double_middle_subtree_after(g, p, node, above, pv, gv, far, m, mv, middle_left, middle_right, nv)) == to_integer(gv) by {
                        unfold(sized_context_double_middle_subtree_after(g, p, node, above, pv, gv, far, m, mv, middle_left, middle_right, nv));
                        unfold(rb_subtree_size(RbTree::Node(node, above, Color::Black, RbTree::Node(p, node, Color::Red, sized_shape(far), sized_shape(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))), RbTree::Node(g, node, Color::Red, RbTree::Empty, RbTree::Empty))));
                        unfold(rb_subtree_size(RbTree::Node(p, node, Color::Red, sized_shape(far), sized_shape(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))))); unfold(rb_subtree_size(RbTree::Node(g, node, Color::Red, RbTree::Empty, RbTree::Empty)));
                        unfold(rb_subtree_size(RbTree::Empty));
                        apply(sized_valid_value_matches_size(far));
                        apply(sized_valid_value_matches_size(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)));
                        close() using {
                            to_integer(gv) == 1 + to_integer(pv);
                            to_integer(pv) == 2 + to_integer(sized_value(far)) + to_integer(sized_value(SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right)));
                            to_integer(sized_value(far)) == rb_subtree_size(sized_shape(far));
                            to_integer(sized_value(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))) == rb_subtree_size(sized_shape(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)));
                            to_integer(sized_value(SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right))) == to_integer(mv);
                            to_integer(sized_value(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))) == to_integer(mv);
                        };
                    }
                    have to_integer(sized_value(second.model)) == to_integer(gv) by {
                        rewrite(to_integer(sized_value(second.model)), rb_subtree_size(sized_shape(second.model)));
                        rewrite(sized_shape(second.model), sized_context_double_middle_subtree_after(g, p, node, above, pv, gv, far, m, mv, middle_left, middle_right, nv)); close();
                    }
                    have sized_value(second.model) == gv;
                    apply(sized_parent_is_shape(second.model, above));
                    have rb_parent_is(sized_shape(second.model), above) == 1 by {
                        rewrite(sized_shape(second.model), sized_context_double_middle_subtree_after(g, p, node, above, pv, gv, far, m, mv, middle_left, middle_right, nv));
                        unfold(sized_context_double_middle_subtree_after(g, p, node, above, pv, gv, far, m, mv, middle_left, middle_right, nv));
                        unfold(rb_parent_is(RbTree::Node(node, above, Color::Black, RbTree::Node(p, node, Color::Red, sized_shape(far), sized_shape(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))), RbTree::Node(g, node, Color::Red, RbTree::Empty, RbTree::Empty)), above)); normalize();
                    }
                    have sized_parent_is(second.model, above) == 1 by {
                        rewrite(sized_parent_is(second.model, above), rb_parent_is(sized_shape(second.model), above)); close();
                    }
                    let { frames: path } = unfold(link);
                    have path.model == old(state.context) by { close(); }
                    have sized_parent_is(second.model, sized_context_parent(path.model, 0)) == 1 by {
                        rewrite(path.model, old(state.context));
                        rewrite(sized_context_parent(old(state.context), 0), above); close();
                    }
                    mark before_restore;
                    let { whole: whole } = restore_sized_context(node, root->rb_node, 0, gv, { path: path, sub: second });
                    have whole.model == sized_plug(old(state.context), at(before_restore, second.model)) by { close(); }
                    let state = fold(sized_insert_context_double_middle_subtree_at(node, root), {
                        phase: SizedInsertContextDoubleMiddleSubtreePhase::After(g, p, above, pv, gv, far, m, mv, middle_left, middle_right, nv), model: at(before_restore, second.model), context: old(state.context), whole_model: whole.model,
                        whole: whole
                    });
                    have state.context == old(state.context) by { close(); }
                    have state.whole_model == sized_plug(old(state.context), state.model) by { close(); }
                    have state.phase == sized_context_double_middle_subtree_finish(old(state.phase)) by {
                        unfold(sized_context_double_middle_subtree_finish(SizedInsertContextDoubleMiddleSubtreePhase::Before(g, p, above, pv, gv, far, m, mv, middle_left, middle_right, nv))); close();
                    }
                    have sized_shape(state.model) == sized_context_double_middle_subtree_expected(old(state.phase), node) by {
                        rewrite(old(state.phase), SizedInsertContextDoubleMiddleSubtreePhase::Before(g, p, above, pv, gv, far, m, mv, middle_left, middle_right, nv));
                        unfold(sized_context_double_middle_subtree_expected(SizedInsertContextDoubleMiddleSubtreePhase::Before(g, p, above, pv, gv, far, m, mv, middle_left, middle_right, nv), node)); close();
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
    requires RotateTreeLeft(augment_rotate);
    owns state: sized_insert_context_double_middle_subtree_at(node, root);
    requires sized_context_double_middle_subtree_pending(state.phase) == 1;
    requires node->rb_left != node;
    requires node->rb_right != node;
    ensures state.context == old(state.context);
    ensures state.whole_model == sized_plug(old(state.context), state.model);
    ensures state.phase == sized_context_double_middle_subtree_finish(old(state.phase));
    ensures sized_shape(state.model) == sized_context_double_middle_subtree_expected(old(state.phase), node);
} by {
    step(insert::__rb_insert, { state: state });
}

void insert::rb_insert_augmented(struct rb_node* node, struct rb_root* root,
                         const struct rb_augment_callbacks* augment) {
    views augment->rotate;
    requires RotateTreeRight(augment->rotate);
    requires RotateTreeLeft(augment->rotate);
    owns state: sized_insert_context_double_middle_subtree_at(node, root);
    requires sized_context_double_middle_subtree_pending(state.phase) == 1;
    requires node->rb_left != node;
    requires node->rb_right != node;
    ensures state.context == old(state.context);
    ensures state.whole_model == sized_plug(old(state.context), state.model);
    ensures state.phase == sized_context_double_middle_subtree_finish(old(state.phase));
    ensures sized_shape(state.model) == sized_context_double_middle_subtree_expected(old(state.phase), node);
} by {
    have separate(state, memory(augment->rotate)) by close();
    step(insert::__rb_insert_augmented, { state: state });
}
