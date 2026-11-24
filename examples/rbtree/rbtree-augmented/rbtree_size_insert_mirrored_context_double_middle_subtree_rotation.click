// Mirrored writable insertion callbacks with arbitrary far and transferred subtrees.
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

spec enum SizedInsertMirroredContextDoubleMiddleSubtreePhase {
    Before(struct rb_node*, struct rb_node*, struct rb_node*, int32, int32, SizedTree, struct rb_node*, int32, SizedTree, SizedTree, int32),
    After(struct rb_node*, struct rb_node*, struct rb_node*, int32, int32, SizedTree, struct rb_node*, int32, SizedTree, SizedTree, int32),
}

function sized_mirrored_context_double_middle_subtree_pending(phase: SizedInsertMirroredContextDoubleMiddleSubtreePhase) -> int32 {
    match phase {
        SizedInsertMirroredContextDoubleMiddleSubtreePhase::Before(g, p, above, pv, gv, far, m, mv, middle_right, middle_left, nv) => 1,
        SizedInsertMirroredContextDoubleMiddleSubtreePhase::After(g, p, above, pv, gv, far, m, mv, middle_right, middle_left, nv) => 0,
    }
}

function sized_mirrored_context_double_middle_subtree_finish(phase: SizedInsertMirroredContextDoubleMiddleSubtreePhase) -> SizedInsertMirroredContextDoubleMiddleSubtreePhase {
    match phase {
        SizedInsertMirroredContextDoubleMiddleSubtreePhase::Before(g, p, above, pv, gv, far, m, mv, middle_right, middle_left, nv) => SizedInsertMirroredContextDoubleMiddleSubtreePhase::After(g, p, above, pv, gv, far, m, mv, middle_right, middle_left, nv),
        SizedInsertMirroredContextDoubleMiddleSubtreePhase::After(g, p, above, pv, gv, far, m, mv, middle_right, middle_left, nv) => SizedInsertMirroredContextDoubleMiddleSubtreePhase::After(g, p, above, pv, gv, far, m, mv, middle_right, middle_left, nv),
    }
}

function sized_mirrored_context_double_middle_subtree_before(g: struct rb_node*, p: struct rb_node*, n: struct rb_node*, above: struct rb_node*, pv: int32, gv: int32, far: SizedTree, m: struct rb_node*, mv: int32, middle_right: SizedTree, middle_left: SizedTree, nv: int32) -> SizedTree {
    SizedTree::Node(g, above, Color::Black, gv, SizedTree::Empty, SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(n, p, Color::Red, nv, SizedTree::Empty, SizedTree::Node(m, n, Color::Black, mv, middle_left, middle_right)), far))
}

function sized_mirrored_context_double_middle_subtree_after(g: struct rb_node*, p: struct rb_node*, n: struct rb_node*, above: struct rb_node*, pv: int32, gv: int32, far: SizedTree, m: struct rb_node*, mv: int32, middle_right: SizedTree, middle_left: SizedTree, nv: int32) -> RbTree {
    RbTree::Node(n, above, Color::Black, RbTree::Node(g, n, Color::Red, RbTree::Empty, RbTree::Empty), RbTree::Node(p, n, Color::Red, sized_shape(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)), sized_shape(far)))
}

function sized_mirrored_context_double_middle_subtree_expected(phase: SizedInsertMirroredContextDoubleMiddleSubtreePhase, node: struct rb_node*) -> RbTree {
    match phase {
        SizedInsertMirroredContextDoubleMiddleSubtreePhase::Before(g, p, above, pv, gv, far, m, mv, middle_right, middle_left, nv) => sized_mirrored_context_double_middle_subtree_after(g, p, node, above, pv, gv, far, m, mv, middle_right, middle_left, nv),
        SizedInsertMirroredContextDoubleMiddleSubtreePhase::After(g, p, above, pv, gv, far, m, mv, middle_right, middle_left, nv) => sized_mirrored_context_double_middle_subtree_after(g, p, node, above, pv, gv, far, m, mv, middle_right, middle_left, nv),
    }
}

// The transferred subtree retains its identities and in-order sequence.
theorem sized_mirrored_context_double_middle_subtree_preserves_inorder(g: struct rb_node*, p: struct rb_node*, node: struct rb_node*,
    above: struct rb_node*, pv: int32, gv: int32, far: SizedTree, m: struct rb_node*, mv: int32,
    middle_right: SizedTree, middle_left: SizedTree, nv: int32) {
    ensures rb_inorder(sized_mirrored_context_double_middle_subtree_after(g, p, node, above, pv, gv, far, m, mv, middle_right, middle_left, nv))
        == rb_inorder(sized_shape(sized_mirrored_context_double_middle_subtree_before(g, p, node, above, pv, gv, far, m, mv, middle_right, middle_left, nv))) by {
        apply(sized_mirrored_context_double_subtree_preserves_inorder(g, p, node, above, nv, pv, gv, far, SizedTree::Empty, SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right), SizedTree::Empty));
        unfold(sized_mirrored_context_double_middle_subtree_before(g, p, node, above, pv, gv, far, m, mv, middle_right, middle_left, nv));
        unfold(sized_mirrored_context_double_subtree_before(g, p, node, above, nv, pv, gv, far, SizedTree::Empty, SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right), SizedTree::Empty));
        unfold(sized_mirrored_context_double_middle_subtree_after(g, p, node, above, pv, gv, far, m, mv, middle_right, middle_left, nv));
        unfold(sized_mirrored_context_double_subtree_after(g, p, node, above, far, SizedTree::Empty, SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right), SizedTree::Empty));
        unfold(sized_shape(SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right)));
        unfold(sized_shape(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)));
        unfold(rb_reparent(RbTree::Node(m, node, Color::Black, sized_shape(middle_left), sized_shape(middle_right)), p));
        unfold(sized_shape(SizedTree::Empty));
        unfold(rb_reparent(RbTree::Empty, g));
        close();
    }
}

resource sized_insert_mirrored_context_double_middle_subtree_at(node: struct rb_node*, root: struct rb_root*) {
    field phase: SizedInsertMirroredContextDoubleMiddleSubtreePhase;
    field model: SizedTree;
    field context: SizedContext;
    field whole_model: SizedTree;
    match phase {
        SizedInsertMirroredContextDoubleMiddleSubtreePhase::Before(g, p, above, pv, gv, far, m, mv, middle_right, middle_left, nv) => {
            owns link: sized_link_at(g, root, gv);
            owns tree: sized_at(g);
            fact link.model == context;
            fact above == sized_context_parent(context, 0);
            fact tree.model == model;
            fact model == sized_mirrored_context_double_middle_subtree_before(g, p, node, above, pv, gv, far, m, mv, middle_right, middle_left, nv);
        },
        SizedInsertMirroredContextDoubleMiddleSubtreePhase::After(g, p, above, pv, gv, far, m, mv, middle_right, middle_left, nv) => {
            owns root->rb_node;
            owns whole: sized_at(root->rb_node);
            fact above == sized_context_parent(context, 0);
            fact whole.model == whole_model;
            fact sized_parent_is(whole.model, 0) == 1;
        },
    }
}

// Retain complete node observations through read-only C steps.
resource mirrored_context_double_middle_node_frame(p: struct rb_node*, up: struct rb_node*) {
    field color: Color;
    field word: uint64;
    field right: int32*;
    field left: int32*;
    owns p->__rb_parent_color;
    fact p->__rb_parent_color == word;
    fact p->__rb_parent_color == address(up) + (p->__rb_parent_color & 1);
    fact ((p->__rb_parent_color & ~3) as (struct rb_node*)) == up;
    fact (p->__rb_parent_color & 1) == color_bit(color);
    owns p->rb_right;
    owns p->rb_left;
    fact p->rb_right == right;
    fact p->rb_left == left;
    fact p->rb_right != p;
    fact p->rb_left != p;
}

resource mirrored_context_double_middle_tag(p: struct rb_node*, up: struct rb_node*) {
    field color: Color;
    field word: uint64;
    owns p->__rb_parent_color;
    fact p->__rb_parent_color == word;
    fact p->__rb_parent_color == address(up) + (p->__rb_parent_color & 1);
    fact ((p->__rb_parent_color & ~3) as (struct rb_node*)) == up;
    fact (p->__rb_parent_color & 1) == color_bit(color);
}

resource mirrored_context_double_middle_link(slot: struct rb_node**) {
    field child: int32*;
    owns *slot;
    fact *slot == child;
}

void insert::__rb_insert(struct rb_node* node, struct rb_root* root,
                  void (*augment_rotate)(struct rb_node*, struct rb_node*)) {
    requires RotateTreeLeft(augment_rotate);
    requires RotateTreeRight(augment_rotate);
    owns state: sized_insert_mirrored_context_double_middle_subtree_at(node, root);
    requires sized_mirrored_context_double_middle_subtree_pending(state.phase) == 1;
    requires node->rb_left != node;
    requires node->rb_right != node;
    ensures state.context == old(state.context);
    ensures state.whole_model == sized_plug(old(state.context), state.model);
    ensures state.phase == sized_mirrored_context_double_middle_subtree_finish(old(state.phase));
    ensures sized_shape(state.model) == sized_mirrored_context_double_middle_subtree_expected(old(state.phase), node);
} by {
    match state.phase {
        SizedInsertMirroredContextDoubleMiddleSubtreePhase::After(g, p, above, pv, gv, far, m, mv, middle_right, middle_left, nv) => {
            have sized_mirrored_context_double_middle_subtree_pending(state.phase) != 1 by {
                rewrite(state.phase, SizedInsertMirroredContextDoubleMiddleSubtreePhase::After(g, p, above, pv, gv, far, m, mv, middle_right, middle_left, nv));
                unfold(sized_mirrored_context_double_middle_subtree_pending(SizedInsertMirroredContextDoubleMiddleSubtreePhase::After(g, p, above, pv, gv, far, m, mv, middle_right, middle_left, nv))); normalize();
            }
            contradiction(sized_mirrored_context_double_middle_subtree_pending(state.phase) == 1);
        },
        SizedInsertMirroredContextDoubleMiddleSubtreePhase::Before(g, p, above, pv, gv, far, m, mv, middle_right, middle_left, nv) => {
            let { tree: tree, link: link } = unfold(state);
            unfold(sized_mirrored_context_double_middle_subtree_before(g, p, node, above, pv, gv, far, m, mv, middle_right, middle_left, nv));
            have tree.model == SizedTree::Node(g, above, Color::Black, gv, SizedTree::Empty, SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(node, p, Color::Red, nv, SizedTree::Empty, SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right)), far)) by {
                rewrite(tree.model, sized_mirrored_context_double_middle_subtree_before(g, p, node, above, pv, gv, far, m, mv, middle_right, middle_left, nv));
                unfold(sized_mirrored_context_double_middle_subtree_before(g, p, node, above, pv, gv, far, m, mv, middle_right, middle_left, nv)); normalize();
            }
            let { metadata: g_size, right: parent_tree, left: g_left } = unfold(tree);
            let { metadata: p_size, right: p_right, left: focus } = unfold(parent_tree);
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
            let { metadata: m_size, right: m_right, left: m_left } = unfold(n_right);
            have node == g->rb_right->rb_left by close();
            have node->rb_right == m by {
                rewrite(node, g->rb_right->rb_left);
                close();
            }
            have m == old(g->rb_right->rb_left->rb_right) by close();
            let n_right = fold(sized_at(m), { model: SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right), metadata: m_size, right: m_right, left: m_left });
            have node->rb_left != node by close();
            have node->rb_right != node by close();
            let initial_focus = fold(mirrored_context_double_middle_node_frame(node, p), { color: Color::Red, word: node->__rb_parent_color, right: node->rb_right, left: node->rb_left });
            have p == g->rb_right by close();
            have p->__rb_parent_color == address(g) + (p->__rb_parent_color & 1) by {
                rewrite(p, g->rb_right);
                close();
            }
            have ((p->__rb_parent_color & ~3) as (struct rb_node *)) == g by {
                rewrite(p, g->rb_right);
                close();
            }
            have (p->__rb_parent_color & 1) == color_bit(Color::Red) by {
                rewrite(p, g->rb_right);
                close();
            }
            let initial_parent = fold(mirrored_context_double_middle_node_frame(p, g), { color: Color::Red, word: p->__rb_parent_color, right: p->rb_right, left: p->rb_left });
            let initial_grandparent = fold(mirrored_context_double_middle_node_frame(g, above), { color: Color::Black, word: g->__rb_parent_color, right: g->rb_right, left: g->rb_left });
            step(); step(); step(); step();
            unfold(initial_grandparent); unfold(initial_parent);
            unfold(initial_focus);
            let focus = fold(sized_at(node), { model: SizedTree::Node(node, p, Color::Red, nv, SizedTree::Empty, SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right)), metadata: n_size, right: n_right, left: n_left });
            have p->rb_left == node by { close(); }
            have p->rb_right != p by {
                close();
            }
            have p->rb_left != p by {
                close();
            }
            let parent_tree = fold(sized_at(p), { model: SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(node, p, Color::Red, nv, SizedTree::Empty, SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right)), far), metadata: p_size, right: p_right, left: focus });
            have ((g->__rb_parent_color & ~3) as (struct rb_node*)) == above by close();
            let tree = fold(sized_at(g), { model: SizedTree::Node(g, above, Color::Black, gv, SizedTree::Empty, SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(node, p, Color::Red, nv, SizedTree::Empty, SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right)), far)), metadata: g_size, right: parent_tree, left: g_left });
            have tree.model == old(state.model) by close();
            let state = fold(sized_insert_mirrored_context_double_middle_subtree_at(node, root), { phase: SizedInsertMirroredContextDoubleMiddleSubtreePhase::Before(g, p, above, pv, gv, far, m, mv, middle_right, middle_left, nv), model: old(state.model), context: old(state.context), whole_model: old(state.whole_model), tree: tree, link: link });
            step(); // Declare tmp before the C loop.
            loop {
                owns state: sized_insert_mirrored_context_double_middle_subtree_at(node, root);
                decreases 0;
                invariant node == old(node);
                invariant parent == p;
                invariant state.context == old(state.context);
                invariant p == old(g->rb_right);
                invariant m == old(g->rb_right->rb_left->rb_right);
                invariant state.phase == SizedInsertMirroredContextDoubleMiddleSubtreePhase::Before(g, p, above, pv, gv, far, m, mv, middle_right, middle_left, nv);
                invariant old(state.phase) == SizedInsertMirroredContextDoubleMiddleSubtreePhase::Before(g, p, above, pv, gv, far, m, mv, middle_right, middle_left, nv);
                invariant state.model == sized_mirrored_context_double_middle_subtree_before(g, p, node, above, pv, gv, far, m, mv, middle_right, middle_left, nv);
                initialize by close();
                maintain by {
                    let { tree: loop_tree, link: link } = unfold(state);
                    unfold(sized_mirrored_context_double_middle_subtree_before(g, p, node, above, pv, gv, far, m, mv, middle_right, middle_left, nv));
                    have loop_tree.model == SizedTree::Node(g, above, Color::Black, gv, SizedTree::Empty, SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(node, p, Color::Red, nv, SizedTree::Empty, SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right)), far)) by {
                        rewrite(loop_tree.model, sized_mirrored_context_double_middle_subtree_before(g, p, node, above, pv, gv, far, m, mv, middle_right, middle_left, nv));
                        unfold(sized_mirrored_context_double_middle_subtree_before(g, p, node, above, pv, gv, far, m, mv, middle_right, middle_left, nv)); normalize();
                    }
                    let { metadata: g_size, right: parent_tree, left: g_left } = unfold(loop_tree);
                    let { metadata: p_size, right: p_right, left: focus } = unfold(parent_tree);
                    unfold(g_left);
                    let { checked: p_right } = certify_size(p->rb_right, { tree: p_right });
                    let { metadata: n_size, right: n_right, left: n_left } = unfold(focus);
                    let { checked: n_right } = certify_size(node->rb_right, { tree: n_right });
                    unfold(sized_value(SizedTree::Node(node, p, Color::Red, nv, SizedTree::Empty, SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right))));
                    unfold(sized_value(SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(node, p, Color::Red, nv, SizedTree::Empty, SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right)), far)));
                    unfold(sized_value(SizedTree::Empty));
                    have to_integer(nv) == 1 + to_integer(sized_value(SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right))) by {
                        close() using { to_integer(nv) == 1 + to_integer(sized_value(SizedTree::Empty)) + to_integer(sized_value(SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right))); to_integer(sized_value(SizedTree::Empty)) == 0; };
                    }
                    have to_integer(pv) == 1 + to_integer(nv) + to_integer(sized_value(far)) by {
                        close();
                    }
                    have to_integer(gv) == 1 + to_integer(pv) by {
                        close() using { to_integer(gv) == 1 + to_integer(sized_value(SizedTree::Empty)) + to_integer(sized_value(SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(node, p, Color::Red, nv, SizedTree::Empty, SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right)), far))); to_integer(sized_value(SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(node, p, Color::Red, nv, SizedTree::Empty, SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right)), far))) == to_integer(pv); to_integer(sized_value(SizedTree::Empty)) == 0; };
                    }
                    have to_integer(pv) == 2 + to_integer(sized_value(far)) + to_integer(sized_value(SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right))) by {
                        close() using {
                            to_integer(pv) == 1 + to_integer(nv) + to_integer(sized_value(far));
                            to_integer(nv) == 1 + to_integer(sized_value(SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right)));
                        };
                    }
                    apply(sized_reparent_observations(SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right), p));
                    unfold(sized_reparent(SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right), p));
                    unfold(sized_value(SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right)));
                    unfold(sized_value(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)));
                    apply(sized_double_middle_bounds(pv, nv, far, SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right)));
                    have to_integer(pv - 1) == to_integer(pv) - to_integer(1);
                    let focus = fold(sized_at(node), { model: SizedTree::Node(node, p, Color::Red, nv, SizedTree::Empty, SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right)), metadata: n_size, right: n_right, left: n_left });
                    have node->__rb_parent_color == address(p) + (node->__rb_parent_color & 1) by { close(); }
                    let { metadata: n_size, right: n_right, left: n_left } = unfold(focus);
                    have separate(memory(g->__rb_parent_color), memory(node->__rb_parent_color)) by close();
                    have g != node by close();
                    let focus = fold(sized_at(node), { model: SizedTree::Node(node, p, Color::Red, nv, SizedTree::Empty, SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right)), metadata: n_size, right: n_right, left: n_left });
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
                    let loop_parent = fold(mirrored_context_double_middle_node_frame(p, g), { color: Color::Red, word: p->__rb_parent_color, right: p->rb_right, left: p->rb_left });
                    let loop_grandparent = fold(mirrored_context_double_middle_node_frame(g, above), { color: Color::Black, word: g->__rb_parent_color, right: g->rb_right, left: g->rb_left });
                    step(); step(); step(); step(); step(); step(); step();
                    unfold(loop_grandparent);
                    have gparent == g by close();
                    have parent == p by close();
                    let grandparent_tag = fold(mirrored_context_double_middle_tag(g, above), { color: Color::Black, word: g->__rb_parent_color });
                    let grandparent_right = fold(mirrored_context_double_middle_link(&g->rb_right), { child: g->rb_right });
                    let grandparent_left = fold(mirrored_context_double_middle_link(&g->rb_left), { child: g->rb_left });
                    step(); step(); step(); step();
                    step(); // Load the inner pivot after the mirrored uncle read.
                    unfold(loop_parent);
                    have p->rb_left == node by close();
                    have tmp == node by close();
                    step();
                    let { metadata: n_size, right: n_right, left: n_left } = unfold(focus);
                    unfold(n_left);
                    let { metadata: m_size, right: m_right, left: m_left } = unfold(n_right);
                    have node->rb_right == m by { close(); }
                    have m != 0 by { close(); }
                    have separate(memory(p->__rb_parent_color), memory(m->__rb_parent_color)) by { close(); }
                    have m != p by { close(); }
                    have to_integer(mv) == 1 + to_integer(sized_value(middle_left)) + to_integer(sized_value(middle_right)) by { close(); }
                    let n_right = fold(sized_recompute_at(m), { model: SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right), metadata: m_size, right: m_right, left: m_left });
                    have node->rb_left == 0 by close();
                    let node_tag = fold(mirrored_context_double_middle_tag(node, p), { color: Color::Red, word: node->__rb_parent_color });
                    let parent_tag = fold(mirrored_context_double_middle_tag(p, g), { color: Color::Red, word: p->__rb_parent_color });
                    let outer_left = fold(mirrored_context_double_middle_link(&node->rb_left), { child: node->rb_left });
                    let parent_right = fold(mirrored_context_double_middle_link(&p->rb_right), { child: p->rb_right });
                    step(); // Read the transferred subtree.
                    have tmp == m by close();
                    step(); // Install it as the parent's left child.
                    have p->rb_left == m by close();
                    let parent_left = fold(mirrored_context_double_middle_link(&p->rb_left), { child: m });
                    step(); // Put the old parent under the pivot.
                    have node->rb_right == p by close();
                    let inner_right = fold(mirrored_context_double_middle_link(&node->rb_right), { child: p });
                    step(); // Enter the nonnull transferred-child branch.
                    unfold(sized_root_color_bit(SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right)));
                    have 1 == sized_root_color_bit(n_right.model) by close();
                    let { after: dirty_middle } = step(insert::rb_set_parent_color, { tree: n_right });
                    unfold(sized_reparent(SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right), p));
                    have dirty_middle.model == SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right) by close();
                    let { metadata: m_size, right: m_right, left: m_left } = unfold(dirty_middle);
                    let p_left = fold(sized_at(m), { model: SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), metadata: m_size, right: m_right, left: m_left });
                    unfold(parent_tag); unfold(parent_right); unfold(parent_left);
                    have p->rb_left == m by close();
                    have sized_parent_is(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), p) == 1 by {
                        unfold(sized_parent_is(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), p)); normalize();
                    }
                    let before_parent_update = fold(sized_recompute_at(p), { model: SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far), metadata: p_size, right: p_right, left: p_left });
                    unfold(sized_root_color_bit(SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far)));
                    have 0 == sized_root_color_bit(before_parent_update.model) by close();
                    let { after: demoted } = step(insert::rb_set_parent_color, { tree: before_parent_update });
                    unfold(sized_reparent(SizedTree::Node(p, g, Color::Red, pv, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far), node));
                    have demoted.model == SizedTree::Node(p, node, Color::Red, pv, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far) by close();
                    unfold(outer_left); unfold(inner_right); unfold(node_tag);
                    have node->rb_left == 0 by close();
                    have node->rb_right == p by close();
                    let other = fold(sized_at(0), { model: SizedTree::Empty });
                    have sized_parent_is(SizedTree::Node(p, node, Color::Red, pv, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far), node) == 1 by { unfold(sized_parent_is(SizedTree::Node(p, node, Color::Red, pv, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far), node)); normalize(); }
                    have sized_parent_is(SizedTree::Empty, node) == 1 by { unfold(sized_parent_is(SizedTree::Empty, node)); normalize(); }
                    unfold(sized_value(SizedTree::Node(p, node, Color::Red, pv, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far)));
                    unfold(sized_right(SizedTree::Node(p, node, Color::Red, pv, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far)));
                    unfold(sized_left(SizedTree::Node(p, node, Color::Red, pv, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far)));
                    unfold(sized_value(SizedTree::Empty));
                    have to_integer(sized_value(SizedTree::Node(p, node, Color::Red, pv, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far))) == 2 + to_integer(sized_value(sized_left(SizedTree::Node(p, node, Color::Red, pv, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far)))) + to_integer(sized_value(sized_right(SizedTree::Node(p, node, Color::Red, pv, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far)))) + to_integer(sized_value(SizedTree::Empty)) by {
                        rewrite(sized_value(SizedTree::Node(p, node, Color::Red, pv, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far)), pv);
                        rewrite(sized_right(SizedTree::Node(p, node, Color::Red, pv, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far)), far);
                        rewrite(sized_left(SizedTree::Node(p, node, Color::Red, pv, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far)), SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right));
                        rewrite(sized_value(SizedTree::Empty), 0);
                        close() using {
                            to_integer(pv) == 2 + to_integer(sized_value(far)) + to_integer(sized_value(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)));
                        };
                    }
                    let rotated = fold(sized_rotation_right_at(p, node), { model: SizedTree::Node(node, p, Color::Red, nv, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, pv, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far)), metadata: n_size, demoted: demoted, other: other });
                    unfold(sized_right(SizedTree::Node(node, p, Color::Red, nv, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, pv, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far))));
                    have -2147483648 <= to_integer(pv);
                    have to_integer(pv) <= 2147483647;
                    have 0 <= to_integer(sized_value(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))) by {
                        close() using {
                            0 <= to_integer(sized_value(SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right)));
                            to_integer(sized_value(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))) == to_integer(mv);
                            to_integer(sized_value(SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right))) == to_integer(mv);
                        };
                    }
                    have 1 + to_integer(sized_value(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))) + to_integer(sized_value(far)) <= 2147483647 by {
                        close() using {
                            to_integer(pv) == 2 + to_integer(sized_value(far)) + to_integer(sized_value(SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right)));
                            to_integer(pv) <= 2147483647;
                            to_integer(sized_value(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right))) == to_integer(mv);
                            to_integer(sized_value(SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right))) == to_integer(mv);
                        };
                    }
                    apply(size_children_fit(sized_value(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)), sized_value(far)));
                    let { checked: first } = step(RotateTreeRight, { tree: rotated });
                    let { checked: first } = certify_size(node, { tree: first });
                    apply(sized_mirrored_double_middle_valid(p, node, pv, far, SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right)));
                    unfold(sized_reparent(SizedTree::Node(m, node, Color::Black, mv, middle_left, middle_right), p));
                    unfold(sized_recolor(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), Color::Black));
                    have sized_shape(first.model) == sized_shape(SizedTree::Node(node, p, Color::Red, pv, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far))) by {
                        rewrite(sized_shape(first.model), sized_shape(SizedTree::Node(node, p, Color::Red, nv, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, pv, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far))));
                        unfold(sized_shape(SizedTree::Node(node, p, Color::Red, nv, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, pv, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far))));
                        unfold(sized_shape(SizedTree::Node(node, p, Color::Red, pv, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far))));
                        unfold(sized_shape(SizedTree::Node(p, node, Color::Red, pv, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far)));
                        unfold(sized_shape(SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far))); normalize();
                    }
                    apply(sized_model_unique(first.model, SizedTree::Node(node, p, Color::Red, pv, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far))));
                    have first.model == SizedTree::Node(node, p, Color::Red, pv, SizedTree::Empty, SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far)) by { close(); }
                    let { metadata: n_size, right: parent_subtree, left: outer_empty } = unfold(first);
                    unfold(outer_empty);
                    let { metadata: p_size, right: far_subtree, left: middle_subtree } = unfold(parent_subtree);
                    have node->rb_right == p by close();
                    let parent_subtree = fold(sized_at(p), { model: SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far), metadata: p_size, right: far_subtree, left: middle_subtree });
                    let kept_right = fold(mirrored_context_double_middle_link(&node->rb_right), { child: p });
                    unfold(grandparent_right);
                    step(); step(); step(); // Select the pivot and store the null outer middle child.
                    have parent == node by close();
                    have g->rb_right == 0 by close();
                    let kept_g_right = fold(mirrored_context_double_middle_link(&g->rb_right), { child: g->rb_right });
                    step(); // Put the grandparent under the promoted pivot.
                    have node->rb_left == g by close();
                    let kept_left = fold(mirrored_context_double_middle_link(&node->rb_left), { child: node->rb_left });
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
                    unfold(kept_g_right); unfold(grandparent_left);
                    unfold(kept_right); unfold(kept_left);
                    have g->rb_right == 0 by close();
                    have g->rb_left == 0 by close();
                    let g_right = fold(sized_at(0), { model: SizedTree::Empty });
                    let g_left = fold(sized_at(0), { model: SizedTree::Empty });
                    let demoted = fold(sized_recompute_at(g), {
                        model: SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty),
                        metadata: g_size, right: g_right, left: g_left
                    });
                    have node->rb_right == p by close();
                    have node->rb_left == g by close();
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
                    have sized_parent_is(SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far), node) == 1 by {
                        unfold(sized_parent_is(SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far), node)); normalize();
                    }
                    have sized_parent_is(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty), node) == 1 by {
                        unfold(sized_parent_is(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty), node)); normalize();
                    }
                    unfold(sized_value(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)));
                    unfold(sized_right(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)));
                    unfold(sized_left(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)));
                    unfold(sized_value(SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far)));
                    have to_integer(sized_value(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty))) == 2 + to_integer(sized_value(sized_right(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)))) + to_integer(sized_value(sized_left(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)))) + to_integer(sized_value(SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far))) by {
                        rewrite(sized_value(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)), gv);
                        rewrite(sized_right(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty);
                        rewrite(sized_left(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far)), pv - 1);
                        rewrite(sized_value(SizedTree::Empty), 0);
                        close() using {
                            to_integer(gv) == 1 + to_integer(pv);
                            to_integer(pv - 1) == to_integer(pv) - to_integer(1);
                        };
                    }
                    let second_rotated = fold(sized_rotation_left_at(g, node), {
                        model: SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far)),
                        metadata: n_size, other: parent_subtree, demoted: demoted
                    });
                    unfold(sized_left(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far))));
                    unfold(sized_right(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)));
                    unfold(sized_left(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)));
                    unfold(sized_value(SizedTree::Empty));
                    have 0 <= sized_value(sized_right(sized_left(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far))))) by {
                        rewrite(sized_left(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far))), SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty));
                        rewrite(sized_right(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty), 0); normalize();
                    }
                    have 0 <= sized_value(sized_left(sized_left(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far))))) by {
                        rewrite(sized_left(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far))), SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty));
                        rewrite(sized_left(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty), 0); normalize();
                    }
                    have sized_value(sized_left(sized_left(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far))))) <= 2147483646 by {
                        rewrite(sized_left(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far))), SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty));
                        rewrite(sized_left(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty), 0); normalize();
                    }
                    have sized_value(sized_right(sized_left(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far))))) <= 2147483646 - sized_value(sized_left(sized_left(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far))))) by {
                        rewrite(sized_left(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far))), SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty));
                        rewrite(sized_right(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty);
                        rewrite(sized_left(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty), 0); normalize();
                    }
                    let { checked: second } = step(RotateTreeLeft, { tree: second_rotated });
                    have sized_shape(second.model) == sized_mirrored_context_double_middle_subtree_after(g, p, node, above, pv, gv, far, m, mv, middle_right, middle_left, nv) by {
                        rewrite(sized_shape(second.model), sized_shape(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far))));
                        unfold(sized_shape(SizedTree::Node(node, above, Color::Black, pv, SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far))));
                        unfold(sized_shape(SizedTree::Node(p, node, Color::Red, pv - 1, SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right), far)));
                        unfold(sized_shape(SizedTree::Node(g, node, Color::Red, gv, SizedTree::Empty, SizedTree::Empty)));
                        unfold(sized_shape(SizedTree::Empty));
                        unfold(sized_mirrored_context_double_middle_subtree_after(g, p, node, above, pv, gv, far, m, mv, middle_right, middle_left, nv)); normalize();
                    }
                    have rb_subtree_size(sized_mirrored_context_double_middle_subtree_after(g, p, node, above, pv, gv, far, m, mv, middle_right, middle_left, nv)) == to_integer(gv) by {
                        unfold(sized_mirrored_context_double_middle_subtree_after(g, p, node, above, pv, gv, far, m, mv, middle_right, middle_left, nv));
                        unfold(rb_subtree_size(RbTree::Node(node, above, Color::Black, RbTree::Node(g, node, Color::Red, RbTree::Empty, RbTree::Empty), RbTree::Node(p, node, Color::Red, sized_shape(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)), sized_shape(far)))));
                        unfold(rb_subtree_size(RbTree::Node(p, node, Color::Red, sized_shape(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)), sized_shape(far)))); unfold(rb_subtree_size(RbTree::Node(g, node, Color::Red, RbTree::Empty, RbTree::Empty)));
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
                        rewrite(sized_shape(second.model), sized_mirrored_context_double_middle_subtree_after(g, p, node, above, pv, gv, far, m, mv, middle_right, middle_left, nv)); close();
                    }
                    have sized_value(second.model) == gv;
                    apply(sized_parent_is_shape(second.model, above));
                    have rb_parent_is(sized_shape(second.model), above) == 1 by {
                        rewrite(sized_shape(second.model), sized_mirrored_context_double_middle_subtree_after(g, p, node, above, pv, gv, far, m, mv, middle_right, middle_left, nv));
                        unfold(sized_mirrored_context_double_middle_subtree_after(g, p, node, above, pv, gv, far, m, mv, middle_right, middle_left, nv));
                        unfold(rb_parent_is(RbTree::Node(node, above, Color::Black, RbTree::Node(g, node, Color::Red, RbTree::Empty, RbTree::Empty), RbTree::Node(p, node, Color::Red, sized_shape(SizedTree::Node(m, p, Color::Black, mv, middle_left, middle_right)), sized_shape(far))), above)); normalize();
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
                    let state = fold(sized_insert_mirrored_context_double_middle_subtree_at(node, root), {
                        phase: SizedInsertMirroredContextDoubleMiddleSubtreePhase::After(g, p, above, pv, gv, far, m, mv, middle_right, middle_left, nv), model: at(before_restore, second.model), context: old(state.context), whole_model: whole.model,
                        whole: whole
                    });
                    have state.context == old(state.context) by { close(); }
                    have state.whole_model == sized_plug(old(state.context), state.model) by { close(); }
                    have state.phase == sized_mirrored_context_double_middle_subtree_finish(old(state.phase)) by {
                        unfold(sized_mirrored_context_double_middle_subtree_finish(SizedInsertMirroredContextDoubleMiddleSubtreePhase::Before(g, p, above, pv, gv, far, m, mv, middle_right, middle_left, nv))); close();
                    }
                    have sized_shape(state.model) == sized_mirrored_context_double_middle_subtree_expected(old(state.phase), node) by {
                        rewrite(old(state.phase), SizedInsertMirroredContextDoubleMiddleSubtreePhase::Before(g, p, above, pv, gv, far, m, mv, middle_right, middle_left, nv));
                        unfold(sized_mirrored_context_double_middle_subtree_expected(SizedInsertMirroredContextDoubleMiddleSubtreePhase::Before(g, p, above, pv, gv, far, m, mv, middle_right, middle_left, nv), node)); close();
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
    requires RotateTreeRight(augment_rotate);
    owns state: sized_insert_mirrored_context_double_middle_subtree_at(node, root);
    requires sized_mirrored_context_double_middle_subtree_pending(state.phase) == 1;
    requires node->rb_left != node;
    requires node->rb_right != node;
    ensures state.context == old(state.context);
    ensures state.whole_model == sized_plug(old(state.context), state.model);
    ensures state.phase == sized_mirrored_context_double_middle_subtree_finish(old(state.phase));
    ensures sized_shape(state.model) == sized_mirrored_context_double_middle_subtree_expected(old(state.phase), node);
} by {
    step(insert::__rb_insert, { state: state });
}

void insert::rb_insert_augmented(struct rb_node* node, struct rb_root* root,
                         const struct rb_augment_callbacks* augment) {
    views augment->rotate;
    requires RotateTreeLeft(augment->rotate);
    requires RotateTreeRight(augment->rotate);
    owns state: sized_insert_mirrored_context_double_middle_subtree_at(node, root);
    requires sized_mirrored_context_double_middle_subtree_pending(state.phase) == 1;
    requires node->rb_left != node;
    requires node->rb_right != node;
    ensures state.context == old(state.context);
    ensures state.whole_model == sized_plug(old(state.context), state.model);
    ensures state.phase == sized_mirrored_context_double_middle_subtree_finish(old(state.phase));
    ensures sized_shape(state.model) == sized_mirrored_context_double_middle_subtree_expected(old(state.phase), node);
} by {
    have separate(state, memory(augment->rotate)) by close();
    step(insert::__rb_insert_augmented, { state: state });
}
