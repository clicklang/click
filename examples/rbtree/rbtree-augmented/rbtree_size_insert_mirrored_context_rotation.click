// Writable right-right insertion rotation with an owned outer ancestor context.
verifying "rb_insert_augmented.c" as insert;
verifying "rbtree_size_rotate.c";
verifying "rbtree_size_copy.c";
verifying "rbtree_size_compute.c";
import "rbtree_size_rotate_model.click";
import "rbtree_size_rotate_set_parents.click";

spec enum SizedInsertMirroredContextThreePhase {
    Before(struct rb_node*, struct rb_node*, struct rb_node*),
    After(struct rb_node*, struct rb_node*, struct rb_node*),
}

function sized_mirrored_context_three_pending(phase: SizedInsertMirroredContextThreePhase) -> int32 {
    match phase {
        SizedInsertMirroredContextThreePhase::Before(g, p, above) => 1,
        SizedInsertMirroredContextThreePhase::After(g, p, above) => 0,
    }
}

function sized_mirrored_context_three_finish(phase: SizedInsertMirroredContextThreePhase) -> SizedInsertMirroredContextThreePhase {
    match phase {
        SizedInsertMirroredContextThreePhase::Before(g, p, above) => SizedInsertMirroredContextThreePhase::After(g, p, above),
        SizedInsertMirroredContextThreePhase::After(g, p, above) => SizedInsertMirroredContextThreePhase::After(g, p, above),
    }
}

function sized_mirrored_context_three_before(g: struct rb_node*, p: struct rb_node*, n: struct rb_node*, above: struct rb_node*) -> SizedTree {
    SizedTree::Node(g, above, Color::Black, 3, SizedTree::Empty, SizedTree::Node(p, g, Color::Red, 2, SizedTree::Empty, SizedTree::Node(n, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty)))
}

function sized_mirrored_context_three_after(g: struct rb_node*, p: struct rb_node*, n: struct rb_node*, above: struct rb_node*) -> RbTree {
    RbTree::Node(p, above, Color::Black, RbTree::Node(g, p, Color::Red, RbTree::Empty, RbTree::Empty), RbTree::Node(n, p, Color::Red, RbTree::Empty, RbTree::Empty))
}

function sized_mirrored_context_three_expected(phase: SizedInsertMirroredContextThreePhase, node: struct rb_node*) -> RbTree {
    match phase {
        SizedInsertMirroredContextThreePhase::Before(g, p, above) => sized_mirrored_context_three_after(g, p, node, above),
        SizedInsertMirroredContextThreePhase::After(g, p, above) => sized_mirrored_context_three_after(g, p, node, above),
    }
}


resource sized_insert_mirrored_context_three_at(node: struct rb_node*, root: struct rb_root*) {
    field phase: SizedInsertMirroredContextThreePhase;
    field model: SizedTree;
    field context: SizedContext;
    field whole_model: SizedTree;
    match phase {
        SizedInsertMirroredContextThreePhase::Before(g, p, above) => {
            owns link: sized_link_at(g, root, 3);
            owns tree: sized_at(g);
            fact link.model == context;
            fact above == sized_context_parent(context, 0);
            fact tree.model == model;
            fact model == sized_mirrored_context_three_before(g, p, node, above);
        },
        SizedInsertMirroredContextThreePhase::After(g, p, above) => {
            owns root->rb_node;
            owns whole: sized_at(root->rb_node);
            fact above == sized_context_parent(context, 0);
            fact whole.model == whole_model;
            fact sized_parent_is(whole.model, 0) == 1;
        },
    }
}

// Read-only steps retain child links and the complete tagged-parent relationship.
resource mirrored_context_rotation_parent_frame(p: struct rb_node*, node: struct rb_node*, up: struct rb_node*) {
    field color: Color;
    field word: uint64;
    field left: int32*;
    owns p->__rb_parent_color;
    fact p->__rb_parent_color == word;
    fact p->__rb_parent_color == address(up) + (p->__rb_parent_color & 1);
    fact ((p->__rb_parent_color & ~3) as (struct rb_node*)) == up;
    fact (p->__rb_parent_color & 1) == color_bit(color);
    owns p->rb_right;
    owns p->rb_left;
    fact p->rb_right == node;
    fact p->rb_right != p;
    fact p->rb_left == left;
    fact p->rb_left != p;
}

resource mirrored_context_rotation_tag(p: struct rb_node*, up: struct rb_node*) {
    field color: Color;
    field word: uint64;
    owns p->__rb_parent_color;
    fact p->__rb_parent_color == word;
    fact p->__rb_parent_color == address(up) + (p->__rb_parent_color & 1);
    fact ((p->__rb_parent_color & ~3) as (struct rb_node*)) == up;
    fact (p->__rb_parent_color & 1) == color_bit(color);
}

resource mirrored_context_rotation_link(slot: struct rb_node**) {
    field child: int32*;
    owns *slot;
    fact *slot == child;
}

void insert::__rb_insert(struct rb_node* node, struct rb_root* root,
                  void (*augment_rotate)(struct rb_node*, struct rb_node*)) {
    requires RotateTreeLeft(augment_rotate);
    owns state: sized_insert_mirrored_context_three_at(node, root);
    requires sized_mirrored_context_three_pending(state.phase) == 1;
    ensures state.context == old(state.context);
    ensures state.whole_model == sized_plug(old(state.context), state.model);
    ensures state.phase == sized_mirrored_context_three_finish(old(state.phase));
    ensures sized_shape(state.model) == sized_mirrored_context_three_expected(old(state.phase), node);
} by {
    match state.phase {
        SizedInsertMirroredContextThreePhase::After(g, p, above) => {
            have sized_mirrored_context_three_pending(state.phase) != 1 by {
                rewrite(state.phase, SizedInsertMirroredContextThreePhase::After(g, p, above));
                unfold(sized_mirrored_context_three_pending(SizedInsertMirroredContextThreePhase::After(g, p, above))); close();
            }
            close();
        },
        SizedInsertMirroredContextThreePhase::Before(g, p, above) => {
            let { tree: tree, link: link } = unfold(state);
            unfold(sized_mirrored_context_three_before(g, p, node, above));
            have tree.model == SizedTree::Node(g, above, Color::Black, 3, SizedTree::Empty, SizedTree::Node(p, g, Color::Red, 2, SizedTree::Empty, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))) by {
                rewrite(tree.model, sized_mirrored_context_three_before(g, p, node, above));
                unfold(sized_mirrored_context_three_before(g, p, node, above)); close();
            }
            let { metadata: g_size, right: parent_tree, left: g_left } = unfold(tree);
            let { metadata: p_size, right: focus, left: p_left } = unfold(parent_tree);
            let { metadata: n_size, right: n_left, left: n_right } = unfold(focus);
            unfold(color_bit(Color::Red));
            have (node->__rb_parent_color & 1) == 0 by {
                rewrite((node->__rb_parent_color & 1), color_bit(Color::Red));
                rewrite(color_bit(Color::Red), 0); close();
            }
            have node->__rb_parent_color == address(p) by {
                rewrite(node->__rb_parent_color, address(p) + (node->__rb_parent_color & 1));
                rewrite((node->__rb_parent_color & 1), 0); close();
            }
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
            let initial_parent_frame = fold(mirrored_context_rotation_parent_frame(p, node, g), { color: Color::Red, left: p->rb_left, word: p->__rb_parent_color });
            let initial_grandparent_frame = fold(mirrored_context_rotation_parent_frame(g, p, above), { color: Color::Black, left: g->rb_left, word: g->__rb_parent_color });
            have node == g->rb_right->rb_right by close();
            unfold(n_left); unfold(n_right);
            have node->rb_left == 0 by {
                rewrite(node, g->rb_right->rb_right);
                close();
            }
            have node->rb_right == 0 by {
                rewrite(node, g->rb_right->rb_right);
                close();
            }
            step(); step(); step(); step();
            unfold(initial_grandparent_frame);
            unfold(initial_parent_frame);
            let n_left = fold(sized_at(0), { model: SizedTree::Empty });
            let n_right = fold(sized_at(0), { model: SizedTree::Empty });
            let focus = fold(sized_at(node), { model: SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), metadata: n_size, right: n_left, left: n_right });
            have p->rb_right == node by { close(); }
            have p->rb_right != p by {
                close();
            }
            have p->rb_left != p by {
                close();
            }
            let parent_tree = fold(sized_at(p), { model: SizedTree::Node(p, g, Color::Red, 2, SizedTree::Empty, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty)), metadata: p_size, right: focus, left: p_left });
            have ((g->__rb_parent_color & ~3) as (struct rb_node*)) == above by close();
            let tree = fold(sized_at(g), { model: SizedTree::Node(g, above, Color::Black, 3, SizedTree::Empty, SizedTree::Node(p, g, Color::Red, 2, SizedTree::Empty, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))), metadata: g_size, right: parent_tree, left: g_left });
            have tree.model == old(state.model) by close();
            let state = fold(sized_insert_mirrored_context_three_at(node, root), { phase: SizedInsertMirroredContextThreePhase::Before(g, p, above), model: old(state.model), context: old(state.context), whole_model: old(state.whole_model), tree: tree, link: link });
            step(); // Declare tmp before entering the C loop.
            loop {
                owns state: sized_insert_mirrored_context_three_at(node, root);
                decreases 0;
                invariant node == old(node);
                invariant parent == p;
                invariant state.context == old(state.context);
                invariant p == old(g->rb_right);
                invariant state.phase == SizedInsertMirroredContextThreePhase::Before(g, p, above);
                invariant old(state.phase) == SizedInsertMirroredContextThreePhase::Before(g, p, above);
                invariant state.model == sized_mirrored_context_three_before(g, p, node, above);
                initialize by close();
                maintain by {
                    let { tree: loop_tree, link: link } = unfold(state);
                    unfold(sized_mirrored_context_three_before(g, p, node, above));
                    have loop_tree.model == SizedTree::Node(g, above, Color::Black, 3, SizedTree::Empty, SizedTree::Node(p, g, Color::Red, 2, SizedTree::Empty, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))) by {
                        rewrite(loop_tree.model, sized_mirrored_context_three_before(g, p, node, above));
                        unfold(sized_mirrored_context_three_before(g, p, node, above)); close();
                    }
                    let { metadata: g_size, right: parent_tree, left: g_left } = unfold(loop_tree);
                    let { metadata: p_size, right: focus, left: p_left } = unfold(parent_tree);
                    unfold(g_left); unfold(p_left);
                    let { metadata: n_size, right: n_left, left: n_right } = unfold(focus);
                    let focus = fold(sized_at(node), { model: SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), metadata: n_size, right: n_left, left: n_right });
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
                    have g->rb_right == p by close();
                    have g->rb_right->rb_left == 0 by close();
                    have p->rb_left == 0 by { rewrite(p, g->rb_right); close(); }
                    // These steps only read nodes and assign C locals.
                    let loop_parent_frame = fold(mirrored_context_rotation_parent_frame(p, node, g), { color: Color::Red, left: p->rb_left, word: p->__rb_parent_color });
                    let loop_grandparent_frame = fold(mirrored_context_rotation_parent_frame(g, p, above), { color: Color::Black, left: g->rb_left, word: g->__rb_parent_color });
                    step(); step(); step(); step(); step(); step(); step(); step();
                    unfold(loop_grandparent_frame);
                    unfold(loop_parent_frame);
                    have gparent == g by { close(); }
                    have parent == p by { close(); }
                    have p->rb_right == node by close();
                    have parent->rb_right == node by { rewrite(parent, p); close(); }
                    have p->rb_left == 0 by close();
                    have parent->rb_left == 0 by { rewrite(parent, p); close(); }
                    have g->rb_left == 0 by close();
                    let rotating_tag = fold(mirrored_context_rotation_tag(g, above), { color: Color::Black, word: g->__rb_parent_color });
                    let kept_g_left = fold(mirrored_context_rotation_link(&g->rb_left), { child: g->rb_left });
                    let kept_p_right = fold(mirrored_context_rotation_link(&p->rb_right), { child: p->rb_right });
                    step(); step(); step();
                    have tmp == 0 by close();
                    have node != 0 by close();
                    step(); step(); step();
                    step(); // Store the null middle child in gparent->rb_right.
                    have g->rb_right == 0 by close();
                    let kept_g_right = fold(mirrored_context_rotation_link(&g->rb_right), { child: g->rb_right });
                    step(); // Put the old grandparent under the promoted parent.
                    have p->rb_left == g by close();
                    let kept_p_left = fold(mirrored_context_rotation_link(&p->rb_left), { child: p->rb_left });
                    step(); step(); // The middle child is null.
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
                    let g_size = fold(size_metadata(g), { value: 3 });
                    unfold(kept_g_right);
                    unfold(kept_g_left);
                    unfold(kept_p_right);
                    unfold(kept_p_left);
                    have g->rb_right == 0 by close();
                    have g->rb_left == 0 by close();
                    let p_left = fold(sized_at(0), { model: SizedTree::Empty });
                    let g_left = fold(sized_at(0), { model: SizedTree::Empty });
                    let demoted = fold(sized_recompute_at(g), {
                        model: SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty),
                        metadata: g_size, right: p_left, left: g_left
                    });
                    have p->rb_right == node by close();
                    have p->rb_left == g by close();
                    have parent == p by close();
                    have p->__rb_parent_color == at(before_parent_update, g->__rb_parent_color) by { close(); }
                    have p->__rb_parent_color == address(above) + (p->__rb_parent_color & 1) by {
                        rewrite(p->__rb_parent_color, at(before_parent_update, g->__rb_parent_color));
                        close();
                    }
                    have (p->__rb_parent_color & 1) == color_bit(Color::Black) by {
                        rewrite(p->__rb_parent_color, at(before_parent_update, g->__rb_parent_color));
                        close();
                    }
                    have sized_parent_is(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), p) == 1 by {
                        unfold(sized_parent_is(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), p)); close();
                    }
                    have sized_parent_is(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), p) == 1 by {
                        unfold(sized_parent_is(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), p)); close();
                    }
                    have to_integer(sized_value(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))) == 2 + to_integer(sized_value(sized_left(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)))) + to_integer(sized_value(sized_right(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)))) + to_integer(sized_value(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))) by {
                        unfold(sized_value(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)));
                        unfold(sized_right(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)));
                        unfold(sized_left(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)));
                        unfold(sized_value(SizedTree::Empty));
                        unfold(sized_value(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))); close();
                    }
                    let rotated = fold(sized_rotation_left_at(g, p), {
                        model: SizedTree::Node(p, above, Color::Black, 2, SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty)),
                        metadata: p_size, other: focus, demoted: demoted
                    });
                    unfold(sized_left(SizedTree::Node(p, above, Color::Black, 2, SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))));
                    unfold(sized_right(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)));
                    unfold(sized_left(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)));
                    unfold(sized_value(SizedTree::Empty));
                    have 0 <= sized_value(sized_right(sized_left(SizedTree::Node(p, above, Color::Black, 2, SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))))) by {
                        rewrite(sized_left(SizedTree::Node(p, above, Color::Black, 2, SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))), SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty));
                        rewrite(sized_right(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty), 0); close();
                    }
                    have 0 <= sized_value(sized_left(sized_left(SizedTree::Node(p, above, Color::Black, 2, SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))))) by {
                        rewrite(sized_left(SizedTree::Node(p, above, Color::Black, 2, SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))), SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty));
                        rewrite(sized_left(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty), 0); close();
                    }
                    have sized_value(sized_left(sized_left(SizedTree::Node(p, above, Color::Black, 2, SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))))) <= 2147483646 by {
                        rewrite(sized_left(SizedTree::Node(p, above, Color::Black, 2, SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))), SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty));
                        rewrite(sized_left(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty), 0); close();
                    }
                    have sized_value(sized_right(sized_left(SizedTree::Node(p, above, Color::Black, 2, SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))))) <= 2147483646 - sized_value(sized_left(sized_left(SizedTree::Node(p, above, Color::Black, 2, SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))))) by {
                        rewrite(sized_left(SizedTree::Node(p, above, Color::Black, 2, SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))), SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty));
                        rewrite(sized_right(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty);
                        rewrite(sized_left(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)), SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty), 0); close();
                    }
                    let { checked: checked } = step(RotateTreeLeft, { tree: rotated });
                    have sized_shape(checked.model) == sized_mirrored_context_three_after(g, p, node, above) by {
                        rewrite(sized_shape(checked.model), sized_shape(SizedTree::Node(p, above, Color::Black, 2, SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))));
                        unfold(sized_shape(SizedTree::Node(p, above, Color::Black, 2, SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))));
                        unfold(sized_shape(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty)));
                        unfold(sized_shape(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)));
                        unfold(sized_shape(SizedTree::Empty));
                        unfold(sized_mirrored_context_three_after(g, p, node, above)); close();
                    }
                    have rb_subtree_size(sized_mirrored_context_three_after(g, p, node, above)) == 3 by {
                        unfold(sized_mirrored_context_three_after(g, p, node, above));
                        unfold(rb_subtree_size(RbTree::Node(p, above, Color::Black, RbTree::Node(g, p, Color::Red, RbTree::Empty, RbTree::Empty), RbTree::Node(node, p, Color::Red, RbTree::Empty, RbTree::Empty))));
                        unfold(rb_subtree_size(RbTree::Node(node, p, Color::Red, RbTree::Empty, RbTree::Empty)));
                        unfold(rb_subtree_size(RbTree::Node(g, p, Color::Red, RbTree::Empty, RbTree::Empty)));
                        unfold(rb_subtree_size(RbTree::Empty)); close();
                    }
                    have to_integer(sized_value(checked.model)) == 3 by {
                        rewrite(to_integer(sized_value(checked.model)), rb_subtree_size(sized_shape(checked.model)));
                        rewrite(sized_shape(checked.model), sized_mirrored_context_three_after(g, p, node, above));
                        close();
                    }
                    have sized_value(checked.model) == 3;
                    apply(sized_parent_is_shape(checked.model, above));
                    have rb_parent_is(sized_shape(checked.model), above) == 1 by {
                        rewrite(sized_shape(checked.model), sized_mirrored_context_three_after(g, p, node, above));
                        unfold(sized_mirrored_context_three_after(g, p, node, above));
                        unfold(rb_parent_is(RbTree::Node(p, above, Color::Black, RbTree::Node(g, p, Color::Red, RbTree::Empty, RbTree::Empty), RbTree::Node(node, p, Color::Red, RbTree::Empty, RbTree::Empty)), above)); close();
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
                    let { whole: whole } = restore_sized_context(p, root->rb_node, 0, 3, { path: path, sub: checked });
                    have whole.model == sized_plug(old(state.context), at(before_restore, checked.model)) by { close(); }
                    let state = fold(sized_insert_mirrored_context_three_at(node, root), {
                        phase: SizedInsertMirroredContextThreePhase::After(g, p, above), model: at(before_restore, checked.model), context: old(state.context), whole_model: whole.model,
                        whole: whole
                    });
                    have state.context == old(state.context) by { close(); }
                    have state.whole_model == sized_plug(old(state.context), state.model) by { close(); }
                    have state.phase == sized_mirrored_context_three_finish(old(state.phase)) by {
                        unfold(sized_mirrored_context_three_finish(SizedInsertMirroredContextThreePhase::Before(g, p, above))); close();
                    }
                    have sized_shape(state.model) == sized_mirrored_context_three_expected(old(state.phase), node) by {
                        rewrite(old(state.phase), SizedInsertMirroredContextThreePhase::Before(g, p, above));
                        unfold(sized_mirrored_context_three_expected(SizedInsertMirroredContextThreePhase::Before(g, p, above), node)); close();
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
    owns state: sized_insert_mirrored_context_three_at(node, root);
    requires sized_mirrored_context_three_pending(state.phase) == 1;
    ensures state.context == old(state.context);
    ensures state.whole_model == sized_plug(old(state.context), state.model);
    ensures state.phase == sized_mirrored_context_three_finish(old(state.phase));
    ensures sized_shape(state.model) == sized_mirrored_context_three_expected(old(state.phase), node);
} by {
    step(insert::__rb_insert, { state: state });
}

void insert::rb_insert_augmented(struct rb_node* node, struct rb_root* root,
                         const struct rb_augment_callbacks* augment) {
    views augment->rotate;
    requires RotateTreeLeft(augment->rotate);
    owns state: sized_insert_mirrored_context_three_at(node, root);
    requires sized_mirrored_context_three_pending(state.phase) == 1;
    ensures state.context == old(state.context);
    ensures state.whole_model == sized_plug(old(state.context), state.model);
    ensures state.phase == sized_mirrored_context_three_finish(old(state.phase));
    ensures sized_shape(state.model) == sized_mirrored_context_three_expected(old(state.phase), node);
} by {
    have separate(state, memory(augment->rotate)) by close();
    step(insert::__rb_insert_augmented, { state: state });
}
