// Writable left-left insertion rotation with an owned outer ancestor context.
verifying "rb_insert_augmented.c" as insert;
verifying "rbtree_size_rotate.c";
verifying "rbtree_size_copy.c";
verifying "rbtree_size_compute.c";
import "rbtree_size_rotate_model.click";
import "rbtree_size_rotate_set_parents.click";

spec enum SizedInsertContextThreePhase {
    Before(struct rb_node*, struct rb_node*, struct rb_node*),
    After(struct rb_node*, struct rb_node*, struct rb_node*),
}

function sized_context_three_pending(phase: SizedInsertContextThreePhase) -> int32 {
    match phase {
        SizedInsertContextThreePhase::Before(g, p, above) => 1,
        SizedInsertContextThreePhase::After(g, p, above) => 0,
    }
}

function sized_context_three_finish(phase: SizedInsertContextThreePhase) -> SizedInsertContextThreePhase {
    match phase {
        SizedInsertContextThreePhase::Before(g, p, above) => SizedInsertContextThreePhase::After(g, p, above),
        SizedInsertContextThreePhase::After(g, p, above) => SizedInsertContextThreePhase::After(g, p, above),
    }
}

function sized_context_three_before(g: struct rb_node*, p: struct rb_node*, n: struct rb_node*, above: struct rb_node*) -> SizedTree {
    SizedTree::Node(g, above, Color::Black, 3,
        SizedTree::Node(p, g, Color::Red, 2,
            SizedTree::Node(n, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty), SizedTree::Empty)
}

function sized_context_three_after(g: struct rb_node*, p: struct rb_node*, n: struct rb_node*, above: struct rb_node*) -> RbTree {
    RbTree::Node(p, above, Color::Black,
        RbTree::Node(n, p, Color::Red, RbTree::Empty, RbTree::Empty),
        RbTree::Node(g, p, Color::Red, RbTree::Empty, RbTree::Empty))
}

function sized_context_three_expected(phase: SizedInsertContextThreePhase, node: struct rb_node*) -> RbTree {
    match phase {
        SizedInsertContextThreePhase::Before(g, p, above) => sized_context_three_after(g, p, node, above),
        SizedInsertContextThreePhase::After(g, p, above) => sized_context_three_after(g, p, node, above),
    }
}


theorem sized_context_parent_word_black(ctx: SizedContext, parent: struct rb_node*, word: uint64) {
    requires parent == sized_context_parent(ctx, 0);
    requires word == address(parent) + 1;
    ensures sized_context_parent_word(ctx, word) == 1 by {
        match ctx {
            SizedContext::Top => {
                have parent == 0 by {
                    rewrite(parent == sized_context_parent(ctx, 0));
                    rewrite(ctx == SizedContext::Top);
                    unfold(sized_context_parent(SizedContext::Top, 0)); normalize();
                }
                have word == address(0) + 1 by {
                    rewrite(word == address(parent) + 1);
                    rewrite(parent == 0); normalize();
                }
                rewrite(ctx == SizedContext::Top);
                unfold(sized_context_parent_word(SizedContext::Top, word));
                normalize() using { word == address(0) + 1; }
            },
            SizedContext::Left(a, ancestor, color, count, sibling, up) => {
                have parent == a by {
                    rewrite(parent == sized_context_parent(ctx, 0));
                    rewrite(ctx == SizedContext::Left(a, ancestor, color, count, sibling, up));
                    unfold(sized_context_parent(SizedContext::Left(a, ancestor, color, count, sibling, up), 0)); normalize();
                }
                have word == address(a) + 1 by {
                    rewrite(a == parent); assumption();
                }
                rewrite(ctx == SizedContext::Left(a, ancestor, color, count, sibling, up));
                unfold(sized_context_parent_word(SizedContext::Left(a, ancestor, color, count, sibling, up), word));
                normalize() using { word == address(a) + 1; }
            },
            SizedContext::Right(a, ancestor, color, count, sibling, up) => {
                have parent == a by {
                    rewrite(parent == sized_context_parent(ctx, 0));
                    rewrite(ctx == SizedContext::Right(a, ancestor, color, count, sibling, up));
                    unfold(sized_context_parent(SizedContext::Right(a, ancestor, color, count, sibling, up), 0)); normalize();
                }
                have word == address(a) + 1 by {
                    rewrite(a == parent); assumption();
                }
                rewrite(ctx == SizedContext::Right(a, ancestor, color, count, sibling, up));
                unfold(sized_context_parent_word(SizedContext::Right(a, ancestor, color, count, sibling, up), word));
                normalize() using { word == address(a) + 1; }
            },
        }
    }
}

resource sized_insert_context_three_at(node: struct rb_node*, root: struct rb_root*) {
    field phase: SizedInsertContextThreePhase;
    field model: SizedTree;
    field context: SizedContext;
    field whole_model: SizedTree;
    match phase {
        SizedInsertContextThreePhase::Before(g, p, above) => {
            owns link: sized_link_at(g, root, 3);
            owns tree: sized_at(g);
            fact link.model == context;
            fact above == sized_context_parent(context, 0);
            fact tree.model == model;
            fact model == sized_context_three_before(g, p, node, above);
        },
        SizedInsertContextThreePhase::After(g, p, above) => {
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
    owns state: sized_insert_context_three_at(node, root);
    requires sized_context_three_pending(state.phase) == 1;
    ensures state.context == old(state.context);
    ensures state.whole_model == sized_plug(old(state.context), state.model);
    ensures state.phase == sized_context_three_finish(old(state.phase));
    ensures sized_shape(state.model) == sized_context_three_expected(old(state.phase), node);
} by {
    match state.phase {
        SizedInsertContextThreePhase::After(g, p, above) => {
            have sized_context_three_pending(state.phase) != 1 by {
                rewrite(state.phase == SizedInsertContextThreePhase::After(g, p, above));
                unfold(sized_context_three_pending(SizedInsertContextThreePhase::After(g, p, above))); normalize();
            }
            contradiction(sized_context_three_pending(state.phase) == 1);
        },
        SizedInsertContextThreePhase::Before(g, p, above) => {
            let { tree: tree, link: link } = unfold(state);
            unfold(sized_context_three_before(g, p, node, above));
            have tree.model == SizedTree::Node(g, above, Color::Black, 3,
                SizedTree::Node(p, g, Color::Red, 2,
                    SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty), SizedTree::Empty) by {
                rewrite(tree.model == sized_context_three_before(g, p, node, above));
                unfold(sized_context_three_before(g, p, node, above)); normalize();
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
            unfold(n_left); unfold(n_right);
            have node->rb_left == 0 by { assumption(); }
            have node->rb_right == 0 by { assumption(); }
            let n_left = fold(sized_at(node->rb_left), { model: SizedTree::Empty });
            let n_right = fold(sized_at(node->rb_right), { model: SizedTree::Empty });
            let focus = fold(sized_at(node), { model: SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty) }, { metadata: n_size, left: n_left, right: n_right });
            have p->rb_left == node by { assumption(); }
            have p->rb_left != p by {
                assumption();
            }
            have p->rb_right != p by {
                assumption();
            }
            let parent_tree = fold(sized_at(p), { model: SizedTree::Node(p, g, Color::Red, 2, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty) }, { metadata: p_size, left: focus, right: p_right });
            let tree = fold(sized_at(g), { model: old(state.model) }, { metadata: g_size, left: parent_tree, right: g_right });
            let state = fold(sized_insert_context_three_at(node, root), { phase: SizedInsertContextThreePhase::Before(g, p, above), model: old(state.model), context: old(state.context), whole_model: old(state.whole_model) }, { tree: tree, link: link });
            loop {
                owns state: sized_insert_context_three_at(node, root);
                decreases 0;
                invariant node == old(node);
                invariant parent == p;
                invariant state.context == old(state.context);
                invariant p == old(g->rb_left);
                invariant state.phase == SizedInsertContextThreePhase::Before(g, p, above);
                invariant old(state.phase) == SizedInsertContextThreePhase::Before(g, p, above);
                invariant state.model == sized_context_three_before(g, p, node, above);
                initialize by simp;
                preserve by {
                    let { tree: loop_tree, link: link } = unfold(state);
                    unfold(sized_context_three_before(g, p, node, above));
                    have loop_tree.model == SizedTree::Node(g, above, Color::Black, 3,
                        SizedTree::Node(p, g, Color::Red, 2,
                            SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty), SizedTree::Empty) by {
                        rewrite(loop_tree.model == sized_context_three_before(g, p, node, above));
                        unfold(sized_context_three_before(g, p, node, above)); normalize();
                    }
                    let { metadata: g_size, left: parent_tree, right: g_right } = unfold(loop_tree);
                    let { metadata: p_size, left: focus, right: p_right } = unfold(parent_tree);
                    unfold(g_right); unfold(p_right);
                    let { metadata: n_size, left: n_left, right: n_right } = unfold(focus);
                    let focus = fold(sized_at(node), { model: SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty) }, { metadata: n_size, left: n_left, right: n_right });
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
                    have tmp == 0 by { assumption(); }
                    have node != 0 by { assumption(); }
                    step(); step(); step();
                    mark after_left_write;
                    have at(after_left_write, g->rb_left == 0) by { assumption(); }
                    have separate(memory(g->rb_left), memory(parent->rb_right)) by { assumption(); }
                    step(); step(); step();
                    have gparent->__rb_parent_color == address(above) + 1 by { simp(); }
                    unfold(g_size);
                    have sized_context_parent_word(link.model, g->__rb_parent_color) == 1 by {
                        apply(sized_context_parent_word_black(link.model, above, g->__rb_parent_color));
                    }
                    have g->rb_left == 0 by {
                        transport(at(after_left_write, g->rb_left == 0), g->rb_left == 0) using {
                            at(after_left_write, g->rb_left == 0);
                            separate(memory(g->rb_left), memory(parent->rb_right));
                            at(before_link_writes, g->rb_left) == parent;
                        };
                    }
                    transport(at(before_link_writes, parent->rb_left == node), parent->rb_left == node);
                    have parent->rb_right == gparent by { simp(); }
                    mark before_parent_update;
                    have at(before_parent_update, g->rb_left == 0) by { assumption(); }
                    have at(before_parent_update, parent->rb_left == node) by { assumption(); }
                    have at(before_parent_update, parent->rb_right == gparent) by { assumption(); }
                    let { after: link } = step(insert::__rb_rotate_set_parents(g, p, root, 0), { c: link });
                    let g_size = fold(size_metadata(g), { value: 3 });
                    transport(at(before_parent_update, g->rb_left == 0), g->rb_left == 0);
                    let p_right = fold(sized_at(g->rb_left), { model: SizedTree::Empty });
                    have g->rb_right == 0 by { simp(); }
                    let g_right = fold(sized_at(g->rb_right), { model: SizedTree::Empty });
                    let demoted = fold(sized_recompute_at(g), {
                        model: SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)
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
                    have p->rb_right == g by {
                        rewrite(p == parent);
                        rewrite(g == gparent);
                        assumption();
                    }
                    have parent == p by { assumption(); }
                    have p->__rb_parent_color == at(before_parent_update, g->__rb_parent_color) by { simp(); }
                    have p->__rb_parent_color == address(above) + (p->__rb_parent_color & 1) by {
                        rewrite(p->__rb_parent_color == at(before_parent_update, g->__rb_parent_color));
                        assumption();
                    }
                    have (p->__rb_parent_color & 1) == color_bit(Color::Black) by {
                        rewrite(p->__rb_parent_color == at(before_parent_update, g->__rb_parent_color));
                        assumption();
                    }
                    have sized_parent_is(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), p) == 1 by {
                        unfold(sized_parent_is(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), p)); normalize();
                    }
                    have sized_parent_is(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), p) == 1 by {
                        unfold(sized_parent_is(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty), p)); normalize();
                    }
                    have to_integer(sized_value(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))) == 2 + to_integer(sized_value(sized_left(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)))) + to_integer(sized_value(sized_right(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)))) + to_integer(sized_value(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))) by {
                        unfold(sized_value(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)));
                        unfold(sized_left(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)));
                        unfold(sized_right(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)));
                        unfold(sized_value(SizedTree::Empty));
                        unfold(sized_value(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))); normalize();
                    }
                    let rotated = fold(sized_rotation_right_at(g, p), {
                        model: SizedTree::Node(p, above, Color::Black, 2,
                            SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty),
                            SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))
                    }, { metadata: p_size, other: focus, demoted: demoted });
                    unfold(sized_right(SizedTree::Node(p, above, Color::Black, 2, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))));
                    unfold(sized_left(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)));
                    unfold(sized_right(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)));
                    unfold(sized_value(SizedTree::Empty));
                    have 0 <= sized_value(sized_left(sized_right(SizedTree::Node(p, above, Color::Black, 2, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))))) by {
                        rewrite(sized_right(SizedTree::Node(p, above, Color::Black, 2, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))) == SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty));
                        rewrite(sized_left(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)) == SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty) == 0); normalize();
                    }
                    have 0 <= sized_value(sized_right(sized_right(SizedTree::Node(p, above, Color::Black, 2, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))))) by {
                        rewrite(sized_right(SizedTree::Node(p, above, Color::Black, 2, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))) == SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty));
                        rewrite(sized_right(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)) == SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty) == 0); normalize();
                    }
                    have sized_value(sized_right(sized_right(SizedTree::Node(p, above, Color::Black, 2, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))))) <= 2147483646 by {
                        rewrite(sized_right(SizedTree::Node(p, above, Color::Black, 2, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))) == SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty));
                        rewrite(sized_right(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)) == SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty) == 0); normalize();
                    }
                    have sized_value(sized_left(sized_right(SizedTree::Node(p, above, Color::Black, 2, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))))) <= 2147483646 - sized_value(sized_right(sized_right(SizedTree::Node(p, above, Color::Black, 2, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))))) by {
                        rewrite(sized_right(SizedTree::Node(p, above, Color::Black, 2, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))) == SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty));
                        rewrite(sized_left(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)) == SizedTree::Empty);
                        rewrite(sized_right(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)) == SizedTree::Empty);
                        rewrite(sized_value(SizedTree::Empty) == 0); normalize();
                    }
                    let { checked: checked } = step(RotateTreeRight, { tree: rotated });
                    have sized_shape(checked.model) == sized_context_three_after(g, p, node, above) by {
                        rewrite(sized_shape(checked.model) == sized_shape(SizedTree::Node(p, above, Color::Black, 2, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))));
                        unfold(sized_shape(SizedTree::Node(p, above, Color::Black, 2, SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty))));
                        unfold(sized_shape(SizedTree::Node(node, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty)));
                        unfold(sized_shape(SizedTree::Node(g, p, Color::Red, 3, SizedTree::Empty, SizedTree::Empty)));
                        unfold(sized_shape(SizedTree::Empty));
                        unfold(sized_context_three_after(g, p, node, above)); normalize();
                    }
                    have rb_subtree_size(sized_context_three_after(g, p, node, above)) == 3 by {
                        unfold(sized_context_three_after(g, p, node, above));
                        unfold(rb_subtree_size(RbTree::Node(p, above, Color::Black, RbTree::Node(node, p, Color::Red, RbTree::Empty, RbTree::Empty), RbTree::Node(g, p, Color::Red, RbTree::Empty, RbTree::Empty))));
                        unfold(rb_subtree_size(RbTree::Node(node, p, Color::Red, RbTree::Empty, RbTree::Empty)));
                        unfold(rb_subtree_size(RbTree::Node(g, p, Color::Red, RbTree::Empty, RbTree::Empty)));
                        unfold(rb_subtree_size(RbTree::Empty)); normalize();
                    }
                    have to_integer(sized_value(checked.model)) == 3 by {
                        rewrite(to_integer(sized_value(checked.model)) == rb_subtree_size(sized_shape(checked.model)));
                        rewrite(sized_shape(checked.model) == sized_context_three_after(g, p, node, above));
                        assumption();
                    }
                    have sized_value(checked.model) == 3 by {
                        apply(click::integer::int32_to_integer_equal_implies_equal(sized_value(checked.model), 3));
                    }
                    apply(sized_parent_is_shape(checked.model, above));
                    have rb_parent_is(sized_shape(checked.model), above) == 1 by {
                        rewrite(sized_shape(checked.model) == sized_context_three_after(g, p, node, above));
                        unfold(sized_context_three_after(g, p, node, above));
                        unfold(rb_parent_is(RbTree::Node(p, above, Color::Black, RbTree::Node(node, p, Color::Red, RbTree::Empty, RbTree::Empty), RbTree::Node(g, p, Color::Red, RbTree::Empty, RbTree::Empty)), above)); normalize();
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
                    let { whole: whole } = restore_sized_context(p, root->rb_node, 0, 3, { path: path, sub: checked });
                    have whole.model == sized_plug(old(state.context), at(before_restore, checked.model)) by { assumption(); }
                    let state = fold(sized_insert_context_three_at(node, root), {
                        phase: SizedInsertContextThreePhase::After(g, p, above), model: at(before_restore, checked.model), context: old(state.context), whole_model: whole.model
                    }, { whole: whole });
                    have state.context == old(state.context) by { assumption(); }
                    have state.whole_model == sized_plug(old(state.context), state.model) by { assumption(); }
                    have state.phase == sized_context_three_finish(old(state.phase)) by {
                        unfold(sized_context_three_finish(SizedInsertContextThreePhase::Before(g, p, above))); simp();
                    }
                    have sized_shape(state.model) == sized_context_three_expected(old(state.phase), node) by {
                        rewrite(old(state.phase) == SizedInsertContextThreePhase::Before(g, p, above));
                        unfold(sized_context_three_expected(SizedInsertContextThreePhase::Before(g, p, above), node)); simp();
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
    owns state: sized_insert_context_three_at(node, root);
    requires sized_context_three_pending(state.phase) == 1;
    ensures state.context == old(state.context);
    ensures state.whole_model == sized_plug(old(state.context), state.model);
    ensures state.phase == sized_context_three_finish(old(state.phase));
    ensures sized_shape(state.model) == sized_context_three_expected(old(state.phase), node);
} by {
    step(insert::__rb_insert(node, root, augment_rotate), { state: state });
    execute(); simp();
}

void insert::rb_insert_augmented(struct rb_node* node, struct rb_root* root,
                         const struct rb_augment_callbacks* augment) {
    views augment->rotate;
    requires RotateTreeRight(augment->rotate);
    owns state: sized_insert_context_three_at(node, root);
    requires sized_context_three_pending(state.phase) == 1;
    ensures state.context == old(state.context);
    ensures state.whole_model == sized_plug(old(state.context), state.model);
    ensures state.phase == sized_context_three_finish(old(state.phase));
    ensures sized_shape(state.model) == sized_context_three_expected(old(state.phase), node);
} by {
    step(insert::__rb_insert_augmented(node, root, augment->rotate), { state: state });
    execute(); simp();
}
