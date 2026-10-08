verifying "rb_erase_augmented.c";

import "../rbtree-model/rbtree_resources.click";
import "../rbtree-model/rbtree_erase_one_child.click";

contract void AugmentRotate(struct rb_node* old, struct rb_node* new) {
    requires new != 0;
    ensures 1 == 1;
}

contract void ErasePropagate(struct rb_node* node, struct rb_node* stop) {
    ensures 1 == 1;
}

contract void EraseCopy(struct rb_node* node, struct rb_node* successor) {
    requires node != 0;
    requires successor != 0;
    ensures 1 == 1;
}

resource erase_callbacks(augment: const struct rb_augment_callbacks*) {
    owns augment->propagate;
    owns augment->copy;
    owns augment->rotate;
    fact ErasePropagate(augment->propagate);
    fact EraseCopy(augment->copy);
    fact AugmentRotate(augment->rotate);
}

# A non-root node whose only child is on the left; colors follow from validity.
struct rb_node* __rb_erase_augmented(struct rb_node* node, struct rb_root* root,
                                    const struct rb_augment_callbacks* augment) {
    consumes tree: rb_at(node);
    consumes up: ctx_at(node, root);
    requires tree.model != RbTree::Empty;
    requires rb_right(tree.model) == RbTree::Empty;
    requires rb_left(tree.model) != RbTree::Empty;
    requires is_rb(tree.model) == 1;
    requires up.model != Context::Top;
    requires ctx_rb(up.model, black_height(tree.model), rb_color(tree.model)) == 1;
    requires ctx_consistent(up.model, tree.model, 0) == 1;
    owns erase_callbacks(augment);
    produces node->__rb_parent_color;
    produces node->rb_right;
    produces node->rb_left;
    produces replacement: rb_at(old(node->rb_left));
    produces remaining: ctx_at(old(node->rb_left), root);
    ensures replacement.model == rb_erase_one_child_model(old(tree.model));
    ensures remaining.model == old(up.model);
    ensures is_rb_root(plug(remaining.model, replacement.model)) == 1;
    ensures ctx_consistent(remaining.model, replacement.model, 0) == 1;
    ensures rb_inorder(replacement.model) == rb_inorder(rb_left(old(tree.model)));
    ensures result == 0;
} by {
    match tree.model {
        RbTree::Empty => { contradiction(tree.model == RbTree::Empty); },
        RbTree::Node(id, parent, color, child, empty) => {
            have empty == RbTree::Empty by {
                unfold(rb_right(RbTree::Node(id, parent, color, child, empty)));
                rewrite(empty == rb_right(RbTree::Node(id, parent, color, child, empty)));
                rewrite(RbTree::Node(id, parent, color, child, empty) == tree.model); assumption();
            }
            have child != RbTree::Empty by {
                unfold(rb_left(RbTree::Node(id, parent, color, child, empty)));
                rewrite(child == rb_left(RbTree::Node(id, parent, color, child, empty)));
                rewrite(RbTree::Node(id, parent, color, child, empty) == tree.model); assumption();
            }
            have is_rb(RbTree::Node(id, parent, color, child, RbTree::Empty)) == 1 by {
                rewrite(RbTree::Empty == empty);
                rewrite(RbTree::Node(id, parent, color, child, empty) == tree.model); assumption();
            }
            have ctx_rb(up.model, black_height(RbTree::Node(id, parent, color, child, RbTree::Empty)),
                rb_color(RbTree::Node(id, parent, color, child, RbTree::Empty))) == 1 by {
                rewrite(RbTree::Empty == empty);
                rewrite(RbTree::Node(id, parent, color, child, empty) == tree.model); assumption();
            }
            apply(rb_erase_only_left_child(id, parent, color, child, up.model));
            have color == Color::Black by { extract(color == Color::Black); assumption(); }
            have is_rb_root(plug(up.model, rb_reparent(rb_recolor(child, Color::Black), parent))) == 1 by {
                extract(is_rb_root(plug(up.model, rb_reparent(rb_recolor(child, Color::Black), parent))) == 1); assumption();
            }
            have ctx_consistent(up.model, RbTree::Node(id, parent, color, child, empty), 0) == 1 by {
                rewrite(RbTree::Node(id, parent, color, child, empty) == tree.model); assumption();
            }
            match child {
                RbTree::Empty => { contradiction(child == RbTree::Empty); },
                RbTree::Node(cid, cp, cc, cl, cr) => {
                    let { left: r, right: l } = unfold(tree);
                    unfold(l);
                    let { left: child_left, right: child_right } = unfold(r);
                    have color_bit(Color::Black) == 1 by { unfold(color_bit(Color::Black)); normalize(); }
                    have (node->__rb_parent_color & 1) == 1 by {
                        rewrite((node->__rb_parent_color & 1) == color_bit(color));
                        rewrite(color == Color::Black); unfold(color_bit(Color::Black)); normalize();
                    }
                    have rb_reparent(rb_recolor(child, Color::Black), parent)
                        == RbTree::Node(cid, parent, Color::Black, cl, cr) by {
                        rewrite(child == RbTree::Node(cid, cp, cc, cl, cr));
                        unfold(rb_recolor(RbTree::Node(cid, cp, cc, cl, cr), Color::Black));
                        unfold(rb_reparent(RbTree::Node(cid, cp, Color::Black, cl, cr), parent)); normalize();
                    }
                    match up.model {
                        Context::Top => { contradiction(up.model == Context::Top); },
                        Context::Left(pid, gp, pc, sibling_model, above_model) => {
                            have ctx_consistent(Context::Left(pid, gp, pc, sibling_model, above_model), RbTree::Node(id, parent, color, child, empty), 0) == 1 by {
                                rewrite(Context::Left(pid, gp, pc, sibling_model, above_model) == up.model); assumption();
                            }
                            apply(ctx_consistent_left_focus(pid, gp, pc, sibling_model, above_model,
                                RbTree::Node(id, parent, color, child, empty), 0));
                            apply(rb_parent_consistent_node_fixes_parent(id, parent, color, child, empty, pid));
                            apply(rb_parent_consistent_node_left(id, parent, color, child, empty, pid));
                            apply(rb_erase_child_keeps_parents(up.model, id, parent, color, child, empty, child));
                            have is_rb_root(plug(Context::Left(pid, gp, pc, sibling_model, above_model), RbTree::Node(cid, parent, Color::Black, cl, cr))) == 1 by {
                                rewrite(Context::Left(pid, gp, pc, sibling_model, above_model) == up.model);
                                rewrite(RbTree::Node(cid, parent, Color::Black, cl, cr) == rb_reparent(rb_recolor(child, Color::Black), parent));
                                assumption();
                            }
                            have ctx_consistent(Context::Left(pid, gp, pc, sibling_model, above_model), RbTree::Node(cid, parent, Color::Black, cl, cr), 0) == 1 by {
                                rewrite(Context::Left(pid, gp, pc, sibling_model, above_model) == up.model);
                                rewrite(RbTree::Node(cid, parent, Color::Black, cl, cr) == rb_reparent(rb_recolor(child, Color::Black), parent));
                                assumption();
                            }
                            let { sibling: sibling, up: above } = unfold(up);
                            unfold(erase_callbacks(augment));
                            execute();
                            fold(erase_callbacks(augment));
                            let replacement = fold(rb_at(cid), {
                                model: RbTree::Node(cid, parent, Color::Black, cl, cr)
                            }, { left: child_left, right: child_right });
                            let remaining = fold(ctx_at(cid, root), { model: Context::Left(pid, gp, pc, sibling_model, above_model) },
                                { sibling: sibling, up: above });
                            have replacement.model == rb_erase_one_child_model(old(tree.model)) by {
                                rewrite(old(tree.model) == RbTree::Node(id, parent, color, child, empty));
                                unfold(rb_left(RbTree::Node(id, parent, color, child, empty)));
                                unfold(rb_erase_one_child_model(RbTree::Node(id, parent, color, child, empty)));
                                rewrite(empty == RbTree::Empty);
                                rewrite(child == RbTree::Node(cid, cp, cc, cl, cr));
                                unfold(rb_erase_root_child(RbTree::Node(id, parent, color, RbTree::Node(cid, cp, cc, cl, cr), RbTree::Empty)));
                                rewrite(RbTree::Node(cid, cp, cc, cl, cr) == child);
                                rewrite(rb_reparent(rb_recolor(child, Color::Black), parent) == RbTree::Node(cid, parent, Color::Black, cl, cr));
                                simp();
                            }
                            have rb_inorder(replacement.model) == rb_inorder(rb_left(old(tree.model))) by {
                                rewrite(old(tree.model) == RbTree::Node(id, parent, color, child, empty));
                                unfold(rb_left(RbTree::Node(id, parent, color, child, empty)));
                                rewrite(RbTree::Node(cid, parent, Color::Black, cl, cr) == rb_reparent(rb_recolor(child, Color::Black), parent));
                                assumption();
                            }
                            simp();
                        },
                        Context::Right(pid, gp, pc, sibling_model, above_model) => {
                            have ctx_consistent(Context::Right(pid, gp, pc, sibling_model, above_model), RbTree::Node(id, parent, color, child, empty), 0) == 1 by {
                                rewrite(Context::Right(pid, gp, pc, sibling_model, above_model) == up.model); assumption();
                            }
                            apply(ctx_consistent_right_focus(pid, gp, pc, sibling_model, above_model,
                                RbTree::Node(id, parent, color, child, empty), 0));
                            apply(rb_parent_consistent_node_fixes_parent(id, parent, color, child, empty, pid));
                            apply(rb_parent_consistent_node_left(id, parent, color, child, empty, pid));
                            apply(rb_erase_child_keeps_parents(up.model, id, parent, color, child, empty, child));
                            have is_rb_root(plug(Context::Right(pid, gp, pc, sibling_model, above_model), RbTree::Node(cid, parent, Color::Black, cl, cr))) == 1 by {
                                rewrite(Context::Right(pid, gp, pc, sibling_model, above_model) == up.model);
                                rewrite(RbTree::Node(cid, parent, Color::Black, cl, cr) == rb_reparent(rb_recolor(child, Color::Black), parent));
                                assumption();
                            }
                            have ctx_consistent(Context::Right(pid, gp, pc, sibling_model, above_model), RbTree::Node(cid, parent, Color::Black, cl, cr), 0) == 1 by {
                                rewrite(Context::Right(pid, gp, pc, sibling_model, above_model) == up.model);
                                rewrite(RbTree::Node(cid, parent, Color::Black, cl, cr) == rb_reparent(rb_recolor(child, Color::Black), parent));
                                assumption();
                            }
                            let { sibling: sibling, up: above } = unfold(up);
                            match sibling.model {
                                RbTree::Empty => {
                                    unfold(sibling);
                                    unfold(erase_callbacks(augment));
                                    execute();
                                    fold(erase_callbacks(augment));
                                    let sibling = fold(rb_at(0), { model: RbTree::Empty });
                                    let replacement = fold(rb_at(cid), {
                                        model: RbTree::Node(cid, parent, Color::Black, cl, cr)
                                    }, { left: child_left, right: child_right });
                                    let remaining = fold(ctx_at(cid, root), { model: Context::Right(pid, gp, pc, sibling_model, above_model) },
                                        { sibling: sibling, up: above });
                                    have replacement.model == rb_erase_one_child_model(old(tree.model)) by {
                                        rewrite(old(tree.model) == RbTree::Node(id, parent, color, child, empty));
                                        unfold(rb_left(RbTree::Node(id, parent, color, child, empty)));
                                        unfold(rb_erase_one_child_model(RbTree::Node(id, parent, color, child, empty)));
                                        rewrite(empty == RbTree::Empty);
                                        rewrite(child == RbTree::Node(cid, cp, cc, cl, cr));
                                        unfold(rb_erase_root_child(RbTree::Node(id, parent, color, RbTree::Node(cid, cp, cc, cl, cr), RbTree::Empty)));
                                        rewrite(RbTree::Node(cid, cp, cc, cl, cr) == child);
                                        rewrite(rb_reparent(rb_recolor(child, Color::Black), parent) == RbTree::Node(cid, parent, Color::Black, cl, cr));
                                        simp();
                                    }
                                    have rb_inorder(replacement.model) == rb_inorder(rb_left(old(tree.model))) by {
                                        rewrite(old(tree.model) == RbTree::Node(id, parent, color, child, empty));
                                        unfold(rb_left(RbTree::Node(id, parent, color, child, empty)));
                                        rewrite(RbTree::Node(cid, parent, Color::Black, cl, cr) == rb_reparent(rb_recolor(child, Color::Black), parent));
                                        assumption();
                                    }
                                    simp();
                                },
                                RbTree::Node(sid, sp, sc, sl, sr) => {
                                    let { left: sl_tree, right: sr_tree } = unfold(sibling);
                                    unfold(erase_callbacks(augment));
                                    execute();
                                    fold(erase_callbacks(augment));
                                    let sibling = fold(rb_at(sid), { model: RbTree::Node(sid, sp, sc, sl, sr) }, { left: sl_tree, right: sr_tree });
                                    let replacement = fold(rb_at(cid), {
                                        model: RbTree::Node(cid, parent, Color::Black, cl, cr)
                                    }, { left: child_left, right: child_right });
                                    let remaining = fold(ctx_at(cid, root), { model: Context::Right(pid, gp, pc, sibling_model, above_model) },
                                        { sibling: sibling, up: above });
                                    have replacement.model == rb_erase_one_child_model(old(tree.model)) by {
                                        rewrite(old(tree.model) == RbTree::Node(id, parent, color, child, empty));
                                        unfold(rb_left(RbTree::Node(id, parent, color, child, empty)));
                                        unfold(rb_erase_one_child_model(RbTree::Node(id, parent, color, child, empty)));
                                        rewrite(empty == RbTree::Empty);
                                        rewrite(child == RbTree::Node(cid, cp, cc, cl, cr));
                                        unfold(rb_erase_root_child(RbTree::Node(id, parent, color, RbTree::Node(cid, cp, cc, cl, cr), RbTree::Empty)));
                                        rewrite(RbTree::Node(cid, cp, cc, cl, cr) == child);
                                        rewrite(rb_reparent(rb_recolor(child, Color::Black), parent) == RbTree::Node(cid, parent, Color::Black, cl, cr));
                                        simp();
                                    }
                                    have rb_inorder(replacement.model) == rb_inorder(rb_left(old(tree.model))) by {
                                        rewrite(old(tree.model) == RbTree::Node(id, parent, color, child, empty));
                                        unfold(rb_left(RbTree::Node(id, parent, color, child, empty)));
                                        rewrite(RbTree::Node(cid, parent, Color::Black, cl, cr) == rb_reparent(rb_recolor(child, Color::Black), parent));
                                        assumption();
                                    }
                                    simp();
                                },
                            }
                        },
                    }
                },
            }
        },
    }
}
