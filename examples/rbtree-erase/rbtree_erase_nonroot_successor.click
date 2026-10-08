verifying "rb_erase_augmented.c";

import "../rbtree-model/rbtree_resources.click";
import "../rbtree-model/rbtree_erase_splice.click";

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

# Immediate red-leaf successor below the root, on either parent link.
struct rb_node* __rb_erase_augmented(struct rb_node* node, struct rb_root* root,
                                    const struct rb_augment_callbacks* augment) {
    consumes tree: rb_at(node);
    consumes up: ctx_at(node, root);
    requires up.model != Context::Top;
    requires tree.model != RbTree::Empty;
    requires rb_left(tree.model) != RbTree::Empty;
    requires rb_right(tree.model) != RbTree::Empty;
    requires rb_left(rb_right(tree.model)) == RbTree::Empty;
    requires rb_right(rb_right(tree.model)) == RbTree::Empty;
    requires rb_color(rb_right(tree.model)) == Color::Red;
    requires is_rb(tree.model) == 1;
    requires ctx_rb(up.model, black_height(tree.model), rb_color(tree.model)) == 1;
    requires ctx_consistent(up.model, tree.model, 0) == 1;
    owns erase_callbacks(augment);
    produces node->__rb_parent_color;
    produces node->rb_left;
    produces node->rb_right;
    produces replacement: rb_at(old(node->rb_right));
    produces remaining: ctx_at(old(node->rb_right), root);
    ensures replacement.model == rb_erase_immediate_red_model(old(tree.model));
    ensures remaining.model == old(up.model);
    ensures is_rb_root(plug(remaining.model, replacement.model)) == 1;
    ensures ctx_consistent(remaining.model, replacement.model, 0) == 1;
    ensures rb_inorder(replacement.model) == list_append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model))));
    ensures result == 0;
} by {
    match tree.model {
        RbTree::Empty => { contradiction(tree.model == RbTree::Empty); },
        RbTree::Node(identity, parent, color, left_model, right_model) => {
            have rb_left(tree.model) == left_model by {
                rewrite(tree.model == RbTree::Node(identity, parent, color, left_model, right_model));
                unfold(rb_left(RbTree::Node(identity, parent, color, left_model, right_model))); normalize();
            }
            have rb_right(tree.model) == right_model by {
                rewrite(tree.model == RbTree::Node(identity, parent, color, left_model, right_model));
                unfold(rb_right(RbTree::Node(identity, parent, color, left_model, right_model))); normalize();
            }
            have left_model != RbTree::Empty by { rewrite(left_model == rb_left(tree.model)); assumption(); }
            have right_model != RbTree::Empty by { rewrite(right_model == rb_right(tree.model)); assumption(); }
            have rb_left(right_model) == RbTree::Empty by { rewrite(right_model == rb_right(tree.model)); assumption(); }
            have rb_right(right_model) == RbTree::Empty by { rewrite(right_model == rb_right(tree.model)); assumption(); }
            have rb_color(right_model) == Color::Red by { rewrite(right_model == rb_right(tree.model)); assumption(); }
            have is_rb(RbTree::Node(identity, parent, color, left_model, right_model)) == 1 by {
                rewrite(RbTree::Node(identity, parent, color, left_model, right_model) == tree.model); assumption();
            }
            have ctx_rb(up.model, black_height(RbTree::Node(identity, parent, color, left_model, right_model)),
                rb_color(RbTree::Node(identity, parent, color, left_model, right_model))) == 1 by {
                rewrite(RbTree::Node(identity, parent, color, left_model, right_model) == tree.model); assumption();
            }
            have ctx_consistent(up.model, RbTree::Node(identity, parent, color, left_model, right_model), 0) == 1 by {
                rewrite(RbTree::Node(identity, parent, color, left_model, right_model) == tree.model); assumption();
            }
            let { left: l, right: r } = unfold(tree);
            match right_model {
                RbTree::Empty => { contradiction(right_model == RbTree::Empty); },
                RbTree::Node(sid, sp, sc, sl, sr) => {
                    have sl == RbTree::Empty by {
                        unfold(rb_left(RbTree::Node(sid, sp, sc, sl, sr)));
                        rewrite(sl == rb_left(RbTree::Node(sid, sp, sc, sl, sr)));
                        rewrite(RbTree::Node(sid, sp, sc, sl, sr) == right_model); assumption();
                    }
                    have sr == RbTree::Empty by {
                        unfold(rb_right(RbTree::Node(sid, sp, sc, sl, sr)));
                        rewrite(sr == rb_right(RbTree::Node(sid, sp, sc, sl, sr)));
                        rewrite(RbTree::Node(sid, sp, sc, sl, sr) == right_model); assumption();
                    }
                    have sc == Color::Red by {
                        unfold(rb_color(RbTree::Node(sid, sp, sc, sl, sr)));
                        rewrite(sc == rb_color(RbTree::Node(sid, sp, sc, sl, sr)));
                        rewrite(RbTree::Node(sid, sp, sc, sl, sr) == right_model); assumption();
                    }
                    have rb_minimum(right_model) == RbMinimum::Found(sid, Color::Red, RbTree::Empty) by {
                        rewrite(right_model == RbTree::Node(sid, sp, sc, sl, sr));
                        rewrite(sl == RbTree::Empty); rewrite(sr == RbTree::Empty); rewrite(sc == Color::Red);
                        unfold(rb_minimum(RbTree::Node(sid, sp, Color::Red, RbTree::Empty, RbTree::Empty))); normalize();
                    }
                    have rb_erase_immediate_red_model(RbTree::Node(identity, parent, color, left_model, RbTree::Node(sid, sp, sc, sl, sr)))
                        == rb_successor_splice(sid, parent, color, left_model, RbTree::Node(sid, sp, sc, sl, sr)) by {
                        unfold(rb_erase_immediate_red_model(RbTree::Node(identity, parent, color, left_model, RbTree::Node(sid, sp, sc, sl, sr)))); normalize();
                    }
                    apply(rb_erase_red_successor_splice(identity, sid, parent, color, left_model, right_model, up.model, 0));
                    apply(plug_parent_consistent_ctx(up.model,
                        rb_successor_splice(sid, parent, color, left_model, right_model), 0));
                    let { left: sleft, right: sright } = unfold(r);
                    unfold(sleft); unfold(sright);
                    match left_model {
                        RbTree::Empty => { contradiction(left_model == RbTree::Empty); },
                        RbTree::Node(lid, lp, lc, ll, lr) => {
                            have rb_successor_splice(sid, parent, color, left_model, right_model)
                                == RbTree::Node(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), RbTree::Empty) by {
                                unfold(rb_successor_splice(sid, parent, color, left_model, right_model));
                                rewrite(left_model == RbTree::Node(lid, lp, lc, ll, lr));
                                rewrite(right_model == RbTree::Node(sid, sp, sc, sl, sr));
                                rewrite(sl == RbTree::Empty); rewrite(sr == RbTree::Empty);
                                unfold(rb_remove_min(RbTree::Node(sid, sp, sc, RbTree::Empty, RbTree::Empty)));
                                unfold(rb_reparent(RbTree::Empty, sp)); unfold(rb_reparent(RbTree::Empty, sid));
                                unfold(rb_reparent(RbTree::Node(lid, lp, lc, ll, lr), sid));
                                normalize();
                            }
                            let { left: lleft, right: lright } = unfold(l);
                            have (sid->__rb_parent_color & 1) == 0 by {
                                rewrite((sid->__rb_parent_color & 1) == color_bit(sc));
                                rewrite(sc == Color::Red); unfold(color_bit(Color::Red)); normalize();
                            }
                            match up.model {
                                Context::Top => { contradiction(up.model == Context::Top); },
                                Context::Left(pid, gp, pc, sibling_model, above_model) => {
                                    have ctx_consistent(Context::Left(pid, gp, pc, sibling_model, above_model), RbTree::Node(identity, parent, color, left_model, right_model), 0) == 1 by {
                                        rewrite(Context::Left(pid, gp, pc, sibling_model, above_model) == up.model); assumption();
                                    }
                                    apply(ctx_consistent_left_focus(pid, gp, pc, sibling_model, above_model,
                                        RbTree::Node(identity, parent, color, left_model, right_model), 0));
                                    apply(rb_parent_consistent_node_fixes_parent(identity, parent, color, left_model, right_model, pid));
                                    have is_rb_root(plug(Context::Left(pid, gp, pc, sibling_model, above_model), RbTree::Node(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), RbTree::Empty))) == 1 by {
                                        rewrite(Context::Left(pid, gp, pc, sibling_model, above_model) == up.model); rewrite(RbTree::Node(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), RbTree::Empty) == rb_successor_splice(sid, parent, color, left_model, right_model)); assumption();
                                    }
                                    have ctx_consistent(Context::Left(pid, gp, pc, sibling_model, above_model), RbTree::Node(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), RbTree::Empty), 0) == 1 by {
                                        rewrite(Context::Left(pid, gp, pc, sibling_model, above_model) == up.model); rewrite(RbTree::Node(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), RbTree::Empty) == rb_successor_splice(sid, parent, color, left_model, right_model)); assumption();
                                    }
                                    let { sibling: sibling, up: above } = unfold(up);
                                    unfold(erase_callbacks(augment));
                                    execute();
                                    fold(erase_callbacks(augment));
                                    let moved_left = fold(rb_at(lid), {
                                        model: RbTree::Node(lid, sid, lc, ll, lr)
                                    }, { left: lleft, right: lright });
                                    let empty_right = fold(rb_at(0), { model: RbTree::Empty });
                                    have rb_parent_is(RbTree::Node(lid, sid, lc, ll, lr), sid) == 1 by {
                                        unfold(rb_parent_is(RbTree::Node(lid, sid, lc, ll, lr), sid)); normalize();
                                    }
                                    have rb_parent_is(RbTree::Empty, sid) == 1 by { unfold(rb_parent_is(RbTree::Empty, sid)); normalize(); }
                                    let replacement = fold(rb_at(sid), { model: RbTree::Node(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), RbTree::Empty) },
                                        { left: moved_left, right: empty_right });
                                    let remaining = fold(ctx_at(sid, root), { model: Context::Left(pid, gp, pc, sibling_model, above_model) },
                                        { sibling: sibling, up: above });
                                    have replacement.model == rb_successor_splice(sid, parent, color, left_model, right_model) by {
                                        rewrite(rb_successor_splice(sid, parent, color, left_model, right_model) == RbTree::Node(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), RbTree::Empty)); normalize();
                                    }
                                    have replacement.model == rb_erase_immediate_red_model(old(tree.model)) by {
                                        rewrite(old(tree.model) == RbTree::Node(identity, parent, color, left_model, right_model));

                                        rewrite(right_model == RbTree::Node(sid, sp, sc, sl, sr));
                                        rewrite(rb_erase_immediate_red_model(RbTree::Node(identity, parent, color, left_model, RbTree::Node(sid, sp, sc, sl, sr)))
                                            == rb_successor_splice(sid, parent, color, left_model, RbTree::Node(sid, sp, sc, sl, sr)));
                                        rewrite(RbTree::Node(sid, sp, sc, sl, sr) == right_model); assumption();
                                    }
                                    have rb_inorder(replacement.model) == list_append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model)))) by {
                                        rewrite(replacement.model == rb_successor_splice(sid, parent, color, left_model, right_model));
                                        rewrite(rb_left(old(tree.model)) == left_model); rewrite(rb_right(old(tree.model)) == right_model); assumption();
                                    }
                                    simp();
                                },
                                Context::Right(pid, gp, pc, sibling_model, above_model) => {
                                    have ctx_consistent(Context::Right(pid, gp, pc, sibling_model, above_model), RbTree::Node(identity, parent, color, left_model, right_model), 0) == 1 by {
                                        rewrite(Context::Right(pid, gp, pc, sibling_model, above_model) == up.model); assumption();
                                    }
                                    apply(ctx_consistent_right_focus(pid, gp, pc, sibling_model, above_model,
                                        RbTree::Node(identity, parent, color, left_model, right_model), 0));
                                    apply(rb_parent_consistent_node_fixes_parent(identity, parent, color, left_model, right_model, pid));
                                    have is_rb_root(plug(Context::Right(pid, gp, pc, sibling_model, above_model), RbTree::Node(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), RbTree::Empty))) == 1 by {
                                        rewrite(Context::Right(pid, gp, pc, sibling_model, above_model) == up.model); rewrite(RbTree::Node(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), RbTree::Empty) == rb_successor_splice(sid, parent, color, left_model, right_model)); assumption();
                                    }
                                    have ctx_consistent(Context::Right(pid, gp, pc, sibling_model, above_model), RbTree::Node(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), RbTree::Empty), 0) == 1 by {
                                        rewrite(Context::Right(pid, gp, pc, sibling_model, above_model) == up.model); rewrite(RbTree::Node(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), RbTree::Empty) == rb_successor_splice(sid, parent, color, left_model, right_model)); assumption();
                                    }
                                    let { sibling: sibling, up: above } = unfold(up);
                                    match sibling.model {
                                        RbTree::Empty => {
                                            unfold(sibling);
                                            unfold(erase_callbacks(augment));
                                            execute();
                                            fold(erase_callbacks(augment));
                                            let sibling = fold(rb_at(0), { model: RbTree::Empty });
                                            let moved_left = fold(rb_at(lid), {
                                                model: RbTree::Node(lid, sid, lc, ll, lr)
                                            }, { left: lleft, right: lright });
                                            let empty_right = fold(rb_at(0), { model: RbTree::Empty });
                                            have rb_parent_is(RbTree::Node(lid, sid, lc, ll, lr), sid) == 1 by {
                                                unfold(rb_parent_is(RbTree::Node(lid, sid, lc, ll, lr), sid)); normalize();
                                            }
                                            have rb_parent_is(RbTree::Empty, sid) == 1 by { unfold(rb_parent_is(RbTree::Empty, sid)); normalize(); }
                                            let replacement = fold(rb_at(sid), { model: RbTree::Node(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), RbTree::Empty) },
                                                { left: moved_left, right: empty_right });
                                            let remaining = fold(ctx_at(sid, root), { model: Context::Right(pid, gp, pc, sibling_model, above_model) },
                                                { sibling: sibling, up: above });
                                            have replacement.model == rb_successor_splice(sid, parent, color, left_model, right_model) by {
                                                rewrite(rb_successor_splice(sid, parent, color, left_model, right_model) == RbTree::Node(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), RbTree::Empty)); normalize();
                                            }
                                            have replacement.model == rb_erase_immediate_red_model(old(tree.model)) by {
                                                rewrite(old(tree.model) == RbTree::Node(identity, parent, color, left_model, right_model));

                                                rewrite(right_model == RbTree::Node(sid, sp, sc, sl, sr));
                                                rewrite(rb_erase_immediate_red_model(RbTree::Node(identity, parent, color, left_model, RbTree::Node(sid, sp, sc, sl, sr)))
                                            == rb_successor_splice(sid, parent, color, left_model, RbTree::Node(sid, sp, sc, sl, sr)));
                                                rewrite(RbTree::Node(sid, sp, sc, sl, sr) == right_model); assumption();
                                            }
                                            have rb_inorder(replacement.model) == list_append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model)))) by {
                                                rewrite(replacement.model == rb_successor_splice(sid, parent, color, left_model, right_model));
                                                rewrite(rb_left(old(tree.model)) == left_model); rewrite(rb_right(old(tree.model)) == right_model); assumption();
                                            }
                                            simp();
                                        },
                                        RbTree::Node(sbid, sbp, sbc, sbl, sbr) => {
                                            let { left: sb_left, right: sb_right } = unfold(sibling);
                                            unfold(erase_callbacks(augment));
                                            execute();
                                            fold(erase_callbacks(augment));
                                            let sibling = fold(rb_at(sbid), { model: RbTree::Node(sbid, sbp, sbc, sbl, sbr) }, { left: sb_left, right: sb_right });
                                            let moved_left = fold(rb_at(lid), {
                                                model: RbTree::Node(lid, sid, lc, ll, lr)
                                            }, { left: lleft, right: lright });
                                            let empty_right = fold(rb_at(0), { model: RbTree::Empty });
                                            have rb_parent_is(RbTree::Node(lid, sid, lc, ll, lr), sid) == 1 by {
                                                unfold(rb_parent_is(RbTree::Node(lid, sid, lc, ll, lr), sid)); normalize();
                                            }
                                            have rb_parent_is(RbTree::Empty, sid) == 1 by { unfold(rb_parent_is(RbTree::Empty, sid)); normalize(); }
                                            let replacement = fold(rb_at(sid), { model: RbTree::Node(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), RbTree::Empty) },
                                                { left: moved_left, right: empty_right });
                                            let remaining = fold(ctx_at(sid, root), { model: Context::Right(pid, gp, pc, sibling_model, above_model) },
                                                { sibling: sibling, up: above });
                                            have replacement.model == rb_successor_splice(sid, parent, color, left_model, right_model) by {
                                                rewrite(rb_successor_splice(sid, parent, color, left_model, right_model) == RbTree::Node(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), RbTree::Empty)); normalize();
                                            }
                                            have replacement.model == rb_erase_immediate_red_model(old(tree.model)) by {
                                                rewrite(old(tree.model) == RbTree::Node(identity, parent, color, left_model, right_model));

                                                rewrite(right_model == RbTree::Node(sid, sp, sc, sl, sr));
                                                rewrite(rb_erase_immediate_red_model(RbTree::Node(identity, parent, color, left_model, RbTree::Node(sid, sp, sc, sl, sr)))
                                            == rb_successor_splice(sid, parent, color, left_model, RbTree::Node(sid, sp, sc, sl, sr)));
                                                rewrite(RbTree::Node(sid, sp, sc, sl, sr) == right_model); assumption();
                                            }
                                            have rb_inorder(replacement.model) == list_append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model)))) by {
                                                rewrite(replacement.model == rb_successor_splice(sid, parent, color, left_model, right_model));
                                                rewrite(rb_left(old(tree.model)) == left_model); rewrite(rb_right(old(tree.model)) == right_model); assumption();
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
        },
    }
}
