// Arbitrary ancestor propagation over the unchanged Linux callback body.
verifying "rbtree_size_propagate.c";
verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_walk.click";

void sized_propagate(struct rb_node* rb, struct rb_node* stop) {
    consumes walk: sized_walk_at(rb, stop);
    requires sized_walk_pending(walk.model) == 1 or rb == stop;
    requires rb_subtree_size(sized_shape(sized_walk_tree(walk.model))) <= 2147483647;
    produces whole: sized_result_at(stop);
    ensures sized_result_root(whole.model) == sized_walk_root(old(walk.model));
    ensures sized_shape(sized_result_tree(whole.model)) == sized_shape(sized_walk_tree(old(walk.model)));
    ensures sized_counts_valid(sized_result_tree(whole.model)) == 1;
} by {
    apply(compute_size_restores_subtree_size());
    loop {
        owns walk: sized_walk_at(rb, stop);
        decreases sized_walk_rank(walk.model);
        invariant sized_walk_pending(walk.model) == 1 or rb == stop;
        invariant sized_walk_root(walk.model) == sized_walk_root(old(walk.model));
        invariant sized_shape(sized_walk_tree(walk.model)) == sized_shape(sized_walk_tree(old(walk.model)));
        invariant rb_subtree_size(sized_shape(sized_walk_tree(walk.model))) <= 2147483647;
        initialize by simp();
        preserve by {
            mark iteration;
            match walk.model {
                SizedWalk::Done(result_model) => {
                    have sized_walk_pending(walk.model) == 0 by {
                        rewrite(walk.model == SizedWalk::Done(result_model));
                        unfold(sized_walk_pending(SizedWalk::Done(result_model))); normalize();
                    }
                    have not (sized_walk_pending(walk.model) == 1) by {
                        rewrite(sized_walk_pending(walk.model) == 0); normalize();
                    }
                    have rb == stop by {
                        cases {
                            sized_walk_pending(walk.model) == 1 => { contradiction(sized_walk_pending(walk.model) == 1); }
                            rb == stop => { assumption(); }
                        }
                    }
                    contradiction(rb == stop);
                },
                SizedWalk::Active(previous, sub_model, path_model) => {
                    have sized_walk_tree(walk.model) == sized_plug(sized_path_context(path_model), sub_model) by {
                        rewrite(walk.model == SizedWalk::Active(previous, sub_model, path_model));
                        unfold(sized_walk_tree(SizedWalk::Active(previous, sub_model, path_model))); normalize();
                    }
                    have sized_walk_root(walk.model) == sized_path_root(path_model) by {
                        rewrite(walk.model == SizedWalk::Active(previous, sub_model, path_model));
                        unfold(sized_walk_root(SizedWalk::Active(previous, sub_model, path_model))); normalize();
                    }
                    apply(sized_context_depth_nonnegative(sized_path_context(path_model)));
                    apply(sized_plug_contains_focus(sized_path_context(path_model), sub_model));
                    have rb_subtree_size(sized_shape(sized_plug(sized_path_context(path_model), sub_model))) <= 2147483647 by {
                        rewrite(sized_plug(sized_path_context(path_model), sub_model) == sized_walk_tree(walk.model)); assumption();
                    }
                    have rb_subtree_size(sized_shape(sub_model)) <= 2147483647 by {
                        arithmetic() using {
                            rb_subtree_size(sized_shape(sub_model)) <= rb_subtree_size(sized_shape(sized_plug(sized_path_context(path_model), sub_model)));
                            rb_subtree_size(sized_shape(sized_plug(sized_path_context(path_model), sub_model))) <= 2147483647;
                        };
                    }
                    let { focus: dirty, path: path } = unfold(walk);
                    let { prepared: dirty } = prepare_sized_focus(rb, { tree: dirty });
                    step(); step(); step(); step(); step(); step();
                    let { result: child_node } = step();
                    mark before_recompute;
                    let { result: status, checked: repaired } = step(RecomputeTree, { tree: dirty });
                    apply(sized_parent_is_shape(sub_model, sized_context_parent(sized_path_context(path_model), stop)));
                    apply(sized_parent_is_shape(repaired.model, sized_context_parent(sized_path_context(path_model), stop)));
                    apply(sized_plug_same_shape(sized_path_context(path_model), sub_model, repaired.model));
                    if status != 0 {
                        have sized_value(repaired.model) == previous by {
                            cases {
                                status == 0 => { contradiction(status == 0); }
                                sized_value(repaired.model) == sized_value(at(before_recompute, dirty.model)) => {
                                    rewrite(sized_value(repaired.model) == sized_value(at(before_recompute, dirty.model)));
                                    rewrite(at(before_recompute, dirty.model) == sub_model); assumption();
                                }
                            }
                        }
                        let { done: walk } = stop_sized_path(rb, stop, previous, { sub: repaired, path: path });
                        step(); step();
                    } else {
                        step();
                        match repaired.model {
                            SizedTree::Empty => { unfold(repaired); contradiction(&child_node->rb == 0); },
                            SizedTree::Node(identity, parent, color, value, left_model, right_model) => {
                                have sized_parent_is(SizedTree::Node(identity, parent, color, value, left_model, right_model), sized_context_parent(sized_path_context(path_model), stop)) == 1 by {
                                    rewrite(SizedTree::Node(identity, parent, color, value, left_model, right_model) == repaired.model); assumption();
                                }
                                have parent == sized_context_parent(sized_path_context(path_model), stop) by auto();
                                let { metadata: metadata, left: left, right: right } = unfold(repaired);
                                step(); step();
                                have rb == parent by { normalize(); }
                                let sub = fold(sized_at(&child_node->rb), { model: SizedTree::Node(identity, parent, color, value, left_model, right_model) }, { metadata: metadata, left: left, right: right });
                                have rb == sized_context_parent(sized_path_context(path.model), stop) by {
                                    rewrite(rb == parent);
                                    rewrite(path.model == path_model); assumption();
                                }
                                let { next: walk } = advance_sized_path(&child_node->rb, rb, stop, previous, { sub: sub, path: path });
                                have sized_walk_pending(walk.model) == 1 or rb == stop by { assumption(); }
                                have sized_walk_root(walk.model) == sized_walk_root(old(walk.model)) by { assumption(); }
                                have sized_walk_tree(walk.model) == sized_plug(sized_path_context(path_model), SizedTree::Node(identity, parent, color, value, left_model, right_model)) by { assumption(); }
                                have sized_shape(sized_walk_tree(walk.model)) == sized_shape(sized_walk_tree(old(walk.model))) by { assumption(); }
                                have rb_subtree_size(sized_shape(sized_walk_tree(walk.model))) <= 2147483647 by {
                                    rewrite(sized_shape(sized_walk_tree(walk.model)) == sized_shape(sized_walk_tree(old(walk.model))));
                                    rewrite(sized_shape(sized_walk_tree(old(walk.model))) == sized_shape(sized_walk_tree(at(iteration, walk.model)))); assumption();
                                }
                                have 0 <= sized_walk_rank(walk.model) by { assumption(); }
                                have sized_walk_rank(walk.model) < sized_context_depth(sized_path_context(path_model)) + 1 by { assumption(); }
                                have sized_walk_rank(at(iteration, walk.model)) == sized_context_depth(sized_path_context(path_model)) + 1 by {
                                    rewrite(at(iteration, walk.model) == SizedWalk::Active(previous, sub_model, path_model));
                                    unfold(sized_walk_rank(SizedWalk::Active(previous, sub_model, path_model))); normalize();
                                }
                                have sized_walk_rank(walk.model) < sized_walk_rank(at(iteration, walk.model)) by {
                                    rewrite(sized_walk_rank(at(iteration, walk.model)) == sized_context_depth(sized_path_context(path_model)) + 1); assumption();
                                }
                                close_invariants() by { simp(); }
                            },
                        }
                    }
                },
            }
        }
    }
    mark joined;
    match walk.model {
        SizedWalk::Active(previous, sub_model, path_model) => {
            have sized_walk_pending(walk.model) == 1 by {
                rewrite(walk.model == SizedWalk::Active(previous, sub_model, path_model));
                unfold(sized_walk_pending(SizedWalk::Active(previous, sub_model, path_model))); normalize();
            }
            let { focus: focus, path: path } = unfold(walk);
            have sized_walk_pending(at(joined, walk.model)) == 0 by {
                extract(rb == stop or sized_walk_pending(at(joined, walk.model)) == 0);
                cases {
                    rb == stop => { contradiction(rb == stop); }
                    sized_walk_pending(at(joined, walk.model)) == 0 => { assumption(); }
                }
            }
            have not (sized_walk_pending(at(joined, walk.model)) == 1) by {
                rewrite(sized_walk_pending(at(joined, walk.model)) == 0); normalize();
            }
            contradiction(sized_walk_pending(at(joined, walk.model)) == 1);
        },
        SizedWalk::Done(result_model) => {
            have sized_walk_pending(walk.model) == 0 by {
                rewrite(walk.model == SizedWalk::Done(result_model));
                unfold(sized_walk_pending(SizedWalk::Done(result_model))); normalize();
            }
            let { whole: whole } = finish_sized_walk(rb, stop, { walk: walk });
            execute(); simp();
        },
    }
}

contract void PropagateTree(struct rb_node* rb, struct rb_node* stop) {
    consumes walk: sized_walk_at(rb, stop);
    produces whole: sized_result_at(stop);
    requires sized_walk_pending(walk.model) == 1 or rb == stop;
    requires rb_subtree_size(sized_shape(sized_walk_tree(walk.model))) <= 2147483647;
    ensures sized_result_root(whole.model) == sized_walk_root(old(walk.model));
    ensures sized_shape(sized_result_tree(whole.model)) == sized_shape(sized_walk_tree(old(walk.model)));
    ensures sized_counts_valid(sized_result_tree(whole.model)) == 1;
}

theorem sized_propagate_has_tree_contract()
    executes sized_propagate(struct rb_node* rb, struct rb_node* stop) {
    ensures PropagateTree(&sized_propagate) as { walk: walk, whole: whole } by {
        let { whole: whole } = step(sized_propagate(rb, stop), { walk: walk });
        simp();
    }
}
