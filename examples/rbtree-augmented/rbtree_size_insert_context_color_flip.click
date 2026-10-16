// A color flip beneath a black parent retains an arbitrary owned outer context.
verifying "rb_insert_augmented.c";
verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_context_resources.click";

spec enum SizedContextFlipPhase {
    Before(struct rb_node*, struct rb_node*, struct rb_node*),
    After(struct rb_node*, struct rb_node*, struct rb_node*),
    Done(struct rb_node*, struct rb_node*, struct rb_node*),
}
function sized_context_flip_pending(phase: SizedContextFlipPhase) -> int32 {
    match phase {
        SizedContextFlipPhase::Before(g, p, u) => 1,
        SizedContextFlipPhase::After(g, p, u) => 0,
        SizedContextFlipPhase::Done(g, p, u) => 0,
    }
}
function sized_context_flip_running(phase: SizedContextFlipPhase) -> int32 {
    match phase {
        SizedContextFlipPhase::Before(g, p, u) => 1,
        SizedContextFlipPhase::After(g, p, u) => 1,
        SizedContextFlipPhase::Done(g, p, u) => 0,
    }
}
function sized_context_flip_finish(phase: SizedContextFlipPhase) -> SizedContextFlipPhase {
    match phase {
        SizedContextFlipPhase::Before(g, p, u) => SizedContextFlipPhase::Done(g, p, u),
        SizedContextFlipPhase::After(g, p, u) => SizedContextFlipPhase::Done(g, p, u),
        SizedContextFlipPhase::Done(g, p, u) => SizedContextFlipPhase::Done(g, p, u),
    }
}
function sized_context_flip_focus(phase: SizedContextFlipPhase, n: struct rb_node*) -> struct rb_node* {
    match phase {
        SizedContextFlipPhase::Before(g, p, u) => n,
        SizedContextFlipPhase::After(g, p, u) => g,
        SizedContextFlipPhase::Done(g, p, u) => g,
    }
}
function sized_context_flip_parent(phase: SizedContextFlipPhase, outer: SizedContext) -> struct rb_node* {
    match phase {
        SizedContextFlipPhase::Before(g, p, u) => p,
        SizedContextFlipPhase::After(g, p, u) => sized_context_parent(outer, 0),
        SizedContextFlipPhase::Done(g, p, u) => sized_context_parent(outer, 0),
    }
}
function sized_context_flip_black(outer: SizedContext) -> int32 {
    match outer {
        SizedContext::Top => 0,
        SizedContext::Left(a, parent, color, value, sibling, up) => color_bit(color),
        SizedContext::Right(a, parent, color, value, sibling, up) => color_bit(color),
    }
}
function sized_context_flip_subtree(phase: SizedContextFlipPhase, n: struct rb_node*, outer: SizedContext, seed: SizedTree, parent_value: int32, grand_value: int32) -> SizedTree {
    match phase {
        SizedContextFlipPhase::Before(g,p,u) => SizedTree::Node(g, sized_context_parent(outer,0), Color::Red, grand_value, SizedTree::Node(p, g, Color::Black, parent_value, seed, SizedTree::Empty), SizedTree::Node(u, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty)),
        SizedContextFlipPhase::After(g,p,u) => SizedTree::Node(g, sized_context_parent(outer,0), Color::Red, grand_value, SizedTree::Node(p, g, Color::Black, parent_value, seed, SizedTree::Empty), SizedTree::Node(u, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty)),
        SizedContextFlipPhase::Done(g,p,u) => SizedTree::Node(g, sized_context_parent(outer,0), Color::Red, grand_value, SizedTree::Node(p, g, Color::Black, parent_value, seed, SizedTree::Empty), SizedTree::Node(u, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty)),
    }
}
resource sized_context_flip_at(n: struct rb_node*, root: struct rb_root*) {
    field phase: SizedContextFlipPhase;
    field model: SizedTree;
    field context: SizedContext;
    field outer: SizedContext;
    field seed: SizedTree;
    field parent_value: int32;
    field grand_value: int32;
    match phase {
        SizedContextFlipPhase::Before(g, p, u) => {
            fact seed == SizedTree::Node(n, p, Color::Red, sized_value(seed), sized_left(seed), sized_right(seed));
            fact sized_context_flip_black(outer) == 1;
            owns root->rb_node;
            owns focus: sized_at(n);
            owns path: sized_context_at(n, root->rb_node, 0, sized_value(seed));
            fact focus.model == model;
            fact path.model == context;
            fact model == seed;
            fact context == SizedContext::Left(p, g, Color::Red, parent_value, SizedTree::Empty, SizedContext::Left(g, sized_context_parent(outer, 0), Color::Black, grand_value, SizedTree::Node(u, g, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), outer));
        },
        SizedContextFlipPhase::After(g, p, u) => {
            fact seed == SizedTree::Node(n, p, Color::Red, sized_value(seed), sized_left(seed), sized_right(seed));
            fact sized_context_flip_black(outer) == 1;
            owns root->rb_node;
            owns focus: sized_at(g);
            owns path: sized_context_at(g, root->rb_node, 0, grand_value);
            fact focus.model == model;
            fact path.model == context;
            fact context == outer;
            fact model == SizedTree::Node(g, sized_context_parent(outer, 0), Color::Red, grand_value, SizedTree::Node(p, g, Color::Black, parent_value, seed, SizedTree::Empty), SizedTree::Node(u, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty));
        },
        SizedContextFlipPhase::Done(g, p, u) => {
            fact seed == SizedTree::Node(n, p, Color::Red, sized_value(seed), sized_left(seed), sized_right(seed));
            fact sized_context_flip_black(outer) == 1;
            owns root->rb_node;
            owns whole: sized_at(root->rb_node);
            fact whole.model == model;
            fact context == SizedContext::Top;
        },
    }
}
void __rb_insert(struct rb_node* node, struct rb_root* root,
                  void (*augment_rotate)(struct rb_node*, struct rb_node*)) {
    owns state: sized_context_flip_at(node, root);
    requires sized_context_flip_pending(state.phase) == 1;
    ensures state.seed == old(state.seed);
    ensures state.parent_value == old(state.parent_value);
    ensures state.grand_value == old(state.grand_value);
    ensures state.phase == sized_context_flip_finish(old(state.phase));
    ensures state.model == sized_plug(old(state.outer), sized_context_flip_subtree(sized_context_flip_finish(old(state.phase)), node, old(state.outer), old(state.seed), old(state.parent_value), old(state.grand_value)));
} by {
    match state.phase {
        SizedContextFlipPhase::After(g, p, u) => {
            have sized_context_flip_pending(state.phase) != 1 by {
                rewrite(state.phase == SizedContextFlipPhase::After(g, p, u));
                unfold(sized_context_flip_pending(SizedContextFlipPhase::After(g, p, u))); normalize();
            }
            contradiction(sized_context_flip_pending(state.phase) == 1);
        },
        SizedContextFlipPhase::Done(g, p, u) => {
            have sized_context_flip_pending(state.phase) != 1 by {
                rewrite(state.phase == SizedContextFlipPhase::Done(g, p, u));
                unfold(sized_context_flip_pending(SizedContextFlipPhase::Done(g, p, u))); normalize();
            }
            contradiction(sized_context_flip_pending(state.phase) == 1);
        },
        SizedContextFlipPhase::Before(g, p, u) => {
            let { focus: focus, path: path } = unfold(state);
            let { metadata: n_size, left: n_left, right: n_right } = unfold(focus);
            unfold(color_bit(Color::Red));
            have node->__rb_parent_color == address(p) by {
                rewrite(node->__rb_parent_color == address(p) + (node->__rb_parent_color & 1));
                rewrite((node->__rb_parent_color & 1) == color_bit(Color::Red));
                rewrite(color_bit(Color::Red) == 0); normalize();
            }
            step(); step(); step(); step();
            let focus = fold(sized_at(node), { model: old(state.model) }, { metadata: n_size, left: n_left, right: n_right });
            let state = fold(sized_context_flip_at(node,root), { phase: SizedContextFlipPhase::Before(g, p, u), model: old(state.model), context: old(state.context), outer: old(state.outer), seed: old(state.seed), parent_value: old(state.parent_value), grand_value: old(state.grand_value) }, { focus: focus, path: path });
            loop {
                owns state: sized_context_flip_at(old(node),root);
                decreases sized_context_depth(state.context);
                invariant sized_context_flip_running(state.phase) == 1;
                invariant sized_context_flip_finish(state.phase) == sized_context_flip_finish(old(state.phase));
                invariant old(state.phase) == SizedContextFlipPhase::Before(g, p, u);
                invariant state.outer == old(state.outer);
                invariant state.seed == old(state.seed);
                invariant state.parent_value == old(state.parent_value);
                invariant state.grand_value == old(state.grand_value);
                invariant node == sized_context_flip_focus(state.phase, old(node));
                invariant parent == sized_context_flip_parent(state.phase, state.outer);
                initialize by simp();
                preserve by {
                    mark iteration;
                    match state.phase {
                        SizedContextFlipPhase::Done(x, y, z) => {
                            have not (sized_context_flip_running(state.phase) == 1) by {
                                rewrite(state.phase == SizedContextFlipPhase::Done(x, y, z));
                                unfold(sized_context_flip_running(SizedContextFlipPhase::Done(x, y, z))); normalize();
                            }
                            contradiction(sized_context_flip_running(state.phase) == 1);
                        },
                        SizedContextFlipPhase::After(x, y, z) => {
                            have parent == sized_context_parent(at(iteration,state.outer),0) by {
                                rewrite(parent == sized_context_flip_parent(state.phase,at(iteration,state.outer)));
                                rewrite(state.phase == SizedContextFlipPhase::After(x,y,z));
                                unfold(sized_context_flip_parent(SizedContextFlipPhase::After(x,y,z),at(iteration,state.outer))); normalize();
                            }
                            have node == x by {
                                rewrite(node == sized_context_flip_focus(state.phase,old(node)));
                                rewrite(state.phase == SizedContextFlipPhase::After(x,y,z));
                                unfold(sized_context_flip_focus(SizedContextFlipPhase::After(x,y,z),old(node))); normalize();
                            }
                            unfold(sized_context_flip_finish(SizedContextFlipPhase::After(x,y,z)));
                            have SizedContextFlipPhase::Done(x,y,z) == sized_context_flip_finish(old(state.phase)) by {
                                rewrite(SizedContextFlipPhase::Done(x,y,z) == sized_context_flip_finish(SizedContextFlipPhase::After(x,y,z)));
                                rewrite(SizedContextFlipPhase::After(x,y,z) == state.phase); assumption();
                            }
                            let { focus: focus, path: path, grand_value: cached_total } = unfold(state);
                            match at(iteration,state.outer) {
                                SizedContext::Top => {
                                    have not (sized_context_flip_black(at(iteration,state.outer)) == 1) by {
                                        rewrite(at(iteration,state.outer) == SizedContext::Top);
                                        unfold(sized_context_flip_black(SizedContext::Top)); normalize();
                                    }
                                    contradiction(sized_context_flip_black(at(iteration,state.outer)) == 1);
                                },
                                SizedContext::Left(a, ancestor, shade, value, sibling_model, up_model) => {
                                    unfold(sized_context_parent(SizedContext::Left(a, ancestor, shade, value, sibling_model, up_model),0));
                                    have parent == a by {
                                        rewrite(parent == sized_context_parent(at(iteration,state.outer),0));
                                        rewrite(at(iteration,state.outer) == SizedContext::Left(a, ancestor, shade, value, sibling_model, up_model));
                                        rewrite(sized_context_parent(SizedContext::Left(a, ancestor, shade, value, sibling_model, up_model),0) == a); normalize();
                                    }
                                    unfold(sized_context_flip_black(SizedContext::Left(a, ancestor, shade, value, sibling_model, up_model)));
                                    have color_bit(shade) == 1 by {
                                        rewrite(color_bit(shade) == sized_context_flip_black(SizedContext::Left(a, ancestor, shade, value, sibling_model, up_model)));
                                        rewrite(SizedContext::Left(a, ancestor, shade, value, sibling_model, up_model) == at(iteration,state.outer)); assumption();
                                    }
                                    let { metadata: a_size, sibling: sibling, up: up } = unfold(path);
                                    have (a->__rb_parent_color & 1) == 1 by {
                                        rewrite((a->__rb_parent_color & 1) == color_bit(shade));
                                        rewrite(color_bit(shade) == 1); normalize();
                                    }
                                    step(); step();
                                    let path = fold(sized_context_at(x,root->rb_node,0,cached_total), { model: SizedContext::Left(a, ancestor, shade, value, sibling_model, up_model) }, { metadata: a_size, sibling: sibling, up: up });
                                    step();
                                    have sized_value(focus.model) == old(state.grand_value) by {
                                        rewrite(focus.model == SizedTree::Node(x, sized_context_parent(at(iteration,state.outer), 0), Color::Red, old(state.grand_value), SizedTree::Node(y, x, Color::Black, old(state.parent_value), old(state.seed), SizedTree::Empty), SizedTree::Node(z, x, Color::Black, 1, SizedTree::Empty, SizedTree::Empty)));
                                        unfold(sized_value(SizedTree::Node(x, sized_context_parent(at(iteration,state.outer), 0), Color::Red, old(state.grand_value), SizedTree::Node(y, x, Color::Black, old(state.parent_value), old(state.seed), SizedTree::Empty), SizedTree::Node(z, x, Color::Black, 1, SizedTree::Empty, SizedTree::Empty)))); normalize();
                                    }
                                    have sized_parent_is(focus.model,sized_context_parent(path.model,0)) == 1 by {
                                        rewrite(focus.model == SizedTree::Node(x, sized_context_parent(at(iteration,state.outer), 0), Color::Red, old(state.grand_value), SizedTree::Node(y, x, Color::Black, old(state.parent_value), old(state.seed), SizedTree::Empty), SizedTree::Node(z, x, Color::Black, 1, SizedTree::Empty, SizedTree::Empty)));
                                        rewrite(path.model == SizedContext::Left(a, ancestor, shade, value, sibling_model, up_model));
                                        rewrite(at(iteration,state.outer) == SizedContext::Left(a, ancestor, shade, value, sibling_model, up_model));
                                        unfold(sized_parent_is(SizedTree::Node(x, sized_context_parent(SizedContext::Left(a, ancestor, shade, value, sibling_model, up_model), 0), Color::Red, old(state.grand_value), SizedTree::Node(y, x, Color::Black, old(state.parent_value), old(state.seed), SizedTree::Empty), SizedTree::Node(z, x, Color::Black, 1, SizedTree::Empty, SizedTree::Empty)),sized_context_parent(SizedContext::Left(a, ancestor, shade, value, sibling_model, up_model),0))); normalize();
                                    }
                                    let { whole: whole } = restore_sized_context(x,root->rb_node,0,cached_total, { path: path, sub: focus });
                                    have whole.model == sized_plug(SizedContext::Left(a, ancestor, shade, value, sibling_model, up_model), sized_context_flip_subtree(SizedContextFlipPhase::Done(x,y,z), old(node), SizedContext::Left(a, ancestor, shade, value, sibling_model, up_model), old(state.seed), old(state.parent_value), old(state.grand_value))) by {
                                        unfold(sized_context_flip_subtree(SizedContextFlipPhase::Done(x,y,z), old(node), SizedContext::Left(a, ancestor, shade, value, sibling_model, up_model), old(state.seed), old(state.parent_value), old(state.grand_value))); simp();
                                    }
                                    have whole.model == sized_plug(old(state.outer), sized_context_flip_subtree(sized_context_flip_finish(old(state.phase)), old(node), old(state.outer), old(state.seed), old(state.parent_value), old(state.grand_value))) by {
                                        rewrite(sized_context_flip_finish(old(state.phase)) == SizedContextFlipPhase::Done(x,y,z));
                                        rewrite(old(state.outer) == SizedContext::Left(a, ancestor, shade, value, sibling_model, up_model)); assumption();
                                    }
                                    let state = fold(sized_context_flip_at(old(node),root), { phase: SizedContextFlipPhase::Done(x,y,z), model: whole.model, context: SizedContext::Top, outer: SizedContext::Left(a, ancestor, shade, value, sibling_model, up_model), seed: old(state.seed), parent_value: old(state.parent_value), grand_value: old(state.grand_value) }, { whole: whole });
                                    have state.model == sized_plug(old(state.outer), sized_context_flip_subtree(sized_context_flip_finish(old(state.phase)), old(node), old(state.outer), old(state.seed), old(state.parent_value), old(state.grand_value))) by { assumption(); }
                                    step();
                                },
                                SizedContext::Right(a, ancestor, shade, value, sibling_model, up_model) => {
                                    unfold(sized_context_parent(SizedContext::Right(a, ancestor, shade, value, sibling_model, up_model),0));
                                    have parent == a by {
                                        rewrite(parent == sized_context_parent(at(iteration,state.outer),0));
                                        rewrite(at(iteration,state.outer) == SizedContext::Right(a, ancestor, shade, value, sibling_model, up_model));
                                        rewrite(sized_context_parent(SizedContext::Right(a, ancestor, shade, value, sibling_model, up_model),0) == a); normalize();
                                    }
                                    unfold(sized_context_flip_black(SizedContext::Right(a, ancestor, shade, value, sibling_model, up_model)));
                                    have color_bit(shade) == 1 by {
                                        rewrite(color_bit(shade) == sized_context_flip_black(SizedContext::Right(a, ancestor, shade, value, sibling_model, up_model)));
                                        rewrite(SizedContext::Right(a, ancestor, shade, value, sibling_model, up_model) == at(iteration,state.outer)); assumption();
                                    }
                                    let { metadata: a_size, sibling: sibling, up: up } = unfold(path);
                                    have (a->__rb_parent_color & 1) == 1 by {
                                        rewrite((a->__rb_parent_color & 1) == color_bit(shade));
                                        rewrite(color_bit(shade) == 1); normalize();
                                    }
                                    step(); step();
                                    let path = fold(sized_context_at(x,root->rb_node,0,cached_total), { model: SizedContext::Right(a, ancestor, shade, value, sibling_model, up_model) }, { metadata: a_size, sibling: sibling, up: up });
                                    step();
                                    have sized_value(focus.model) == old(state.grand_value) by {
                                        rewrite(focus.model == SizedTree::Node(x, sized_context_parent(at(iteration,state.outer), 0), Color::Red, old(state.grand_value), SizedTree::Node(y, x, Color::Black, old(state.parent_value), old(state.seed), SizedTree::Empty), SizedTree::Node(z, x, Color::Black, 1, SizedTree::Empty, SizedTree::Empty)));
                                        unfold(sized_value(SizedTree::Node(x, sized_context_parent(at(iteration,state.outer), 0), Color::Red, old(state.grand_value), SizedTree::Node(y, x, Color::Black, old(state.parent_value), old(state.seed), SizedTree::Empty), SizedTree::Node(z, x, Color::Black, 1, SizedTree::Empty, SizedTree::Empty)))); normalize();
                                    }
                                    have sized_parent_is(focus.model,sized_context_parent(path.model,0)) == 1 by {
                                        rewrite(focus.model == SizedTree::Node(x, sized_context_parent(at(iteration,state.outer), 0), Color::Red, old(state.grand_value), SizedTree::Node(y, x, Color::Black, old(state.parent_value), old(state.seed), SizedTree::Empty), SizedTree::Node(z, x, Color::Black, 1, SizedTree::Empty, SizedTree::Empty)));
                                        rewrite(path.model == SizedContext::Right(a, ancestor, shade, value, sibling_model, up_model));
                                        rewrite(at(iteration,state.outer) == SizedContext::Right(a, ancestor, shade, value, sibling_model, up_model));
                                        unfold(sized_parent_is(SizedTree::Node(x, sized_context_parent(SizedContext::Right(a, ancestor, shade, value, sibling_model, up_model), 0), Color::Red, old(state.grand_value), SizedTree::Node(y, x, Color::Black, old(state.parent_value), old(state.seed), SizedTree::Empty), SizedTree::Node(z, x, Color::Black, 1, SizedTree::Empty, SizedTree::Empty)),sized_context_parent(SizedContext::Right(a, ancestor, shade, value, sibling_model, up_model),0))); normalize();
                                    }
                                    let { whole: whole } = restore_sized_context(x,root->rb_node,0,cached_total, { path: path, sub: focus });
                                    have whole.model == sized_plug(SizedContext::Right(a, ancestor, shade, value, sibling_model, up_model), sized_context_flip_subtree(SizedContextFlipPhase::Done(x,y,z), old(node), SizedContext::Right(a, ancestor, shade, value, sibling_model, up_model), old(state.seed), old(state.parent_value), old(state.grand_value))) by {
                                        unfold(sized_context_flip_subtree(SizedContextFlipPhase::Done(x,y,z), old(node), SizedContext::Right(a, ancestor, shade, value, sibling_model, up_model), old(state.seed), old(state.parent_value), old(state.grand_value))); simp();
                                    }
                                    have whole.model == sized_plug(old(state.outer), sized_context_flip_subtree(sized_context_flip_finish(old(state.phase)), old(node), old(state.outer), old(state.seed), old(state.parent_value), old(state.grand_value))) by {
                                        rewrite(sized_context_flip_finish(old(state.phase)) == SizedContextFlipPhase::Done(x,y,z));
                                        rewrite(old(state.outer) == SizedContext::Right(a, ancestor, shade, value, sibling_model, up_model)); assumption();
                                    }
                                    let state = fold(sized_context_flip_at(old(node),root), { phase: SizedContextFlipPhase::Done(x,y,z), model: whole.model, context: SizedContext::Top, outer: SizedContext::Right(a, ancestor, shade, value, sibling_model, up_model), seed: old(state.seed), parent_value: old(state.parent_value), grand_value: old(state.grand_value) }, { whole: whole });
                                    have state.model == sized_plug(old(state.outer), sized_context_flip_subtree(sized_context_flip_finish(old(state.phase)), old(node), old(state.outer), old(state.seed), old(state.parent_value), old(state.grand_value))) by { assumption(); }
                                    step();
                                },
                            }
                        },
                        SizedContextFlipPhase::Before(x, y, z) => {
                            have parent == y by {
                                rewrite(parent == sized_context_flip_parent(state.phase, state.outer));
                                rewrite(state.phase == SizedContextFlipPhase::Before(x, y, z));
                                unfold(sized_context_flip_parent(SizedContextFlipPhase::Before(x, y, z),state.outer)); normalize();
                            }
                            have node == old(node) by {
                                rewrite(node == sized_context_flip_focus(state.phase,old(node)));
                                rewrite(state.phase == SizedContextFlipPhase::Before(x, y, z));
                                unfold(sized_context_flip_focus(SizedContextFlipPhase::Before(x, y, z),old(node))); normalize();
                            }
                            let { focus: focus, path: path, grand_value: cached_total } = unfold(state);
                            let { metadata: p_size, sibling: p_right, up: g_path } = unfold(path);
                            let { metadata: g_size, sibling: u_tree, up: top } = unfold(g_path);
                            let { metadata: u_size, left: u_left, right: u_right } = unfold(u_tree);
                            unfold(color_bit(Color::Red)); unfold(color_bit(Color::Black));
                            have y->__rb_parent_color == address(x) by {
                                rewrite(y->__rb_parent_color == address(x) + (y->__rb_parent_color & 1));
                                rewrite((y->__rb_parent_color & 1) == color_bit(Color::Red));
                                rewrite(color_bit(Color::Red) == 0); normalize();
                            }
                            step(); step(); step(); step(); step(); step(); step();
                            step();
                            step(); step(); step(); step(); step();
                            let u_tree = fold(sized_at(z), { model: SizedTree::Node(z, x, Color::Black, 1, SizedTree::Empty, SizedTree::Empty) }, { metadata: u_size, left: u_left, right: u_right });
                            have sized_parent_is(focus.model,y) == 1 by {
                                rewrite(focus.model == old(state.seed));
                                rewrite(old(state.seed) == SizedTree::Node(old(node), y, Color::Red, sized_value(old(state.seed)), sized_left(old(state.seed)), sized_right(old(state.seed))));
                                unfold(sized_parent_is(SizedTree::Node(old(node), y, Color::Red, sized_value(old(state.seed)), sized_left(old(state.seed)), sized_right(old(state.seed))),y)); normalize();
                            }
                            unfold(sized_parent_is(SizedTree::Empty,y));
                            unfold(sized_value(SizedTree::Empty));
                            unfold(sized_value(old(state.seed)));
                            have to_integer(old(state.parent_value)) == 1 + to_integer(sized_value(old(state.seed))) + to_integer(sized_value(SizedTree::Empty)) by {
                                rewrite(old(state.parent_value) == at(iteration,state.parent_value));
                                rewrite(old(state.seed) == at(iteration,state.seed));
                                assumption();
                            }
                            let p_tree = fold(sized_at(y), { model: SizedTree::Node(y, x, Color::Black, old(state.parent_value), old(state.seed), SizedTree::Empty) }, { metadata: p_size, left: focus, right: p_right });
                            have sized_parent_is(p_tree.model,x) == 1 by {
                                rewrite(p_tree.model == SizedTree::Node(y, x, Color::Black, old(state.parent_value), old(state.seed), SizedTree::Empty));
                                unfold(sized_parent_is(SizedTree::Node(y, x, Color::Black, old(state.parent_value), old(state.seed), SizedTree::Empty),x)); normalize();
                            }
                            have sized_parent_is(u_tree.model,x) == 1 by {
                                rewrite(u_tree.model == SizedTree::Node(z, x, Color::Black, 1, SizedTree::Empty, SizedTree::Empty));
                                unfold(sized_parent_is(SizedTree::Node(z, x, Color::Black, 1, SizedTree::Empty, SizedTree::Empty),x)); normalize();
                            }
                            unfold(sized_value(SizedTree::Node(y, x, Color::Black, old(state.parent_value), old(state.seed), SizedTree::Empty)));
                            unfold(sized_value(SizedTree::Node(z, x, Color::Black, 1, SizedTree::Empty, SizedTree::Empty)));
                            unfold(sized_value(SizedTree::Node(z, x, Color::Red, 1, SizedTree::Empty, SizedTree::Empty)));
                            have to_integer(old(state.grand_value)) == 1 + to_integer(sized_value(SizedTree::Node(y, x, Color::Black, old(state.parent_value), old(state.seed), SizedTree::Empty))) + to_integer(sized_value(SizedTree::Node(z, x, Color::Black, 1, SizedTree::Empty, SizedTree::Empty))) by {
                                rewrite(sized_value(SizedTree::Node(y, x, Color::Black, old(state.parent_value), old(state.seed), SizedTree::Empty)) == old(state.parent_value));
                                rewrite(sized_value(SizedTree::Node(z, x, Color::Black, 1, SizedTree::Empty, SizedTree::Empty)) == sized_value(SizedTree::Node(z, x, Color::Red, 1, SizedTree::Empty, SizedTree::Empty)));
                                rewrite(old(state.grand_value) == at(iteration,state.grand_value));
                                rewrite(old(state.parent_value) == at(iteration,state.parent_value));
                                assumption();
                            }
                            let focus = fold(sized_at(x), { model: SizedTree::Node(x, sized_context_parent(at(iteration,state.outer),0), Color::Red, old(state.grand_value), SizedTree::Node(y, x, Color::Black, old(state.parent_value), old(state.seed), SizedTree::Empty), SizedTree::Node(z, x, Color::Black, 1, SizedTree::Empty, SizedTree::Empty)) }, { metadata: g_size, left: p_tree, right: u_tree });
                            let state = fold(sized_context_flip_at(old(node),root), { phase: SizedContextFlipPhase::After(x, y, z), model: SizedTree::Node(x, sized_context_parent(at(iteration,state.outer),0), Color::Red, old(state.grand_value), SizedTree::Node(y, x, Color::Black, old(state.parent_value), old(state.seed), SizedTree::Empty), SizedTree::Node(z, x, Color::Black, 1, SizedTree::Empty, SizedTree::Empty)), context: at(iteration,state.outer), outer: at(iteration,state.outer), seed: old(state.seed), parent_value: old(state.parent_value), grand_value: old(state.grand_value) }, { focus: focus, path: top });
                            apply(sized_context_depth_nonnegative(state.outer));
                            have 0 <= sized_context_depth(state.context) by { rewrite(state.context == state.outer); assumption(); }
                            have sized_context_depth(state.context) < sized_context_depth(at(iteration,state.context)) by {
                                rewrite(state.context == at(iteration,state.outer));
                                rewrite(at(iteration,state.context) == SizedContext::Left(y, x, Color::Red, old(state.parent_value), SizedTree::Empty, SizedContext::Left(x, sized_context_parent(at(iteration,state.outer),0), Color::Black, old(state.grand_value), SizedTree::Node(z, x, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), at(iteration,state.outer))));
                                unfold(sized_context_depth(SizedContext::Left(y, x, Color::Red, old(state.parent_value), SizedTree::Empty, SizedContext::Left(x, sized_context_parent(at(iteration,state.outer),0), Color::Black, old(state.grand_value), SizedTree::Node(z, x, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), at(iteration,state.outer)))));
                                unfold(sized_context_depth(SizedContext::Left(x, sized_context_parent(at(iteration,state.outer),0), Color::Black, old(state.grand_value), SizedTree::Node(z, x, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), at(iteration,state.outer))));
                                arithmetic();
                            }
                            unfold(sized_context_flip_focus(SizedContextFlipPhase::After(x, y, z),old(node)));
                            unfold(sized_context_flip_parent(SizedContextFlipPhase::After(x, y, z),state.outer));
                            unfold(sized_context_flip_finish(SizedContextFlipPhase::Before(x, y, z)));
                            have sized_context_flip_finish(state.phase) == sized_context_flip_finish(old(state.phase)) by {
                                rewrite(state.phase == SizedContextFlipPhase::After(x, y, z));
                                unfold(sized_context_flip_finish(SizedContextFlipPhase::After(x, y, z)));
                                rewrite(SizedContextFlipPhase::Done(x, y, z) == sized_context_flip_finish(SizedContextFlipPhase::Before(x, y, z)));
                                rewrite(SizedContextFlipPhase::Before(x, y, z) == at(iteration,state.phase)); assumption();
                            }
                            have sized_context_flip_running(state.phase) == 1 by {
                                rewrite(state.phase == SizedContextFlipPhase::After(x, y, z));
                                unfold(sized_context_flip_running(SizedContextFlipPhase::After(x, y, z))); normalize();
                            }
                            step();
                            close_invariants() by simp();
                        },
                    }
                }
            }
            execute(); simp();
        },
    }
}

void __rb_insert_augmented(struct rb_node* node, struct rb_root* root,
                  void (*augment_rotate)(struct rb_node*, struct rb_node*)) {
    owns state: sized_context_flip_at(node, root);
    requires sized_context_flip_pending(state.phase) == 1;
    ensures state.seed == old(state.seed);
    ensures state.parent_value == old(state.parent_value);
    ensures state.grand_value == old(state.grand_value);
    ensures state.phase == sized_context_flip_finish(old(state.phase));
    ensures state.model == sized_plug(old(state.outer), sized_context_flip_subtree(sized_context_flip_finish(old(state.phase)), node, old(state.outer), old(state.seed), old(state.parent_value), old(state.grand_value)));
} by {
    step(__rb_insert(node, root, augment_rotate), { state: state });
    execute(); simp();
}

void rb_insert_augmented(struct rb_node* node, struct rb_root* root,
                  const struct rb_augment_callbacks* augment) {
    views augment->rotate;
    owns state: sized_context_flip_at(node, root);
    requires sized_context_flip_pending(state.phase) == 1;
    ensures state.seed == old(state.seed);
    ensures state.parent_value == old(state.parent_value);
    ensures state.grand_value == old(state.grand_value);
    ensures state.phase == sized_context_flip_finish(old(state.phase));
    ensures state.model == sized_plug(old(state.outer), sized_context_flip_subtree(sized_context_flip_finish(old(state.phase)), node, old(state.outer), old(state.seed), old(state.parent_value), old(state.grand_value)));
} by {
    step(__rb_insert_augmented(node, root, augment->rotate), { state: state });
    execute(); simp();
}
