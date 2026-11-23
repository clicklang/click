// The two stopping cases shared by arbitrary insertion color-flip chains.
verifying "rb_insert_augmented.c";
verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_insert_flips.click";

// Retain complete node observations through read-only C steps.
resource flip_boundary_node_frame(p: struct rb_node*, up: struct rb_node*) {
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

resource flip_boundary_root_link(root: struct rb_root*) {
    field node: int32*;
    owns root->rb_node;
    fact root->rb_node == node;
}

// Carry the common observations through the join of the stopping paths.
resource flip_boundary_frame(root: struct rb_root*) {
    field root_node: int32*;
    field chain: SizedFlipChain;
    field model: SizedTree;
    field context: SizedContext;
    match model {
        SizedTree::Empty => { fact false; },
        SizedTree::Node(node, parent, shade, value, left, right) => {
            owns root->rb_node;
            owns focus: sized_at(node);
            owns path: sized_context_at(node, root->rb_node, 0, value);
            fact focus.model == model;
            fact path.model == context;
            fact parent == sized_context_parent(context, 0);
            fact root->rb_node == root_node;
        },
    }
}

void __rb_insert(struct rb_node* node, struct rb_root* root,
                 void (*augment_rotate)(struct rb_node*, struct rb_node*)) {
    consumes state: flip_boundary_frame(root);
    requires sized_flip_stopped(state.chain) == 1;
    requires sized_flip_allowed(state.chain) == 1;
    requires state.context == sized_flip_context(state.chain);
    requires node == sized_flip_node(state.model);
    requires sized_flip_color(state.model) == 0;
    produces root->rb_node;
    produces whole: sized_at(old(root->rb_node));
    ensures root->rb_node == old(root->rb_node);
    ensures whole.model == sized_flip_result(old(state.chain), old(state.model));
    ensures sized_parent_is(whole.model, 0) == 1;
} by {
    match state.model {
        SizedTree::Empty => { unfold(state); contradiction(); },
        SizedTree::Node(identity, ancestor, shade, value, left, right) => {
            have node == identity by {
                rewrite(node, sized_flip_node(state.model));
                rewrite(state.model, SizedTree::Node(identity, ancestor, shade, value, left, right));
                unfold(sized_flip_node(SizedTree::Node(identity, ancestor, shade, value, left, right))); normalize();
            }
            have color_bit(shade) == 0 by {
                unfold(sized_flip_color(SizedTree::Node(identity, ancestor, shade, value, left, right)));
                rewrite(color_bit(shade), sized_flip_color(SizedTree::Node(identity, ancestor, shade, value, left, right)));
                rewrite(SizedTree::Node(identity, ancestor, shade, value, left, right), state.model); known();
            }
            let { focus: focus, path: path } = unfold(state);
            let { metadata: metadata, left: l, right: r } = unfold(focus);
            have node->__rb_parent_color == address(ancestor) by {
                rewrite(node->__rb_parent_color, address(ancestor) + (node->__rb_parent_color & 1));
                rewrite((node->__rb_parent_color & 1), color_bit(shade));
                rewrite(color_bit(shade), 0); normalize();
            }
            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == ancestor by { known(); }
            have ancestor == sized_context_parent(old(state.context), 0) by known();
            have root->rb_node == old(root->rb_node) by known();
            let initial_root = fold(flip_boundary_root_link(root), { node: old(root->rb_node) });
            let initial_focus = fold(flip_boundary_node_frame(node, ancestor), { color: shade, word: node->__rb_parent_color, left: node->rb_left, right: node->rb_right });
            step(); step(); step(); step();
            unfold(initial_focus); unfold(initial_root);
            have root->rb_node == old(root->rb_node) by known();
            let focus = fold(sized_at(node), { model: SizedTree::Node(identity, ancestor, shade, value, left, right), metadata: metadata, left: l, right: r });
            have focus.model == old(state.model) by known();
            let state = fold(flip_boundary_frame(root), {
                root_node: old(root->rb_node), chain: old(state.chain), model: old(state.model), context: old(state.context),
                focus: focus, path: path
            });
            step(); // Declare tmp before the C loop.
            loop {
                owns state: flip_boundary_frame(root);
                decreases 0;
                invariant state.model == old(state.model);
                invariant state.context == old(state.context);
                invariant state.chain == old(state.chain);
                invariant state.root_node == old(root->rb_node);
                invariant parent == ancestor;
                invariant node == old(node);
                invariant node == identity;
                initialize by solve();
                maintain by {
                    let { focus: focus, path: path } = unfold(state);
                    have root->rb_node == old(root->rb_node) by known();
                    let loop_root = fold(flip_boundary_root_link(root), { node: old(root->rb_node) });
                    match old(state.chain) {
                        SizedFlipChain::LL(p, g, pv, gv, other, uncle, up) => {
                            have not (sized_flip_stopped(old(state.chain)) == 1) by {
                                rewrite(old(state.chain), SizedFlipChain::LL(p, g, pv, gv, other, uncle, up));
                                unfold(sized_flip_stopped(SizedFlipChain::LL(p, g, pv, gv, other, uncle, up))); normalize();
                            }
                            contradiction(sized_flip_stopped(old(state.chain)) == 1);
                        },
                        SizedFlipChain::LR(p, g, pv, gv, other, uncle, up) => {
                            have not (sized_flip_stopped(old(state.chain)) == 1) by {
                                rewrite(old(state.chain), SizedFlipChain::LR(p, g, pv, gv, other, uncle, up));
                                unfold(sized_flip_stopped(SizedFlipChain::LR(p, g, pv, gv, other, uncle, up))); normalize();
                            }
                            contradiction(sized_flip_stopped(old(state.chain)) == 1);
                        },
                        SizedFlipChain::RL(p, g, pv, gv, other, uncle, up) => {
                            have not (sized_flip_stopped(old(state.chain)) == 1) by {
                                rewrite(old(state.chain), SizedFlipChain::RL(p, g, pv, gv, other, uncle, up));
                                unfold(sized_flip_stopped(SizedFlipChain::RL(p, g, pv, gv, other, uncle, up))); normalize();
                            }
                            contradiction(sized_flip_stopped(old(state.chain)) == 1);
                        },
                        SizedFlipChain::RR(p, g, pv, gv, other, uncle, up) => {
                            have not (sized_flip_stopped(old(state.chain)) == 1) by {
                                rewrite(old(state.chain), SizedFlipChain::RR(p, g, pv, gv, other, uncle, up));
                                unfold(sized_flip_stopped(SizedFlipChain::RR(p, g, pv, gv, other, uncle, up))); normalize();
                            }
                            contradiction(sized_flip_stopped(old(state.chain)) == 1);
                        },
                        SizedFlipChain::Root => {
                            have path.model == SizedContext::Top by {
                                rewrite(path.model, old(state.context));
                                rewrite(old(state.context), sized_flip_context(old(state.chain)));
                                rewrite(old(state.chain), SizedFlipChain::Root);
                                unfold(sized_flip_context(SizedFlipChain::Root)); normalize();
                            }
                            have parent == 0 by {
                                rewrite(parent, ancestor);
                                rewrite(ancestor, sized_context_parent(old(state.context), 0));
                                rewrite(old(state.context), sized_flip_context(old(state.chain)));
                                rewrite(old(state.chain), SizedFlipChain::Root);
                                unfold(sized_flip_context(SizedFlipChain::Root));
                                unfold(sized_context_parent(SizedContext::Top, 0)); normalize();
                            }
                            let { metadata: metadata, left: l, right: r } = unfold(focus);
                            step(); step();
                            have identity->__rb_parent_color == 1 by known();
                            have node->__rb_parent_color == 1 by { rewrite(node, identity); known(); }
                            unfold(color_bit(Color::Black));
                            have (node->__rb_parent_color & 1) == color_bit(Color::Black) by {
                                rewrite(node->__rb_parent_color, 1);
                                rewrite(color_bit(Color::Black), 1); normalize();
                            }
                            let focus = fold(sized_at(node), { model: SizedTree::Node(identity, 0, Color::Black, value, left, right), metadata: metadata, left: l, right: r });
                            have sized_value(focus.model) == value by {
                                rewrite(focus.model, SizedTree::Node(identity, 0, Color::Black, value, left, right));
                                unfold(sized_value(SizedTree::Node(identity, 0, Color::Black, value, left, right))); normalize();
                            }
                            have sized_parent_is(focus.model, sized_context_parent(path.model, 0)) == 1 by {
                                rewrite(focus.model, SizedTree::Node(identity, 0, Color::Black, value, left, right));
                                rewrite(path.model, SizedContext::Top);
                                unfold(sized_context_parent(SizedContext::Top, 0));
                                unfold(sized_parent_is(SizedTree::Node(identity, 0, Color::Black, value, left, right), 0)); normalize();
                            }
                            have sized_plug(path.model, focus.model) == sized_flip_result(old(state.chain), old(state.model)) by {
                                rewrite(path.model, SizedContext::Top);
                                rewrite(focus.model, SizedTree::Node(identity, 0, Color::Black, value, left, right));
                                rewrite(old(state.chain), SizedFlipChain::Root);
                                rewrite(old(state.model), SizedTree::Node(identity, ancestor, shade, value, left, right));
                                unfold(sized_flip_result(SizedFlipChain::Root, SizedTree::Node(identity, ancestor, shade, value, left, right)));
                                unfold(sized_recolor(SizedTree::Node(identity, ancestor, shade, value, left, right), Color::Black));
                                unfold(sized_plug(SizedContext::Top, SizedTree::Node(identity, 0, Color::Black, value, left, right)));
                                have ancestor == 0 by known();
                                rewrite(ancestor, 0); normalize();
                            }
                            have 0 == sized_context_parent(SizedContext::Top, 0) by {
                                unfold(sized_context_parent(SizedContext::Top, 0)); normalize();
                            }
                            unfold(loop_root);
                            have root->rb_node == old(root->rb_node) by known();
                            let state = fold(flip_boundary_frame(root), {
                                root_node: old(root->rb_node), chain: old(state.chain), model: SizedTree::Node(identity, 0, Color::Black, value, left, right), context: SizedContext::Top,
                                focus: focus, path: path
                            });
                            have sized_plug(state.context, state.model) == sized_flip_result(old(state.chain), old(state.model)) by known();
                            step();
                        },
                        SizedFlipChain::Stop(ctx) => {
                            have path.model == ctx by {
                                rewrite(path.model, old(state.context));
                                rewrite(old(state.context), sized_flip_context(old(state.chain)));
                                rewrite(old(state.chain), SizedFlipChain::Stop(ctx));
                                unfold(sized_flip_context(SizedFlipChain::Stop(ctx))); normalize();
                            }
                            have sized_flip_black_boundary(ctx) == 1 by {
                                unfold(sized_flip_allowed(SizedFlipChain::Stop(ctx)));
                                rewrite(sized_flip_black_boundary(ctx), sized_flip_allowed(SizedFlipChain::Stop(ctx)));
                                rewrite(SizedFlipChain::Stop(ctx), old(state.chain)); known();
                            }
                            match ctx {
                                SizedContext::Top => {
                                    have not (sized_flip_black_boundary(ctx) == 1) by {
                                        rewrite(ctx, SizedContext::Top);
                                        unfold(sized_flip_black_boundary(SizedContext::Top)); normalize();
                                    }
                                    contradiction(sized_flip_black_boundary(ctx) == 1);
                                },
                                SizedContext::Left(a, gp, color, cached, sibling, up) => {
                                    have parent == a by {
                                        rewrite(parent, ancestor);
                                        rewrite(ancestor, sized_context_parent(old(state.context), 0));
                                        rewrite(old(state.context), path.model);
                                        rewrite(path.model, ctx); rewrite(ctx, SizedContext::Left(a, gp, color, cached, sibling, up));
                                        unfold(sized_context_parent(SizedContext::Left(a, gp, color, cached, sibling, up), 0)); normalize();
                                    }
                                    have color_bit(color) == 1 by {
                                        unfold(sized_flip_black_boundary(SizedContext::Left(a, gp, color, cached, sibling, up)));
                                        rewrite(color_bit(color), sized_flip_black_boundary(SizedContext::Left(a, gp, color, cached, sibling, up)));
                                        rewrite(SizedContext::Left(a, gp, color, cached, sibling, up), ctx); known();
                                    }
                                    let { metadata: a_size, sibling: held_sibling, up: held_up } = unfold(path);
                                    have (a->__rb_parent_color & 1) == 1 by {
                                        rewrite((a->__rb_parent_color & 1), color_bit(color));
                                        rewrite(color_bit(color), 1); normalize();
                                    }
                                    step(); step(); step();
                                    unfold(loop_root);
                                    have root->rb_node == old(root->rb_node) by known();
                                    let path = fold(sized_context_at(node, root->rb_node, 0, value), { model: SizedContext::Left(a, gp, color, cached, sibling, up), metadata: a_size, sibling: held_sibling, up: held_up });
                                    have sized_value(focus.model) == value by {
                                        rewrite(focus.model, old(state.model));
                                        rewrite(old(state.model), SizedTree::Node(identity, ancestor, shade, value, left, right));
                                        unfold(sized_value(SizedTree::Node(identity, ancestor, shade, value, left, right))); normalize();
                                    }
                                    have sized_parent_is(focus.model, sized_context_parent(path.model, 0)) == 1 by {
                                        rewrite(focus.model, old(state.model));
                                        rewrite(old(state.model), SizedTree::Node(identity, ancestor, shade, value, left, right));
                                        unfold(sized_parent_is(SizedTree::Node(identity, ancestor, shade, value, left, right), sized_context_parent(path.model, 0)));
                                        normalize() using { ancestor == sized_context_parent(old(state.context), 0); old(state.context) == ctx; ctx == SizedContext::Left(a, gp, color, cached, sibling, up); path.model == SizedContext::Left(a, gp, color, cached, sibling, up); };
                                    }
                                    have sized_plug(path.model, focus.model) == sized_flip_result(old(state.chain), old(state.model)) by {
                                        rewrite(old(state.chain), SizedFlipChain::Stop(ctx));
                                        unfold(sized_flip_result(SizedFlipChain::Stop(ctx), old(state.model)));
                                        rewrite(focus.model, old(state.model));
                                        rewrite(path.model, SizedContext::Left(a, gp, color, cached, sibling, up)); rewrite(SizedContext::Left(a, gp, color, cached, sibling, up), ctx); normalize();
                                    }
                                    have ancestor == sized_context_parent(SizedContext::Left(a, gp, color, cached, sibling, up), 0) by {
                                        rewrite(ancestor, parent);
                                        unfold(sized_context_parent(SizedContext::Left(a, gp, color, cached, sibling, up), 0)); known();
                                    }
                                    let state = fold(flip_boundary_frame(root), {
                                        root_node: old(root->rb_node), chain: old(state.chain), model: SizedTree::Node(identity, ancestor, shade, value, left, right), context: SizedContext::Left(a, gp, color, cached, sibling, up),
                                        focus: focus, path: path
                                    });
                                    have sized_plug(state.context, state.model) == sized_flip_result(old(state.chain), old(state.model)) by known();
                                    step();
                                },
                                SizedContext::Right(a, gp, color, cached, sibling, up) => {
                                    have parent == a by {
                                        rewrite(parent, ancestor);
                                        rewrite(ancestor, sized_context_parent(old(state.context), 0));
                                        rewrite(old(state.context), path.model);
                                        rewrite(path.model, ctx); rewrite(ctx, SizedContext::Right(a, gp, color, cached, sibling, up));
                                        unfold(sized_context_parent(SizedContext::Right(a, gp, color, cached, sibling, up), 0)); normalize();
                                    }
                                    have color_bit(color) == 1 by {
                                        unfold(sized_flip_black_boundary(SizedContext::Right(a, gp, color, cached, sibling, up)));
                                        rewrite(color_bit(color), sized_flip_black_boundary(SizedContext::Right(a, gp, color, cached, sibling, up)));
                                        rewrite(SizedContext::Right(a, gp, color, cached, sibling, up), ctx); known();
                                    }
                                    let { metadata: a_size, sibling: held_sibling, up: held_up } = unfold(path);
                                    have (a->__rb_parent_color & 1) == 1 by {
                                        rewrite((a->__rb_parent_color & 1), color_bit(color));
                                        rewrite(color_bit(color), 1); normalize();
                                    }
                                    step(); step(); step();
                                    unfold(loop_root);
                                    have root->rb_node == old(root->rb_node) by known();
                                    let path = fold(sized_context_at(node, root->rb_node, 0, value), { model: SizedContext::Right(a, gp, color, cached, sibling, up), metadata: a_size, sibling: held_sibling, up: held_up });
                                    have sized_value(focus.model) == value by {
                                        rewrite(focus.model, old(state.model));
                                        rewrite(old(state.model), SizedTree::Node(identity, ancestor, shade, value, left, right));
                                        unfold(sized_value(SizedTree::Node(identity, ancestor, shade, value, left, right))); normalize();
                                    }
                                    have sized_parent_is(focus.model, sized_context_parent(path.model, 0)) == 1 by {
                                        rewrite(focus.model, old(state.model));
                                        rewrite(old(state.model), SizedTree::Node(identity, ancestor, shade, value, left, right));
                                        unfold(sized_parent_is(SizedTree::Node(identity, ancestor, shade, value, left, right), sized_context_parent(path.model, 0)));
                                        normalize() using { ancestor == sized_context_parent(old(state.context), 0); old(state.context) == ctx; ctx == SizedContext::Right(a, gp, color, cached, sibling, up); path.model == SizedContext::Right(a, gp, color, cached, sibling, up); };
                                    }
                                    have sized_plug(path.model, focus.model) == sized_flip_result(old(state.chain), old(state.model)) by {
                                        rewrite(old(state.chain), SizedFlipChain::Stop(ctx));
                                        unfold(sized_flip_result(SizedFlipChain::Stop(ctx), old(state.model)));
                                        rewrite(focus.model, old(state.model));
                                        rewrite(path.model, SizedContext::Right(a, gp, color, cached, sibling, up)); rewrite(SizedContext::Right(a, gp, color, cached, sibling, up), ctx); normalize();
                                    }
                                    have ancestor == sized_context_parent(SizedContext::Right(a, gp, color, cached, sibling, up), 0) by {
                                        rewrite(ancestor, parent);
                                        unfold(sized_context_parent(SizedContext::Right(a, gp, color, cached, sibling, up), 0)); known();
                                    }
                                    let state = fold(flip_boundary_frame(root), {
                                        root_node: old(root->rb_node), chain: old(state.chain), model: SizedTree::Node(identity, ancestor, shade, value, left, right), context: SizedContext::Right(a, gp, color, cached, sibling, up),
                                        focus: focus, path: path
                                    });
                                    have sized_plug(state.context, state.model) == sized_flip_result(old(state.chain), old(state.model)) by known();
                                    step();
                                },
                            }
                        },
                    }
                }
            }
            mark stopped;
            match state.model {
                SizedTree::Empty => { unfold(state); contradiction(); },
                SizedTree::Node(stopped_node, stopped_parent, stopped_shade, stopped_value, stopped_left, stopped_right) => {
                    let { focus: focus, path: path } = unfold(state);
                    have root->rb_node == old(root->rb_node) by known();
                    have focus.model == SizedTree::Node(stopped_node, stopped_parent, stopped_shade, stopped_value, stopped_left, stopped_right) by known();
                    have sized_value(focus.model) == stopped_value by {
                        rewrite(focus.model, SizedTree::Node(stopped_node, stopped_parent, stopped_shade, stopped_value, stopped_left, stopped_right));
                        unfold(sized_value(SizedTree::Node(stopped_node, stopped_parent, stopped_shade, stopped_value, stopped_left, stopped_right)));
                        normalize();
                    }
                    have stopped_parent == sized_context_parent(path.model, 0) by known();
                    have sized_parent_is(focus.model, sized_context_parent(path.model, 0)) == 1 by {
                        rewrite(focus.model, SizedTree::Node(stopped_node, stopped_parent, stopped_shade, stopped_value, stopped_left, stopped_right));
                        unfold(sized_parent_is(SizedTree::Node(stopped_node, stopped_parent, stopped_shade, stopped_value, stopped_left, stopped_right), sized_context_parent(path.model, 0)));
                        rewrite(sized_context_parent(path.model, 0), stopped_parent);
                        normalize();
                    }
                    have sized_plug(path.model, focus.model) == sized_flip_result(old(state.chain), old(state.model)) by {
                        rewrite(path.model, at(stopped, state.context));
                        rewrite(focus.model, at(stopped, state.model));
                        known();
                    }
                    let root_link = fold(flip_boundary_root_link(root), { node: old(root->rb_node) });
                    let { whole: whole } = restore_sized_context(stopped_node, old(root->rb_node), 0, stopped_value, { path: path, sub: focus });
                    step_until(function.exit);
                    unfold(root_link);
                    have root->rb_node == old(root->rb_node) by known();
                    have whole.model == sized_flip_result(old(state.chain), old(state.model)) by known();
                    have sized_parent_is(whole.model, 0) == 1 by known();
                },
            }
        },
    }
}

void __rb_insert_augmented(struct rb_node* node, struct rb_root* root,
                         void (*augment_rotate)(struct rb_node*, struct rb_node*)) {
    consumes state: sized_flip_state(root);
    requires sized_flip_stopped(state.chain) == 1;
    requires sized_flip_allowed(state.chain) == 1;
    requires state.context == sized_flip_context(state.chain);
    requires node == sized_flip_node(state.model);
    requires sized_flip_color(state.model) == 0;
    produces root->rb_node;
    produces whole: sized_at(old(root->rb_node));
    ensures root->rb_node == old(root->rb_node);
    ensures whole.model == sized_flip_result(old(state.chain), old(state.model));
    ensures sized_parent_is(whole.model, 0) == 1;
} by {
    match state.model {
        SizedTree::Empty => { unfold(state); contradiction(); },
        SizedTree::Node(node_id, parent, shade, value, left, right) => {
            let { focus: focus, path: path } = unfold(state);
            have parent == sized_context_parent(path.model, 0) by known();
            let boundary = fold(flip_boundary_frame(root), {
                root_node: root->rb_node,
                chain: old(state.chain),
                model: SizedTree::Node(node_id, parent, shade, value, left, right),
                context: path.model,
                focus: focus, path: path
            });
            let { whole: whole } = step(__rb_insert, { state: boundary });
            step_until(function.exit);
        },
    }
}

void rb_insert_augmented(struct rb_node* node, struct rb_root* root,
                         const struct rb_augment_callbacks* augment) {
    views augment->rotate;
    consumes state: sized_flip_state(root);
    requires sized_flip_stopped(state.chain) == 1;
    requires sized_flip_allowed(state.chain) == 1;
    requires state.context == sized_flip_context(state.chain);
    requires node == sized_flip_node(state.model);
    requires sized_flip_color(state.model) == 0;
    produces root->rb_node;
    produces whole: sized_at(old(root->rb_node));
    ensures root->rb_node == old(root->rb_node);
    ensures whole.model == sized_flip_result(old(state.chain), old(state.model));
    ensures sized_parent_is(whole.model, 0) == 1;
} by {
    let { whole: whole } = step(__rb_insert_augmented, { state: state });
}
