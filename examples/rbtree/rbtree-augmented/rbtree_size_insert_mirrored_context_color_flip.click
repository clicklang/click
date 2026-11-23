// A mirrored color flip beneath a black parent retains an arbitrary owned outer context.
verifying "rb_insert_augmented.c" as insert;
verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_context_flip_frames.click";

spec enum SizedMirroredContextFlipPhase {
    Before(struct rb_node*, struct rb_node*, struct rb_node*),
    After(struct rb_node*, struct rb_node*, struct rb_node*),
    Done(struct rb_node*, struct rb_node*, struct rb_node*),
}
function sized_mirrored_context_flip_pending(phase: SizedMirroredContextFlipPhase) -> int32 {
    match phase {
        SizedMirroredContextFlipPhase::Before(g, p, u) => 1,
        SizedMirroredContextFlipPhase::After(g, p, u) => 0,
        SizedMirroredContextFlipPhase::Done(g, p, u) => 0,
    }
}
function sized_mirrored_context_flip_running(phase: SizedMirroredContextFlipPhase) -> int32 {
    match phase {
        SizedMirroredContextFlipPhase::Before(g, p, u) => 1,
        SizedMirroredContextFlipPhase::After(g, p, u) => 1,
        SizedMirroredContextFlipPhase::Done(g, p, u) => 0,
    }
}
function sized_mirrored_context_flip_finish(phase: SizedMirroredContextFlipPhase) -> SizedMirroredContextFlipPhase {
    match phase {
        SizedMirroredContextFlipPhase::Before(g, p, u) => SizedMirroredContextFlipPhase::Done(g, p, u),
        SizedMirroredContextFlipPhase::After(g, p, u) => SizedMirroredContextFlipPhase::Done(g, p, u),
        SizedMirroredContextFlipPhase::Done(g, p, u) => SizedMirroredContextFlipPhase::Done(g, p, u),
    }
}
function sized_mirrored_context_flip_focus(phase: SizedMirroredContextFlipPhase, n: struct rb_node*) -> struct rb_node* {
    match phase {
        SizedMirroredContextFlipPhase::Before(g, p, u) => n,
        SizedMirroredContextFlipPhase::After(g, p, u) => g,
        SizedMirroredContextFlipPhase::Done(g, p, u) => g,
    }
}
function sized_mirrored_context_flip_parent(phase: SizedMirroredContextFlipPhase, outer: SizedContext) -> struct rb_node* {
    match phase {
        SizedMirroredContextFlipPhase::Before(g, p, u) => p,
        SizedMirroredContextFlipPhase::After(g, p, u) => sized_context_parent(outer, 0),
        SizedMirroredContextFlipPhase::Done(g, p, u) => sized_context_parent(outer, 0),
    }
}
function sized_mirrored_context_flip_black(outer: SizedContext) -> int32 {
    match outer {
        SizedContext::Top => 0,
        SizedContext::Right(a, parent, color, value, sibling, up) => color_bit(color),
        SizedContext::Left(a, parent, color, value, sibling, up) => color_bit(color),
    }
}
function sized_mirrored_context_flip_subtree(phase: SizedMirroredContextFlipPhase, n: struct rb_node*, outer: SizedContext, seed: SizedTree, parent_value: int32, grand_value: int32, other: SizedTree, uncle: SizedTree) -> SizedTree {
    match phase {
        SizedMirroredContextFlipPhase::Before(g,p,u) => SizedTree::Node(g, sized_context_parent(outer,0), Color::Red, grand_value, SizedTree::Node(u, g, Color::Black, sized_value(uncle), sized_left(uncle), sized_right(uncle)), SizedTree::Node(p, g, Color::Black, parent_value, other, seed)),
        SizedMirroredContextFlipPhase::After(g,p,u) => SizedTree::Node(g, sized_context_parent(outer,0), Color::Red, grand_value, SizedTree::Node(u, g, Color::Black, sized_value(uncle), sized_left(uncle), sized_right(uncle)), SizedTree::Node(p, g, Color::Black, parent_value, other, seed)),
        SizedMirroredContextFlipPhase::Done(g,p,u) => SizedTree::Node(g, sized_context_parent(outer,0), Color::Red, grand_value, SizedTree::Node(u, g, Color::Black, sized_value(uncle), sized_left(uncle), sized_right(uncle)), SizedTree::Node(p, g, Color::Black, parent_value, other, seed)),
    }
}
resource sized_mirrored_context_flip_at(n: struct rb_node*, root: struct rb_root*) {
    field phase: SizedMirroredContextFlipPhase;
    field model: SizedTree;
    field context: SizedContext;
    field outer: SizedContext;
    field seed: SizedTree;
    field parent_value: int32;
    field grand_value: int32;
    field other: SizedTree;
    field uncle: SizedTree;
    match phase {
        SizedMirroredContextFlipPhase::Before(g, p, u) => {
            fact uncle == SizedTree::Node(u, g, Color::Red, sized_value(uncle), sized_left(uncle), sized_right(uncle));
            fact seed == SizedTree::Node(n, p, Color::Red, sized_value(seed), sized_left(seed), sized_right(seed));
            fact sized_mirrored_context_flip_black(outer) == 1;
            owns root->rb_node;
            owns focus: sized_at(n);
            owns path: sized_context_at(n, root->rb_node, 0, sized_value(seed));
            fact focus.model == model;
            fact path.model == context;
            fact model == seed;
            fact context == SizedContext::Right(p, g, Color::Red, parent_value, other, SizedContext::Right(g, sized_context_parent(outer, 0), Color::Black, grand_value, uncle, outer));
        },
        SizedMirroredContextFlipPhase::After(g, p, u) => {
            fact uncle == SizedTree::Node(u, g, Color::Red, sized_value(uncle), sized_left(uncle), sized_right(uncle));
            fact seed == SizedTree::Node(n, p, Color::Red, sized_value(seed), sized_left(seed), sized_right(seed));
            fact sized_mirrored_context_flip_black(outer) == 1;
            owns root->rb_node;
            owns focus: sized_at(g);
            owns path: sized_context_at(g, root->rb_node, 0, grand_value);
            fact focus.model == model;
            fact path.model == context;
            fact context == outer;
            fact model == SizedTree::Node(g, sized_context_parent(outer, 0), Color::Red, grand_value, SizedTree::Node(u, g, Color::Black, sized_value(uncle), sized_left(uncle), sized_right(uncle)), SizedTree::Node(p, g, Color::Black, parent_value, other, seed));
        },
        SizedMirroredContextFlipPhase::Done(g, p, u) => {
            fact uncle == SizedTree::Node(u, g, Color::Red, sized_value(uncle), sized_left(uncle), sized_right(uncle));
            fact seed == SizedTree::Node(n, p, Color::Red, sized_value(seed), sized_left(seed), sized_right(seed));
            fact sized_mirrored_context_flip_black(outer) == 1;
            owns root->rb_node;
            owns whole: sized_at(root->rb_node);
            fact whole.model == model;
            fact context == SizedContext::Top;
        },
    }
}
// Preserve the typed parent across the read of its packed word.
struct rb_node* insert::rb_parent(struct rb_node* r) {
    consumes word: sized_context_flip_typed_parent_word(r);
    produces kept: sized_context_flip_typed_parent_word(r);
    ensures kept.link == old(word.link);
    ensures kept.word == old(word.word);
    ensures result == old((r->__rb_parent_color & ~3) as (struct rb_node*));
    ensures SizedContextFlipParent::At(result) == old(word.link);
} by {
    match word.link {
        SizedContextFlipParent::At(up) => {
            unfold(word);
            step_until(function.exit);
            let kept = fold(sized_context_flip_typed_parent_word(r), {
                link: SizedContextFlipParent::At(up),
                word: old(word.word)
            });
        },
    }
}

void insert::__rb_insert(struct rb_node* node, struct rb_root* root,
                  void (*augment_rotate)(struct rb_node*, struct rb_node*)) {
    owns state: sized_mirrored_context_flip_at(node, root);
    requires sized_mirrored_context_flip_pending(state.phase) == 1;
    ensures state.other == old(state.other);
    ensures state.uncle == old(state.uncle);
    ensures state.seed == old(state.seed);
    ensures state.parent_value == old(state.parent_value);
    ensures state.grand_value == old(state.grand_value);
    ensures state.phase == sized_mirrored_context_flip_finish(old(state.phase));
    ensures state.model == sized_plug(old(state.outer), sized_mirrored_context_flip_subtree(sized_mirrored_context_flip_finish(old(state.phase)), node, old(state.outer), old(state.seed), old(state.parent_value), old(state.grand_value), old(state.other), old(state.uncle)));
} by {
    match state.phase {
        SizedMirroredContextFlipPhase::After(g, p, u) => {
            have sized_mirrored_context_flip_pending(state.phase) != 1 by {
                rewrite(state.phase, SizedMirroredContextFlipPhase::After(g, p, u));
                unfold(sized_mirrored_context_flip_pending(SizedMirroredContextFlipPhase::After(g, p, u))); normalize();
            }
            contradiction(sized_mirrored_context_flip_pending(state.phase) == 1);
        },
        SizedMirroredContextFlipPhase::Done(g, p, u) => {
            have sized_mirrored_context_flip_pending(state.phase) != 1 by {
                rewrite(state.phase, SizedMirroredContextFlipPhase::Done(g, p, u));
                unfold(sized_mirrored_context_flip_pending(SizedMirroredContextFlipPhase::Done(g, p, u))); normalize();
            }
            contradiction(sized_mirrored_context_flip_pending(state.phase) == 1);
        },
        SizedMirroredContextFlipPhase::Before(g, p, u) => {
            let { focus: focus, path: path } = unfold(state);
            let { metadata: n_size, right: n_right, left: n_left } = unfold(focus);
            have sized_parent_is(sized_left(old(state.seed)), old(node)) == 1 by known();
            have sized_parent_is(sized_right(old(state.seed)), old(node)) == 1 by known();
            have to_integer(sized_value(old(state.seed))) ==
                1 + to_integer(sized_value(sized_left(old(state.seed)))) +
                    to_integer(sized_value(sized_right(old(state.seed)))) by known();
            unfold(color_bit(Color::Red));
            have node->__rb_parent_color == address(p) by {
                rewrite(node->__rb_parent_color, address(p) + (node->__rb_parent_color & 1));
                rewrite((node->__rb_parent_color & 1), color_bit(Color::Red));
                rewrite(color_bit(Color::Red), 0); normalize();
            }
            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == p by { known(); }
            mark m0; step();
            have *((&node->__rb_parent_color) as (int32 **)) == at(m0, *((&node->__rb_parent_color) as (int32 **))) by solve();
            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == p by { known(); }
            mark m1; step();
            have *((&node->__rb_parent_color) as (int32 **)) == at(m1, *((&node->__rb_parent_color) as (int32 **))) by solve();
            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == p by { known(); }
            mark m2; step();
            have *((&node->__rb_parent_color) as (int32 **)) == at(m2, *((&node->__rb_parent_color) as (int32 **))) by solve();
            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == p by { known(); }
            mark m3; step();
            have *((&node->__rb_parent_color) as (int32 **)) == at(m3, *((&node->__rb_parent_color) as (int32 **))) by solve();
            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == p by { known(); }
            let focus = fold(sized_at(node), { model: old(state.model), metadata: n_size, right: n_right, left: n_left });
            let state = fold(sized_mirrored_context_flip_at(node,root), { phase: SizedMirroredContextFlipPhase::Before(g, p, u), model: old(state.model), context: old(state.context), outer: old(state.outer), seed: old(state.seed), parent_value: old(state.parent_value), grand_value: old(state.grand_value), other: old(state.other), uncle: old(state.uncle), focus: focus, path: path });
            step_until(loop(0).entry);
            loop {
                owns state: sized_mirrored_context_flip_at(old(node),root);
                decreases sized_context_depth(state.context);
                invariant sized_mirrored_context_flip_running(state.phase) == 1;
                invariant sized_mirrored_context_flip_finish(state.phase) == sized_mirrored_context_flip_finish(old(state.phase));
                invariant old(state.phase) == SizedMirroredContextFlipPhase::Before(g, p, u);
                invariant state.outer == old(state.outer);
                invariant state.other == old(state.other);
                invariant state.uncle == old(state.uncle);
                invariant state.seed == old(state.seed);
                invariant state.parent_value == old(state.parent_value);
                invariant state.grand_value == old(state.grand_value);
                invariant node == sized_mirrored_context_flip_focus(state.phase, old(node));
                invariant parent == sized_mirrored_context_flip_parent(state.phase, state.outer);
                initialize by solve();
                maintain by {
                    mark iteration;
                    match state.phase {
                        SizedMirroredContextFlipPhase::Done(x, y, z) => {
                            have not (sized_mirrored_context_flip_running(state.phase) == 1) by {
                                rewrite(state.phase, SizedMirroredContextFlipPhase::Done(x, y, z));
                                unfold(sized_mirrored_context_flip_running(SizedMirroredContextFlipPhase::Done(x, y, z))); normalize();
                            }
                            contradiction(sized_mirrored_context_flip_running(state.phase) == 1);
                        },
                        SizedMirroredContextFlipPhase::After(x, y, z) => {
                            have parent == sized_context_parent(at(iteration,state.outer),0) by {
                                rewrite(parent, sized_mirrored_context_flip_parent(state.phase,at(iteration,state.outer)));
                                rewrite(state.phase, SizedMirroredContextFlipPhase::After(x,y,z));
                                unfold(sized_mirrored_context_flip_parent(SizedMirroredContextFlipPhase::After(x,y,z),at(iteration,state.outer))); normalize();
                            }
                            have node == x by {
                                rewrite(node, sized_mirrored_context_flip_focus(state.phase,old(node)));
                                rewrite(state.phase, SizedMirroredContextFlipPhase::After(x,y,z));
                                unfold(sized_mirrored_context_flip_focus(SizedMirroredContextFlipPhase::After(x,y,z),old(node))); normalize();
                            }
                            unfold(sized_mirrored_context_flip_finish(SizedMirroredContextFlipPhase::After(x,y,z)));
                            have SizedMirroredContextFlipPhase::Done(x,y,z) == sized_mirrored_context_flip_finish(old(state.phase)) by {
                                rewrite(SizedMirroredContextFlipPhase::Done(x,y,z), sized_mirrored_context_flip_finish(SizedMirroredContextFlipPhase::After(x,y,z)));
                                rewrite(SizedMirroredContextFlipPhase::After(x,y,z), state.phase); known();
                            }
                            let { focus: focus, path: path, grand_value: cached_total } = unfold(state);
                            match at(iteration,state.outer) {
                                SizedContext::Top => {
                                    have not (sized_mirrored_context_flip_black(at(iteration,state.outer)) == 1) by {
                                        rewrite(at(iteration,state.outer), SizedContext::Top);
                                        unfold(sized_mirrored_context_flip_black(SizedContext::Top)); normalize();
                                    }
                                    contradiction(sized_mirrored_context_flip_black(at(iteration,state.outer)) == 1);
                                },
                                SizedContext::Right(a, ancestor, shade, value, sibling_model, up_model) => {
                                    unfold(sized_context_parent(SizedContext::Right(a, ancestor, shade, value, sibling_model, up_model),0));
                                    have parent == a by {
                                        rewrite(parent, sized_context_parent(at(iteration,state.outer),0));
                                        rewrite(at(iteration,state.outer), SizedContext::Right(a, ancestor, shade, value, sibling_model, up_model));
                                        rewrite(sized_context_parent(SizedContext::Right(a, ancestor, shade, value, sibling_model, up_model),0), a); normalize();
                                    }
                                    unfold(sized_mirrored_context_flip_black(SizedContext::Right(a, ancestor, shade, value, sibling_model, up_model)));
                                    have color_bit(shade) == 1 by {
                                        rewrite(color_bit(shade), sized_mirrored_context_flip_black(SizedContext::Right(a, ancestor, shade, value, sibling_model, up_model)));
                                        rewrite(SizedContext::Right(a, ancestor, shade, value, sibling_model, up_model), at(iteration,state.outer)); known();
                                    }
                                    let { metadata: a_size, sibling: sibling, up: up } = unfold(path);
                                    have (a->__rb_parent_color & 1) == 1 by {
                                        rewrite((a->__rb_parent_color & 1), color_bit(shade));
                                        rewrite(color_bit(shade), 1); normalize();
                                    }
                                    step(); step();
                                    let path = fold(sized_context_at(x,root->rb_node,0,cached_total), { model: SizedContext::Right(a, ancestor, shade, value, sibling_model, up_model), metadata: a_size, sibling: sibling, up: up });
                                    step();
                                    have sized_value(focus.model) == old(state.grand_value) by {
                                        rewrite(focus.model, SizedTree::Node(x, sized_context_parent(at(iteration,state.outer), 0), Color::Red, old(state.grand_value), SizedTree::Node(z, x, Color::Black, sized_value(old(state.uncle)), sized_left(old(state.uncle)), sized_right(old(state.uncle))), SizedTree::Node(y, x, Color::Black, old(state.parent_value), old(state.other), old(state.seed))));
                                        unfold(sized_value(SizedTree::Node(x, sized_context_parent(at(iteration,state.outer), 0), Color::Red, old(state.grand_value), SizedTree::Node(z, x, Color::Black, sized_value(old(state.uncle)), sized_left(old(state.uncle)), sized_right(old(state.uncle))), SizedTree::Node(y, x, Color::Black, old(state.parent_value), old(state.other), old(state.seed))))); normalize();
                                    }
                                    have sized_parent_is(focus.model,sized_context_parent(path.model,0)) == 1 by {
                                        rewrite(focus.model, SizedTree::Node(x, sized_context_parent(at(iteration,state.outer), 0), Color::Red, old(state.grand_value), SizedTree::Node(z, x, Color::Black, sized_value(old(state.uncle)), sized_left(old(state.uncle)), sized_right(old(state.uncle))), SizedTree::Node(y, x, Color::Black, old(state.parent_value), old(state.other), old(state.seed))));
                                        rewrite(path.model, SizedContext::Right(a, ancestor, shade, value, sibling_model, up_model));
                                        rewrite(at(iteration,state.outer), SizedContext::Right(a, ancestor, shade, value, sibling_model, up_model));
                                        unfold(sized_parent_is(SizedTree::Node(x, sized_context_parent(SizedContext::Right(a, ancestor, shade, value, sibling_model, up_model), 0), Color::Red, old(state.grand_value), SizedTree::Node(z, x, Color::Black, sized_value(old(state.uncle)), sized_left(old(state.uncle)), sized_right(old(state.uncle))), SizedTree::Node(y, x, Color::Black, old(state.parent_value), old(state.other), old(state.seed))),sized_context_parent(SizedContext::Right(a, ancestor, shade, value, sibling_model, up_model),0))); normalize();
                                    }
                                    let { whole: whole } = restore_sized_context(x,root->rb_node,0,cached_total, { path: path, sub: focus });
                                    have whole.model == sized_plug(SizedContext::Right(a, ancestor, shade, value, sibling_model, up_model), sized_mirrored_context_flip_subtree(SizedMirroredContextFlipPhase::Done(x,y,z), old(node), SizedContext::Right(a, ancestor, shade, value, sibling_model, up_model), old(state.seed), old(state.parent_value), old(state.grand_value), old(state.other), old(state.uncle))) by {
                                        unfold(sized_mirrored_context_flip_subtree(SizedMirroredContextFlipPhase::Done(x,y,z), old(node), SizedContext::Right(a, ancestor, shade, value, sibling_model, up_model), old(state.seed), old(state.parent_value), old(state.grand_value), old(state.other), old(state.uncle))); solve();
                                    }
                                    have whole.model == sized_plug(old(state.outer), sized_mirrored_context_flip_subtree(sized_mirrored_context_flip_finish(old(state.phase)), old(node), old(state.outer), old(state.seed), old(state.parent_value), old(state.grand_value), old(state.other), old(state.uncle))) by {
                                        rewrite(sized_mirrored_context_flip_finish(old(state.phase)), SizedMirroredContextFlipPhase::Done(x,y,z));
                                        rewrite(old(state.outer), SizedContext::Right(a, ancestor, shade, value, sibling_model, up_model)); known();
                                    }
                                    let state = fold(sized_mirrored_context_flip_at(old(node),root), { phase: SizedMirroredContextFlipPhase::Done(x,y,z), model: whole.model, context: SizedContext::Top, outer: SizedContext::Right(a, ancestor, shade, value, sibling_model, up_model), seed: old(state.seed), parent_value: old(state.parent_value), grand_value: old(state.grand_value), other: old(state.other), uncle: old(state.uncle), whole: whole });
                                    have state.model == sized_plug(old(state.outer), sized_mirrored_context_flip_subtree(sized_mirrored_context_flip_finish(old(state.phase)), old(node), old(state.outer), old(state.seed), old(state.parent_value), old(state.grand_value), old(state.other), old(state.uncle))) by { known(); }
                                    step();
                                },
                                SizedContext::Left(a, ancestor, shade, value, sibling_model, up_model) => {
                                    unfold(sized_context_parent(SizedContext::Left(a, ancestor, shade, value, sibling_model, up_model),0));
                                    have parent == a by {
                                        rewrite(parent, sized_context_parent(at(iteration,state.outer),0));
                                        rewrite(at(iteration,state.outer), SizedContext::Left(a, ancestor, shade, value, sibling_model, up_model));
                                        rewrite(sized_context_parent(SizedContext::Left(a, ancestor, shade, value, sibling_model, up_model),0), a); normalize();
                                    }
                                    unfold(sized_mirrored_context_flip_black(SizedContext::Left(a, ancestor, shade, value, sibling_model, up_model)));
                                    have color_bit(shade) == 1 by {
                                        rewrite(color_bit(shade), sized_mirrored_context_flip_black(SizedContext::Left(a, ancestor, shade, value, sibling_model, up_model)));
                                        rewrite(SizedContext::Left(a, ancestor, shade, value, sibling_model, up_model), at(iteration,state.outer)); known();
                                    }
                                    let { metadata: a_size, sibling: sibling, up: up } = unfold(path);
                                    have (a->__rb_parent_color & 1) == 1 by {
                                        rewrite((a->__rb_parent_color & 1), color_bit(shade));
                                        rewrite(color_bit(shade), 1); normalize();
                                    }
                                    step(); step();
                                    let path = fold(sized_context_at(x,root->rb_node,0,cached_total), { model: SizedContext::Left(a, ancestor, shade, value, sibling_model, up_model), metadata: a_size, sibling: sibling, up: up });
                                    step();
                                    have sized_value(focus.model) == old(state.grand_value) by {
                                        rewrite(focus.model, SizedTree::Node(x, sized_context_parent(at(iteration,state.outer), 0), Color::Red, old(state.grand_value), SizedTree::Node(z, x, Color::Black, sized_value(old(state.uncle)), sized_left(old(state.uncle)), sized_right(old(state.uncle))), SizedTree::Node(y, x, Color::Black, old(state.parent_value), old(state.other), old(state.seed))));
                                        unfold(sized_value(SizedTree::Node(x, sized_context_parent(at(iteration,state.outer), 0), Color::Red, old(state.grand_value), SizedTree::Node(z, x, Color::Black, sized_value(old(state.uncle)), sized_left(old(state.uncle)), sized_right(old(state.uncle))), SizedTree::Node(y, x, Color::Black, old(state.parent_value), old(state.other), old(state.seed))))); normalize();
                                    }
                                    have sized_parent_is(focus.model,sized_context_parent(path.model,0)) == 1 by {
                                        rewrite(focus.model, SizedTree::Node(x, sized_context_parent(at(iteration,state.outer), 0), Color::Red, old(state.grand_value), SizedTree::Node(z, x, Color::Black, sized_value(old(state.uncle)), sized_left(old(state.uncle)), sized_right(old(state.uncle))), SizedTree::Node(y, x, Color::Black, old(state.parent_value), old(state.other), old(state.seed))));
                                        rewrite(path.model, SizedContext::Left(a, ancestor, shade, value, sibling_model, up_model));
                                        rewrite(at(iteration,state.outer), SizedContext::Left(a, ancestor, shade, value, sibling_model, up_model));
                                        unfold(sized_parent_is(SizedTree::Node(x, sized_context_parent(SizedContext::Left(a, ancestor, shade, value, sibling_model, up_model), 0), Color::Red, old(state.grand_value), SizedTree::Node(z, x, Color::Black, sized_value(old(state.uncle)), sized_left(old(state.uncle)), sized_right(old(state.uncle))), SizedTree::Node(y, x, Color::Black, old(state.parent_value), old(state.other), old(state.seed))),sized_context_parent(SizedContext::Left(a, ancestor, shade, value, sibling_model, up_model),0))); normalize();
                                    }
                                    let { whole: whole } = restore_sized_context(x,root->rb_node,0,cached_total, { path: path, sub: focus });
                                    have whole.model == sized_plug(SizedContext::Left(a, ancestor, shade, value, sibling_model, up_model), sized_mirrored_context_flip_subtree(SizedMirroredContextFlipPhase::Done(x,y,z), old(node), SizedContext::Left(a, ancestor, shade, value, sibling_model, up_model), old(state.seed), old(state.parent_value), old(state.grand_value), old(state.other), old(state.uncle))) by {
                                        unfold(sized_mirrored_context_flip_subtree(SizedMirroredContextFlipPhase::Done(x,y,z), old(node), SizedContext::Left(a, ancestor, shade, value, sibling_model, up_model), old(state.seed), old(state.parent_value), old(state.grand_value), old(state.other), old(state.uncle))); solve();
                                    }
                                    have whole.model == sized_plug(old(state.outer), sized_mirrored_context_flip_subtree(sized_mirrored_context_flip_finish(old(state.phase)), old(node), old(state.outer), old(state.seed), old(state.parent_value), old(state.grand_value), old(state.other), old(state.uncle))) by {
                                        rewrite(sized_mirrored_context_flip_finish(old(state.phase)), SizedMirroredContextFlipPhase::Done(x,y,z));
                                        rewrite(old(state.outer), SizedContext::Left(a, ancestor, shade, value, sibling_model, up_model)); known();
                                    }
                                    let state = fold(sized_mirrored_context_flip_at(old(node),root), { phase: SizedMirroredContextFlipPhase::Done(x,y,z), model: whole.model, context: SizedContext::Top, outer: SizedContext::Left(a, ancestor, shade, value, sibling_model, up_model), seed: old(state.seed), parent_value: old(state.parent_value), grand_value: old(state.grand_value), other: old(state.other), uncle: old(state.uncle), whole: whole });
                                    have state.model == sized_plug(old(state.outer), sized_mirrored_context_flip_subtree(sized_mirrored_context_flip_finish(old(state.phase)), old(node), old(state.outer), old(state.seed), old(state.parent_value), old(state.grand_value), old(state.other), old(state.uncle))) by { known(); }
                                    step();
                                },
                            }
                        },
                        SizedMirroredContextFlipPhase::Before(x, y, z) => {
                            have parent == y by {
                                rewrite(parent, sized_mirrored_context_flip_parent(state.phase, state.outer));
                                rewrite(state.phase, SizedMirroredContextFlipPhase::Before(x, y, z));
                                unfold(sized_mirrored_context_flip_parent(SizedMirroredContextFlipPhase::Before(x, y, z),state.outer)); normalize();
                            }
                            have node == old(node) by {
                                rewrite(node, sized_mirrored_context_flip_focus(state.phase,old(node)));
                                rewrite(state.phase, SizedMirroredContextFlipPhase::Before(x, y, z));
                                unfold(sized_mirrored_context_flip_focus(SizedMirroredContextFlipPhase::Before(x, y, z),old(node))); normalize();
                            }
                            let { focus: focus, path: path, grand_value: cached_total } = unfold(state);
                            let { metadata: p_size, sibling: p_left, up: g_path } = unfold(path);
                            let { metadata: g_size, sibling: u_tree, up: top } = unfold(g_path);
                            let { metadata: u_size, right: u_right, left: u_left } = unfold(u_tree);
                            have x->rb_left != x by known();
                            have x->rb_right != x by known();
                            have y->rb_left != y by known();
                            have y->rb_right != y by known();
                            have z->rb_left != z by known();
                            have z->rb_right != z by known();
                            unfold(color_bit(Color::Red)); unfold(color_bit(Color::Black));
                            have y->__rb_parent_color == address(x) by {
                                rewrite(y->__rb_parent_color, address(x) + (y->__rb_parent_color & 1));
                                rewrite((y->__rb_parent_color & 1), color_bit(Color::Red));
                                rewrite(color_bit(Color::Red), 0); normalize();
                            }
                            have ((x->__rb_parent_color & ~3) as (struct rb_node *)) == sized_context_parent(at(iteration,state.outer),0) by { known(); }
                            mark c0; step();
                            have *((&x->__rb_parent_color) as (int32 **)) == at(c0, *((&x->__rb_parent_color) as (int32 **))) by solve();
                            have ((x->__rb_parent_color & ~3) as (struct rb_node *)) == sized_context_parent(at(iteration,state.outer),0) by { known(); }
                            mark c1; step();
                            have *((&x->__rb_parent_color) as (int32 **)) == at(c1, *((&x->__rb_parent_color) as (int32 **))) by solve();
                            have ((x->__rb_parent_color & ~3) as (struct rb_node *)) == sized_context_parent(at(iteration,state.outer),0) by { known(); }
                            mark c2; step();
                            have *((&x->__rb_parent_color) as (int32 **)) == at(c2, *((&x->__rb_parent_color) as (int32 **))) by solve();
                            have ((x->__rb_parent_color & ~3) as (struct rb_node *)) == sized_context_parent(at(iteration,state.outer),0) by { known(); }
                            mark c3; step();
                            have *((&x->__rb_parent_color) as (int32 **)) == at(c3, *((&x->__rb_parent_color) as (int32 **))) by solve();
                            have ((x->__rb_parent_color & ~3) as (struct rb_node *)) == sized_context_parent(at(iteration,state.outer),0) by { known(); }
                            mark c4; step();
                            have *((&x->__rb_parent_color) as (int32 **)) == at(c4, *((&x->__rb_parent_color) as (int32 **))) by solve();
                            have ((x->__rb_parent_color & ~3) as (struct rb_node *)) == sized_context_parent(at(iteration,state.outer),0) by { known(); }
                            mark c5; step();
                            have *((&x->__rb_parent_color) as (int32 **)) == at(c5, *((&x->__rb_parent_color) as (int32 **))) by solve();
                            have ((x->__rb_parent_color & ~3) as (struct rb_node *)) == sized_context_parent(at(iteration,state.outer),0) by { known(); }
                            mark c6; step();
                            have *((&x->__rb_parent_color) as (int32 **)) == at(c6, *((&x->__rb_parent_color) as (int32 **))) by solve();
                            have ((x->__rb_parent_color & ~3) as (struct rb_node *)) == sized_context_parent(at(iteration,state.outer),0) by { known(); }
                            mark c7; step();
                            have *((&x->__rb_parent_color) as (int32 **)) == at(c7, *((&x->__rb_parent_color) as (int32 **))) by solve();
                            have ((x->__rb_parent_color & ~3) as (struct rb_node *)) == sized_context_parent(at(iteration,state.outer),0) by { known(); }
                            mark c8; step();
                            have *((&x->__rb_parent_color) as (int32 **)) == at(c8, *((&x->__rb_parent_color) as (int32 **))) by solve();
                            have ((x->__rb_parent_color & ~3) as (struct rb_node *)) == sized_context_parent(at(iteration,state.outer),0) by { known(); }
                            have tmp == z by { known(); }
                            have gparent == x by { known(); }
                            have parent == y by { known(); }
                            let links = fold(sized_context_flip_links(root, x, y, z), {
                                top: root->rb_node, xl: x->rb_left, xr: x->rb_right,
                                yl: y->rb_left, yr: y->rb_right, zl: z->rb_left, zr: z->rb_right
                            });
                            let parent_word = fold(sized_context_flip_typed_parent_word(x), {
                                link: SizedContextFlipParent::At(((x->__rb_parent_color & ~3) as (struct rb_node*))),
                                word: x->__rb_parent_color
                            });
                            step();
                            step();
                            have aligned(gparent, 8) by known();
                            have (address(gparent) | 1) == address(gparent) + 1 by {
                                normalize() using { aligned(gparent, 8); };
                            }
                            let uncle_word = fold(sized_context_flip_black_word(tmp, gparent), {
                                word: tmp->__rb_parent_color
                            });
                            step();
                            let black_parent_word = fold(sized_context_flip_black_word(parent, gparent), {
                                word: parent->__rb_parent_color
                            });
                            step();
                            let { kept: parent_word } = step(insert::rb_parent, { word: parent_word });
                            step();
                            unfold(parent_word);
                            step();
                            unfold(uncle_word);
                            unfold(black_parent_word);
                            unfold(links);
                            have parent == sized_context_parent(at(iteration,state.outer),0) by known();
                            have x->__rb_parent_color == address(parent) by known();
                            have aligned(parent, 8) by known();
                            have (address(parent) & 7u64) == 0u64 by {
                                solve() using { aligned(parent, 8); };
                            }
                            have (7u64 & 1u64) == 1u64 by normalize();
                            apply(click::integer::uint64_mask_subset(address(parent), 7u64, 1u64));
                            have (x->__rb_parent_color & 1) == 0 by {
                                rewrite(x->__rb_parent_color, address(parent));
                                known();
                            }
                            have x->__rb_parent_color == address(sized_context_parent(at(iteration,state.outer),0)) + (x->__rb_parent_color & 1) by {
                                rewrite(x->__rb_parent_color, address(parent));
                                rewrite(sized_context_parent(at(iteration,state.outer),0), parent);
                                rewrite((address(parent) & 1u64), 0u64);
                                normalize();
                            }
                            have to_integer(sized_value(old(state.uncle))) == 1 + to_integer(sized_value(sized_left(old(state.uncle)))) + to_integer(sized_value(sized_right(old(state.uncle)))) by {
                                known();
                            }
                            let u_tree = fold(sized_at(z), { model: SizedTree::Node(z, x, Color::Black, sized_value(old(state.uncle)), sized_left(old(state.uncle)), sized_right(old(state.uncle))), metadata: u_size, right: u_right, left: u_left });
                            have sized_parent_is(focus.model,y) == 1 by {
                                rewrite(focus.model, old(state.seed));
                                rewrite(old(state.seed), SizedTree::Node(old(node), y, Color::Red, sized_value(old(state.seed)), sized_left(old(state.seed)), sized_right(old(state.seed))));
                                unfold(sized_parent_is(SizedTree::Node(old(node), y, Color::Red, sized_value(old(state.seed)), sized_left(old(state.seed)), sized_right(old(state.seed))),y)); normalize();
                            }
                            have sized_parent_is(old(state.other),y) == 1 by {
                                rewrite(old(state.other), at(iteration,state.other)); known();
                            }
                            unfold(sized_value(old(state.seed)));
                            have to_integer(old(state.parent_value)) == 1 + to_integer(sized_value(old(state.other))) + to_integer(sized_value(old(state.seed))) by {
                                known();
                            }
                            let p_tree = fold(sized_at(y), { model: SizedTree::Node(y, x, Color::Black, old(state.parent_value), old(state.other), old(state.seed)), metadata: p_size, right: focus, left: p_left });
                            have sized_parent_is(p_tree.model,x) == 1 by {
                                rewrite(p_tree.model, SizedTree::Node(y, x, Color::Black, old(state.parent_value), old(state.other), old(state.seed)));
                                unfold(sized_parent_is(SizedTree::Node(y, x, Color::Black, old(state.parent_value), old(state.other), old(state.seed)),x)); normalize();
                            }
                            have sized_parent_is(u_tree.model,x) == 1 by {
                                rewrite(u_tree.model, SizedTree::Node(z, x, Color::Black, sized_value(old(state.uncle)), sized_left(old(state.uncle)), sized_right(old(state.uncle))));
                                unfold(sized_parent_is(SizedTree::Node(z, x, Color::Black, sized_value(old(state.uncle)), sized_left(old(state.uncle)), sized_right(old(state.uncle))),x)); normalize();
                            }
                            unfold(sized_value(SizedTree::Node(y, x, Color::Black, old(state.parent_value), old(state.other), old(state.seed))));
                            unfold(sized_value(SizedTree::Node(z, x, Color::Black, sized_value(old(state.uncle)), sized_left(old(state.uncle)), sized_right(old(state.uncle)))));
                            unfold(sized_value(old(state.uncle)));
                            have to_integer(old(state.grand_value)) == 1 + to_integer(sized_value(SizedTree::Node(z, x, Color::Black, sized_value(old(state.uncle)), sized_left(old(state.uncle)), sized_right(old(state.uncle))))) + to_integer(sized_value(SizedTree::Node(y, x, Color::Black, old(state.parent_value), old(state.other), old(state.seed)))) by {
                                known();
                            }
                            let focus = fold(sized_at(x), { model: SizedTree::Node(x, sized_context_parent(at(iteration,state.outer),0), Color::Red, old(state.grand_value), SizedTree::Node(z, x, Color::Black, sized_value(old(state.uncle)), sized_left(old(state.uncle)), sized_right(old(state.uncle))), SizedTree::Node(y, x, Color::Black, old(state.parent_value), old(state.other), old(state.seed))), metadata: g_size, right: p_tree, left: u_tree });
                            let state = fold(sized_mirrored_context_flip_at(old(node),root), { phase: SizedMirroredContextFlipPhase::After(x, y, z), model: SizedTree::Node(x, sized_context_parent(at(iteration,state.outer),0), Color::Red, old(state.grand_value), SizedTree::Node(z, x, Color::Black, sized_value(old(state.uncle)), sized_left(old(state.uncle)), sized_right(old(state.uncle))), SizedTree::Node(y, x, Color::Black, old(state.parent_value), old(state.other), old(state.seed))), context: at(iteration,state.outer), outer: at(iteration,state.outer), seed: old(state.seed), parent_value: old(state.parent_value), grand_value: old(state.grand_value), other: old(state.other), uncle: old(state.uncle), focus: focus, path: top });
                            apply(sized_context_depth_nonnegative(state.outer));
                            have 0 <= sized_context_depth(state.context) by { rewrite(state.context, state.outer); known(); }
                            have sized_context_depth(state.context) < sized_context_depth(at(iteration,state.context)) by {
                                rewrite(state.context, at(iteration,state.outer));
                                rewrite(at(iteration,state.context), SizedContext::Right(y, x, Color::Red, old(state.parent_value), old(state.other), SizedContext::Right(x, sized_context_parent(at(iteration,state.outer),0), Color::Black, old(state.grand_value), old(state.uncle), at(iteration,state.outer))));
                                unfold(sized_context_depth(SizedContext::Right(y, x, Color::Red, old(state.parent_value), old(state.other), SizedContext::Right(x, sized_context_parent(at(iteration,state.outer),0), Color::Black, old(state.grand_value), old(state.uncle), at(iteration,state.outer)))));
                                unfold(sized_context_depth(SizedContext::Right(x, sized_context_parent(at(iteration,state.outer),0), Color::Black, old(state.grand_value), old(state.uncle), at(iteration,state.outer))));
                                solve() using {};
                            }
                            unfold(sized_mirrored_context_flip_focus(SizedMirroredContextFlipPhase::After(x, y, z),old(node)));
                            unfold(sized_mirrored_context_flip_parent(SizedMirroredContextFlipPhase::After(x, y, z),state.outer));
                            unfold(sized_mirrored_context_flip_finish(SizedMirroredContextFlipPhase::Before(x, y, z)));
                            have sized_mirrored_context_flip_finish(state.phase) == sized_mirrored_context_flip_finish(old(state.phase)) by {
                                rewrite(state.phase, SizedMirroredContextFlipPhase::After(x, y, z));
                                unfold(sized_mirrored_context_flip_finish(SizedMirroredContextFlipPhase::After(x, y, z)));
                                rewrite(SizedMirroredContextFlipPhase::Done(x, y, z), sized_mirrored_context_flip_finish(SizedMirroredContextFlipPhase::Before(x, y, z)));
                                rewrite(SizedMirroredContextFlipPhase::Before(x, y, z), at(iteration,state.phase)); known();
                            }
                            have sized_mirrored_context_flip_running(state.phase) == 1 by {
                                rewrite(state.phase, SizedMirroredContextFlipPhase::After(x, y, z));
                                unfold(sized_mirrored_context_flip_running(SizedMirroredContextFlipPhase::After(x, y, z))); normalize();
                            }
                            step();
                        },
                    }
                }
            }
            step_until(function.exit);
        },
    }
}

void insert::__rb_insert_augmented(struct rb_node* node, struct rb_root* root,
                  void (*augment_rotate)(struct rb_node*, struct rb_node*)) {
    owns state: sized_mirrored_context_flip_at(node, root);
    requires sized_mirrored_context_flip_pending(state.phase) == 1;
    ensures state.other == old(state.other);
    ensures state.uncle == old(state.uncle);
    ensures state.seed == old(state.seed);
    ensures state.parent_value == old(state.parent_value);
    ensures state.grand_value == old(state.grand_value);
    ensures state.phase == sized_mirrored_context_flip_finish(old(state.phase));
    ensures state.model == sized_plug(old(state.outer), sized_mirrored_context_flip_subtree(sized_mirrored_context_flip_finish(old(state.phase)), node, old(state.outer), old(state.seed), old(state.parent_value), old(state.grand_value), old(state.other), old(state.uncle)));
} by {
    step(insert::__rb_insert, { state: state });
}

void insert::rb_insert_augmented(struct rb_node* node, struct rb_root* root,
                  const struct rb_augment_callbacks* augment) {
    views augment->rotate;
    owns state: sized_mirrored_context_flip_at(node, root);
    requires sized_mirrored_context_flip_pending(state.phase) == 1;
    ensures state.other == old(state.other);
    ensures state.uncle == old(state.uncle);
    ensures state.seed == old(state.seed);
    ensures state.parent_value == old(state.parent_value);
    ensures state.grand_value == old(state.grand_value);
    ensures state.phase == sized_mirrored_context_flip_finish(old(state.phase));
    ensures state.model == sized_plug(old(state.outer), sized_mirrored_context_flip_subtree(sized_mirrored_context_flip_finish(old(state.phase)), node, old(state.outer), old(state.seed), old(state.parent_value), old(state.grand_value), old(state.other), old(state.uncle)));
} by {
    have separate(state, memory(augment->rotate)) by known();
    step(insert::__rb_insert_augmented, { state: state });
}
