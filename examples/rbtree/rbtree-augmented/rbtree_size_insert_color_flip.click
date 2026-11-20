// A color flip continues at the root; termination follows owned ancestor depth.
verifying "rb_insert_augmented.c";
verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_context_flip_frames.click";

spec enum SizedFlipPhase {
    Before(struct rb_node*, struct rb_node*, struct rb_node*),
    After(struct rb_node*, struct rb_node*, struct rb_node*),
    Done(struct rb_node*, struct rb_node*, struct rb_node*),
}
function sized_flip_pending(phase: SizedFlipPhase) -> int32 {
    match phase {
        SizedFlipPhase::Before(g, p, u) => 1,
        SizedFlipPhase::After(g, p, u) => 0,
        SizedFlipPhase::Done(g, p, u) => 0,
    }
}
function sized_flip_running(phase: SizedFlipPhase) -> int32 {
    match phase {
        SizedFlipPhase::Before(g, p, u) => 1,
        SizedFlipPhase::After(g, p, u) => 1,
        SizedFlipPhase::Done(g, p, u) => 0,
    }
}
function sized_flip_finish(phase: SizedFlipPhase) -> SizedFlipPhase {
    match phase {
        SizedFlipPhase::Before(g, p, u) => SizedFlipPhase::Done(g, p, u),
        SizedFlipPhase::After(g, p, u) => SizedFlipPhase::Done(g, p, u),
        SizedFlipPhase::Done(g, p, u) => SizedFlipPhase::Done(g, p, u),
    }
}
function sized_flip_focus(phase: SizedFlipPhase, n: struct rb_node*) -> struct rb_node* {
    match phase {
        SizedFlipPhase::Before(g, p, u) => n,
        SizedFlipPhase::After(g, p, u) => g,
        SizedFlipPhase::Done(g, p, u) => g,
    }
}
function sized_flip_parent(phase: SizedFlipPhase) -> struct rb_node* {
    match phase {
        SizedFlipPhase::Before(g, p, u) => p,
        SizedFlipPhase::After(g, p, u) => 0,
        SizedFlipPhase::Done(g, p, u) => 0,
    }
}
resource sized_flip_at(n: struct rb_node*, root: struct rb_root*) {
    field phase: SizedFlipPhase;
    field model: SizedTree;
    field context: SizedContext;
    match phase {
        SizedFlipPhase::Before(g, p, u) => {
            owns root->rb_node;
            owns focus: sized_at(n);
            owns path: sized_context_at(n, g, 0, 1);
            fact root->rb_node == g;
            fact focus.model == model;
            fact path.model == context;
            fact model == SizedTree::Node(n, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty);
            fact context == SizedContext::Left(p, g, Color::Red, 2, SizedTree::Empty, SizedContext::Left(g, 0, Color::Black, 4, SizedTree::Node(u, g, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedContext::Top));
        },
        SizedFlipPhase::After(g, p, u) => {
            owns root->rb_node;
            owns focus: sized_at(g);
            owns path: sized_context_at(g, g, 0, 4);
            fact root->rb_node == g;
            fact focus.model == model;
            fact path.model == context;
            fact context == SizedContext::Top;
            fact model == SizedTree::Node(g, 0, Color::Red, 4, SizedTree::Node(p, g, Color::Black, 2, SizedTree::Node(n, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty), SizedTree::Node(u, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty));
        },
        SizedFlipPhase::Done(g, p, u) => {
            owns root->rb_node;
            owns focus: sized_at(g);
            owns path: sized_context_at(g, g, 0, 4);
            fact root->rb_node == g;
            fact focus.model == model;
            fact path.model == context;
            fact context == SizedContext::Top;
            fact model == SizedTree::Node(g, 0, Color::Black, 4, SizedTree::Node(p, g, Color::Black, 2, SizedTree::Node(n, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty), SizedTree::Node(u, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty));
        },
    }
}
void __rb_insert(struct rb_node* node, struct rb_root* root,
                  void (*augment_rotate)(struct rb_node*, struct rb_node*)) {
    owns state: sized_flip_at(node, root);
    requires sized_flip_pending(state.phase) == 1;
    ensures state.phase == sized_flip_finish(old(state.phase));
} by {
    match state.phase {
        SizedFlipPhase::After(g, p, u) => {
            have sized_flip_pending(state.phase) != 1 by {
                rewrite(state.phase, SizedFlipPhase::After(g, p, u));
                unfold(sized_flip_pending(SizedFlipPhase::After(g, p, u))); normalize();
            }
            contradiction(sized_flip_pending(state.phase) == 1);
        },
        SizedFlipPhase::Done(g, p, u) => {
            have sized_flip_pending(state.phase) != 1 by {
                rewrite(state.phase, SizedFlipPhase::Done(g, p, u));
                unfold(sized_flip_pending(SizedFlipPhase::Done(g, p, u))); normalize();
            }
            contradiction(sized_flip_pending(state.phase) == 1);
        },
        SizedFlipPhase::Before(g, p, u) => {
            let { focus: focus, path: path } = unfold(state);
            let { metadata: n_size, left: n_left, right: n_right } = unfold(focus);
            unfold(color_bit(Color::Red));
            have node->__rb_parent_color == address(p) by {
                rewrite(node->__rb_parent_color, address(p) + (node->__rb_parent_color & 1));
                rewrite((node->__rb_parent_color & 1), color_bit(Color::Red));
                rewrite(color_bit(Color::Red), 0); normalize();
            }
            have ((load<uint64>(node) & ~3) as (struct rb_node *)) == p by known();
            step(); step(); step(); step();
            have ((load<uint64>(node) & ~3) as (struct rb_node *)) == p by known();
            let focus = fold(sized_at(node), { model: old(state.model), metadata: n_size, left: n_left, right: n_right });
            let state = fold(sized_flip_at(node,root), { phase: SizedFlipPhase::Before(g, p, u), model: old(state.model), context: old(state.context), focus: focus, path: path });
            step();
            loop {
                owns state: sized_flip_at(old(node),root);
                decreases sized_context_depth(state.context);
                invariant sized_flip_running(state.phase) == 1;
                invariant sized_flip_finish(state.phase) == sized_flip_finish(old(state.phase));
                invariant old(state.phase) == SizedFlipPhase::Before(g, p, u);
                invariant node == sized_flip_focus(state.phase, old(node));
                invariant parent == sized_flip_parent(state.phase);
                initialize by solve();
                maintain by {
                    mark iteration;
                    match state.phase {
                        SizedFlipPhase::Done(x, y, z) => {
                            have not (sized_flip_running(state.phase) == 1) by {
                                rewrite(state.phase, SizedFlipPhase::Done(x, y, z));
                                unfold(sized_flip_running(SizedFlipPhase::Done(x, y, z))); normalize();
                            }
                            contradiction(sized_flip_running(state.phase) == 1);
                        },
                        SizedFlipPhase::After(x, y, z) => {
                            have parent == 0 by {
                                rewrite(parent, sized_flip_parent(state.phase));
                                rewrite(state.phase, SizedFlipPhase::After(x, y, z));
                                unfold(sized_flip_parent(SizedFlipPhase::After(x, y, z))); normalize();
                            }
                            have node == x by {
                                rewrite(node, sized_flip_focus(state.phase,old(node)));
                                rewrite(state.phase, SizedFlipPhase::After(x, y, z));
                                unfold(sized_flip_focus(SizedFlipPhase::After(x, y, z),old(node))); normalize();
                            }
                            unfold(sized_flip_finish(SizedFlipPhase::After(x, y, z)));
                            have SizedFlipPhase::Done(x, y, z) == sized_flip_finish(old(state.phase)) by {
                                rewrite(SizedFlipPhase::Done(x, y, z), sized_flip_finish(SizedFlipPhase::After(x, y, z)));
                                rewrite(SizedFlipPhase::After(x, y, z), state.phase); known();
                            }
                            let { focus: focus, path: path } = unfold(state);
                            let { metadata: g_size, left: p_tree, right: u_tree } = unfold(focus);
                            let root_link = fold(sized_flip_root_link(root), { top: x });
                            step(); step();
                            unfold(root_link);
                            have (x->__rb_parent_color & 1) == color_bit(Color::Black) by { unfold(color_bit(Color::Black)); solve(); }
                            let focus = fold(sized_at(x), { model: SizedTree::Node(x, 0, Color::Black, 4, SizedTree::Node(y, x, Color::Black, 2, SizedTree::Node(old(node), y, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty), SizedTree::Node(z, x, Color::Black, 1, SizedTree::Empty, SizedTree::Empty)), metadata: g_size, left: p_tree, right: u_tree });
                            let state = fold(sized_flip_at(old(node),root), { phase: SizedFlipPhase::Done(x, y, z), model: SizedTree::Node(x, 0, Color::Black, 4, SizedTree::Node(y, x, Color::Black, 2, SizedTree::Node(old(node), y, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty), SizedTree::Node(z, x, Color::Black, 1, SizedTree::Empty, SizedTree::Empty)), context: SizedContext::Top, focus: focus, path: path });
                            step();
                        },
                        SizedFlipPhase::Before(x, y, z) => {
                            have parent == y by {
                                rewrite(parent, sized_flip_parent(state.phase));
                                rewrite(state.phase, SizedFlipPhase::Before(x, y, z));
                                unfold(sized_flip_parent(SizedFlipPhase::Before(x, y, z))); normalize();
                            }
                            have node == old(node) by {
                                rewrite(node, sized_flip_focus(state.phase,old(node)));
                                rewrite(state.phase, SizedFlipPhase::Before(x, y, z));
                                unfold(sized_flip_focus(SizedFlipPhase::Before(x, y, z),old(node))); normalize();
                            }
                            let { focus: focus, path: path } = unfold(state);
                            let { metadata: p_size, sibling: p_right, up: g_path } = unfold(path);
                            let { metadata: g_size, sibling: u_tree, up: top } = unfold(g_path);
                            let { metadata: u_size, left: u_left, right: u_right } = unfold(u_tree);
                            unfold(u_left); unfold(u_right); unfold(p_right);
                            unfold(color_bit(Color::Red)); unfold(color_bit(Color::Black));
                            have y->__rb_parent_color == address(x) by {
                                rewrite(y->__rb_parent_color, address(x) + (y->__rb_parent_color & 1));
                                rewrite((y->__rb_parent_color & 1), color_bit(Color::Red));
                                rewrite(color_bit(Color::Red), 0); normalize();
                            }
                            step(); step(); step(); step(); step(); step(); step();
                            step();
                            have tmp == z by { known(); }
                            have gparent == x by { known(); }
                            have aligned(gparent, 8) by known();
                            have (address(gparent) | 1) == address(gparent) + 1 by {
                                normalize() using { aligned(gparent, 8); };
                            }
                            have parent == y by { known(); }
                            step_until(call(rb_set_parent_color, 1).entry);
                            let links = fold(sized_context_flip_links(root, x, y, z), {
                                top: x, xl: y, xr: z,
                                yl: old(node), yr: 0 as (int32 *), zl: 0 as (int32 *), zr: 0 as (int32 *)
                            });
                            let parent_word = fold(sized_context_flip_parent_word(x), {
                                up: 0 as (int32 *), word: x->__rb_parent_color
                            });
                            step();
                            let uncle_word = fold(sized_context_flip_black_word(tmp, gparent), {
                                word: tmp->__rb_parent_color
                            });
                            step_until(call(rb_set_parent_color, 2).entry);
                            step();
                            let black_parent_word = fold(sized_context_flip_black_word(parent, gparent), {
                                word: parent->__rb_parent_color
                            });
                            unfold(parent_word);
                            have ((x->__rb_parent_color & ~3) as (struct rb_node *)) == 0 by known();
                            step_until(call(rb_set_parent_color, 3).entry);
                            have parent == 0 by known();
                            step();
                            unfold(uncle_word);
                            unfold(black_parent_word);
                            unfold(links);
                            let u_left = fold(sized_at(0), { model: SizedTree::Empty });
                            let u_right = fold(sized_at(0), { model: SizedTree::Empty });
                            let p_right = fold(sized_at(0), { model: SizedTree::Empty });
                            let u_tree = fold(sized_at(z), { model: SizedTree::Node(z, x, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), metadata: u_size, left: u_left, right: u_right });
                            have sized_parent_is(focus.model,y) == 1 by {
                                rewrite(focus.model, SizedTree::Node(old(node), y, Color::Red, 1, SizedTree::Empty, SizedTree::Empty));
                                unfold(sized_parent_is(SizedTree::Node(old(node), y, Color::Red, 1, SizedTree::Empty, SizedTree::Empty),y)); normalize();
                            }
                            unfold(sized_parent_is(SizedTree::Empty,y));
                            unfold(sized_value(SizedTree::Empty));
                            unfold(sized_value(SizedTree::Node(old(node), y, Color::Red, 1, SizedTree::Empty, SizedTree::Empty)));
                            have to_integer(2) == 1 + to_integer(sized_value(SizedTree::Node(old(node), y, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))) + to_integer(sized_value(SizedTree::Empty)) by {
                                rewrite(sized_value(SizedTree::Node(old(node), y, Color::Red, 1, SizedTree::Empty, SizedTree::Empty)), 1);
                                rewrite(sized_value(SizedTree::Empty), 0); normalize();
                            }
                            let p_tree = fold(sized_at(y), { model: SizedTree::Node(y, x, Color::Black, 2, SizedTree::Node(old(node), y, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty), metadata: p_size, left: focus, right: p_right });
                            have sized_parent_is(p_tree.model,x) == 1 by {
                                rewrite(p_tree.model, SizedTree::Node(y, x, Color::Black, 2, SizedTree::Node(old(node), y, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty));
                                unfold(sized_parent_is(SizedTree::Node(y, x, Color::Black, 2, SizedTree::Node(old(node), y, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty),x)); normalize();
                            }
                            have sized_parent_is(u_tree.model,x) == 1 by {
                                rewrite(u_tree.model, SizedTree::Node(z, x, Color::Black, 1, SizedTree::Empty, SizedTree::Empty));
                                unfold(sized_parent_is(SizedTree::Node(z, x, Color::Black, 1, SizedTree::Empty, SizedTree::Empty),x)); normalize();
                            }
                            unfold(sized_value(SizedTree::Node(y, x, Color::Black, 2, SizedTree::Node(old(node), y, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty)));
                            unfold(sized_value(SizedTree::Node(z, x, Color::Black, 1, SizedTree::Empty, SizedTree::Empty)));
                            have to_integer(4) == 1 + to_integer(sized_value(SizedTree::Node(y, x, Color::Black, 2, SizedTree::Node(old(node), y, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty))) + to_integer(sized_value(SizedTree::Node(z, x, Color::Black, 1, SizedTree::Empty, SizedTree::Empty))) by {
                                rewrite(sized_value(SizedTree::Node(y, x, Color::Black, 2, SizedTree::Node(old(node), y, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty)), 2);
                                rewrite(sized_value(SizedTree::Node(z, x, Color::Black, 1, SizedTree::Empty, SizedTree::Empty)), 1); normalize();
                            }
                            let focus = fold(sized_at(x), { model: SizedTree::Node(x, 0, Color::Red, 4, SizedTree::Node(y, x, Color::Black, 2, SizedTree::Node(old(node), y, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty), SizedTree::Node(z, x, Color::Black, 1, SizedTree::Empty, SizedTree::Empty)), metadata: g_size, left: p_tree, right: u_tree });
                            let state = fold(sized_flip_at(old(node),root), { phase: SizedFlipPhase::After(x, y, z), model: SizedTree::Node(x, 0, Color::Red, 4, SizedTree::Node(y, x, Color::Black, 2, SizedTree::Node(old(node), y, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Empty), SizedTree::Node(z, x, Color::Black, 1, SizedTree::Empty, SizedTree::Empty)), context: SizedContext::Top, focus: focus, path: top });
                            unfold(sized_context_depth(SizedContext::Top));
                            have 0 <= sized_context_depth(state.context) by solve();
                            have sized_context_depth(state.context) < sized_context_depth(at(iteration,state.context)) by {
                                rewrite(state.context, SizedContext::Top);
                                rewrite(at(iteration,state.context), SizedContext::Left(y, x, Color::Red, 2, SizedTree::Empty, SizedContext::Left(x, 0, Color::Black, 4, SizedTree::Node(z, x, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedContext::Top)));
                                unfold(sized_context_depth(SizedContext::Left(y, x, Color::Red, 2, SizedTree::Empty, SizedContext::Left(x, 0, Color::Black, 4, SizedTree::Node(z, x, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedContext::Top))));
                                unfold(sized_context_depth(SizedContext::Left(x, 0, Color::Black, 4, SizedTree::Node(z, x, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedContext::Top)));
                                unfold(sized_context_depth(SizedContext::Top)); normalize();
                            }
                            unfold(sized_flip_focus(SizedFlipPhase::After(x, y, z),old(node)));
                            unfold(sized_flip_parent(SizedFlipPhase::After(x, y, z)));
                            unfold(sized_flip_finish(SizedFlipPhase::Before(x, y, z)));
                            have sized_flip_finish(state.phase) == sized_flip_finish(old(state.phase)) by {
                                rewrite(state.phase, SizedFlipPhase::After(x, y, z));
                                unfold(sized_flip_finish(SizedFlipPhase::After(x, y, z)));
                                rewrite(SizedFlipPhase::Done(x, y, z), sized_flip_finish(SizedFlipPhase::Before(x, y, z)));
                                rewrite(SizedFlipPhase::Before(x, y, z), at(iteration,state.phase)); known();
                            }
                            have sized_flip_running(state.phase) == 1 by {
                                rewrite(state.phase, SizedFlipPhase::After(x, y, z));
                                unfold(sized_flip_running(SizedFlipPhase::After(x, y, z))); normalize();
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

void __rb_insert_augmented(struct rb_node* node, struct rb_root* root,
                  void (*augment_rotate)(struct rb_node*, struct rb_node*)) {
    owns state: sized_flip_at(node, root);
    requires sized_flip_pending(state.phase) == 1;
    ensures state.phase == sized_flip_finish(old(state.phase));
} by {
    step(__rb_insert, { state: state });
}

void rb_insert_augmented(struct rb_node* node, struct rb_root* root,
                  const struct rb_augment_callbacks* augment) {
    views augment->rotate;
    owns state: sized_flip_at(node, root);
    requires sized_flip_pending(state.phase) == 1;
    ensures state.phase == sized_flip_finish(old(state.phase));
} by {
    step(__rb_insert_augmented, { state: state });
}
