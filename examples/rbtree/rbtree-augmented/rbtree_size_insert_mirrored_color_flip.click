// A mirrored color flip continues at the root; termination follows owned ancestor depth.
verifying "rb_insert_augmented.c";
verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_context_resources.click";

spec enum SizedMirroredFlipPhase {
    Before(struct rb_node*, struct rb_node*, struct rb_node*),
    After(struct rb_node*, struct rb_node*, struct rb_node*),
    Done(struct rb_node*, struct rb_node*, struct rb_node*),
}
function sized_mirrored_flip_pending(phase: SizedMirroredFlipPhase) -> int32 {
    match phase {
        SizedMirroredFlipPhase::Before(g, p, u) => 1,
        SizedMirroredFlipPhase::After(g, p, u) => 0,
        SizedMirroredFlipPhase::Done(g, p, u) => 0,
    }
}
function sized_mirrored_flip_running(phase: SizedMirroredFlipPhase) -> int32 {
    match phase {
        SizedMirroredFlipPhase::Before(g, p, u) => 1,
        SizedMirroredFlipPhase::After(g, p, u) => 1,
        SizedMirroredFlipPhase::Done(g, p, u) => 0,
    }
}
function sized_mirrored_flip_finish(phase: SizedMirroredFlipPhase) -> SizedMirroredFlipPhase {
    match phase {
        SizedMirroredFlipPhase::Before(g, p, u) => SizedMirroredFlipPhase::Done(g, p, u),
        SizedMirroredFlipPhase::After(g, p, u) => SizedMirroredFlipPhase::Done(g, p, u),
        SizedMirroredFlipPhase::Done(g, p, u) => SizedMirroredFlipPhase::Done(g, p, u),
    }
}
function sized_mirrored_flip_focus(phase: SizedMirroredFlipPhase, n: struct rb_node*) -> struct rb_node* {
    match phase {
        SizedMirroredFlipPhase::Before(g, p, u) => n,
        SizedMirroredFlipPhase::After(g, p, u) => g,
        SizedMirroredFlipPhase::Done(g, p, u) => g,
    }
}
function sized_mirrored_flip_parent(phase: SizedMirroredFlipPhase) -> struct rb_node* {
    match phase {
        SizedMirroredFlipPhase::Before(g, p, u) => p,
        SizedMirroredFlipPhase::After(g, p, u) => 0,
        SizedMirroredFlipPhase::Done(g, p, u) => 0,
    }
}
resource sized_mirrored_flip_at(n: struct rb_node*, root: struct rb_root*) {
    field phase: SizedMirroredFlipPhase;
    field model: SizedTree;
    field context: SizedContext;
    match phase {
        SizedMirroredFlipPhase::Before(g, p, u) => {
            owns root->rb_node;
            owns focus: sized_at(n);
            owns path: sized_context_at(n, g, 0, 1);
            fact root->rb_node == g;
            fact focus.model == model;
            fact path.model == context;
            fact model == SizedTree::Node(n, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty);
            fact context == SizedContext::Right(p, g, Color::Red, 2, SizedTree::Empty, SizedContext::Right(g, 0, Color::Black, 4, SizedTree::Node(u, g, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedContext::Top));
        },
        SizedMirroredFlipPhase::After(g, p, u) => {
            owns root->rb_node;
            owns focus: sized_at(g);
            owns path: sized_context_at(g, g, 0, 4);
            fact root->rb_node == g;
            fact focus.model == model;
            fact path.model == context;
            fact context == SizedContext::Top;
            fact model == SizedTree::Node(g, 0, Color::Red, 4, SizedTree::Node(u, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, g, Color::Black, 2, SizedTree::Empty, SizedTree::Node(n, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty)));
        },
        SizedMirroredFlipPhase::Done(g, p, u) => {
            owns root->rb_node;
            owns focus: sized_at(g);
            owns path: sized_context_at(g, g, 0, 4);
            fact root->rb_node == g;
            fact focus.model == model;
            fact path.model == context;
            fact context == SizedContext::Top;
            fact model == SizedTree::Node(g, 0, Color::Black, 4, SizedTree::Node(u, g, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(p, g, Color::Black, 2, SizedTree::Empty, SizedTree::Node(n, p, Color::Red, 1, SizedTree::Empty, SizedTree::Empty)));
        },
    }
}
void __rb_insert(struct rb_node* node, struct rb_root* root,
                  void (*augment_rotate)(struct rb_node*, struct rb_node*)) {
    owns state: sized_mirrored_flip_at(node, root);
    requires sized_mirrored_flip_pending(state.phase) == 1;
    ensures state.phase == sized_mirrored_flip_finish(old(state.phase));
} by {
    match state.phase {
        SizedMirroredFlipPhase::After(g, p, u) => {
            have sized_mirrored_flip_pending(state.phase) != 1 by {
                rewrite(state.phase == SizedMirroredFlipPhase::After(g, p, u));
                unfold(sized_mirrored_flip_pending(SizedMirroredFlipPhase::After(g, p, u))); normalize();
            }
            contradiction(sized_mirrored_flip_pending(state.phase) == 1);
        },
        SizedMirroredFlipPhase::Done(g, p, u) => {
            have sized_mirrored_flip_pending(state.phase) != 1 by {
                rewrite(state.phase == SizedMirroredFlipPhase::Done(g, p, u));
                unfold(sized_mirrored_flip_pending(SizedMirroredFlipPhase::Done(g, p, u))); normalize();
            }
            contradiction(sized_mirrored_flip_pending(state.phase) == 1);
        },
        SizedMirroredFlipPhase::Before(g, p, u) => {
            let { focus: focus, path: path } = unfold(state);
            let { metadata: n_size, right: n_left, left: n_right } = unfold(focus);
            unfold(color_bit(Color::Red));
            have node->__rb_parent_color == address(p) by {
                rewrite(node->__rb_parent_color == address(p) + (node->__rb_parent_color & 1));
                rewrite((node->__rb_parent_color & 1) == color_bit(Color::Red));
                rewrite(color_bit(Color::Red) == 0); normalize();
            }
            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == p by { assumption(); }
            mark m0; step();
            have *((&node->__rb_parent_color) as (int32 **)) == at(m0, *((&node->__rb_parent_color) as (int32 **))) by solve();
            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == p by { assumption(); }
            mark m1; step();
            have *((&node->__rb_parent_color) as (int32 **)) == at(m1, *((&node->__rb_parent_color) as (int32 **))) by solve();
            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == p by { assumption(); }
            mark m2; step();
            have *((&node->__rb_parent_color) as (int32 **)) == at(m2, *((&node->__rb_parent_color) as (int32 **))) by solve();
            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == p by { assumption(); }
            mark m3; step();
            have *((&node->__rb_parent_color) as (int32 **)) == at(m3, *((&node->__rb_parent_color) as (int32 **))) by solve();
            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == p by { assumption(); }
            let focus = fold(sized_at(node), { model: old(state.model) }, { metadata: n_size, right: n_left, left: n_right });
            let state = fold(sized_mirrored_flip_at(node,root), { phase: SizedMirroredFlipPhase::Before(g, p, u), model: old(state.model), context: old(state.context) }, { focus: focus, path: path });
            loop {
                owns state: sized_mirrored_flip_at(old(node),root);
                decreases sized_context_depth(state.context);
                invariant sized_mirrored_flip_running(state.phase) == 1;
                invariant sized_mirrored_flip_finish(state.phase) == sized_mirrored_flip_finish(old(state.phase));
                invariant old(state.phase) == SizedMirroredFlipPhase::Before(g, p, u);
                invariant node == sized_mirrored_flip_focus(state.phase, old(node));
                invariant parent == sized_mirrored_flip_parent(state.phase);
                initialize by solve();
                preserve by {
                    mark iteration;
                    match state.phase {
                        SizedMirroredFlipPhase::Done(x, y, z) => {
                            have not (sized_mirrored_flip_running(state.phase) == 1) by {
                                rewrite(state.phase == SizedMirroredFlipPhase::Done(x, y, z));
                                unfold(sized_mirrored_flip_running(SizedMirroredFlipPhase::Done(x, y, z))); normalize();
                            }
                            contradiction(sized_mirrored_flip_running(state.phase) == 1);
                        },
                        SizedMirroredFlipPhase::After(x, y, z) => {
                            have parent == 0 by {
                                rewrite(parent == sized_mirrored_flip_parent(state.phase));
                                rewrite(state.phase == SizedMirroredFlipPhase::After(x, y, z));
                                unfold(sized_mirrored_flip_parent(SizedMirroredFlipPhase::After(x, y, z))); normalize();
                            }
                            have node == x by {
                                rewrite(node == sized_mirrored_flip_focus(state.phase,old(node)));
                                rewrite(state.phase == SizedMirroredFlipPhase::After(x, y, z));
                                unfold(sized_mirrored_flip_focus(SizedMirroredFlipPhase::After(x, y, z),old(node))); normalize();
                            }
                            unfold(sized_mirrored_flip_finish(SizedMirroredFlipPhase::After(x, y, z)));
                            have SizedMirroredFlipPhase::Done(x, y, z) == sized_mirrored_flip_finish(old(state.phase)) by {
                                rewrite(SizedMirroredFlipPhase::Done(x, y, z) == sized_mirrored_flip_finish(SizedMirroredFlipPhase::After(x, y, z)));
                                rewrite(SizedMirroredFlipPhase::After(x, y, z) == state.phase); assumption();
                            }
                            let { focus: focus, path: path } = unfold(state);
                            let { metadata: g_size, right: p_tree, left: u_tree } = unfold(focus);
                            have separate(memory(root->rb_node), memory(node->__rb_parent_color));
                            mark before_root_recolor;
                            step(); step();
                            transport(at(before_root_recolor, root->rb_node == x), root->rb_node == x) using {
                                at(before_root_recolor, root->rb_node == x);
                                separate(memory(root->rb_node), memory(node->__rb_parent_color));
                            };
                            have (x->__rb_parent_color & 1) == color_bit(Color::Black) by { unfold(color_bit(Color::Black)); solve(); }
                            let focus = fold(sized_at(x), { model: SizedTree::Node(x, 0, Color::Black, 4, SizedTree::Node(z, x, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(y, x, Color::Black, 2, SizedTree::Empty, SizedTree::Node(old(node), y, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))) }, { metadata: g_size, right: p_tree, left: u_tree });
                            let state = fold(sized_mirrored_flip_at(old(node),root), { phase: SizedMirroredFlipPhase::Done(x, y, z), model: SizedTree::Node(x, 0, Color::Black, 4, SizedTree::Node(z, x, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(y, x, Color::Black, 2, SizedTree::Empty, SizedTree::Node(old(node), y, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))), context: SizedContext::Top }, { focus: focus, path: path });
                            step();
                        },
                        SizedMirroredFlipPhase::Before(x, y, z) => {
                            have parent == y by {
                                rewrite(parent == sized_mirrored_flip_parent(state.phase));
                                rewrite(state.phase == SizedMirroredFlipPhase::Before(x, y, z));
                                unfold(sized_mirrored_flip_parent(SizedMirroredFlipPhase::Before(x, y, z))); normalize();
                            }
                            have node == old(node) by {
                                rewrite(node == sized_mirrored_flip_focus(state.phase,old(node)));
                                rewrite(state.phase == SizedMirroredFlipPhase::Before(x, y, z));
                                unfold(sized_mirrored_flip_focus(SizedMirroredFlipPhase::Before(x, y, z),old(node))); normalize();
                            }
                            let { focus: focus, path: path } = unfold(state);
                            let { metadata: p_size, sibling: p_right, up: g_path } = unfold(path);
                            let { metadata: g_size, sibling: u_tree, up: top } = unfold(g_path);
                            let { metadata: u_size, right: u_left, left: u_right } = unfold(u_tree);
                            have separate(memory(x->__rb_parent_color), memory(y->__rb_parent_color));
                            have separate(memory(x->__rb_parent_color), memory(z->__rb_parent_color));
                            have separate(memory(z->__rb_parent_color), memory(y->__rb_parent_color));
                            have separate(memory(root->rb_node), memory(x->__rb_parent_color));
                            have separate(memory(root->rb_node), memory(y->__rb_parent_color));
                            have separate(memory(root->rb_node), memory(z->__rb_parent_color));
                            have separate(memory(z->rb_left), memory(x->__rb_parent_color));
                            have separate(memory(z->rb_left), memory(y->__rb_parent_color));
                            have separate(memory(z->rb_left), memory(z->__rb_parent_color));
                            have separate(memory(z->rb_right), memory(x->__rb_parent_color));
                            have separate(memory(z->rb_right), memory(y->__rb_parent_color));
                            have separate(memory(z->rb_right), memory(z->__rb_parent_color));
                            have separate(memory(y->rb_left), memory(x->__rb_parent_color));
                            have separate(memory(y->rb_left), memory(y->__rb_parent_color));
                            have separate(memory(y->rb_left), memory(z->__rb_parent_color));
                            have separate(memory(y->rb_right), memory(x->__rb_parent_color));
                            have separate(memory(y->rb_right), memory(y->__rb_parent_color));
                            have separate(memory(y->rb_right), memory(z->__rb_parent_color));
                            have separate(memory(x->rb_left), memory(x->__rb_parent_color));
                            have separate(memory(x->rb_left), memory(y->__rb_parent_color));
                            have separate(memory(x->rb_left), memory(z->__rb_parent_color));
                            have separate(memory(x->rb_right), memory(x->__rb_parent_color));
                            have separate(memory(x->rb_right), memory(y->__rb_parent_color));
                            have separate(memory(x->rb_right), memory(z->__rb_parent_color));
                            unfold(color_bit(Color::Red)); unfold(color_bit(Color::Black));
                            have y->__rb_parent_color == address(x) by {
                                rewrite(y->__rb_parent_color == address(x) + (y->__rb_parent_color & 1));
                                rewrite((y->__rb_parent_color & 1) == color_bit(Color::Red));
                                rewrite(color_bit(Color::Red) == 0); normalize();
                            }
                            step(); step(); step(); step(); step(); step(); step(); step();
                            step();
                            have tmp == z by { assumption(); }
                            have gparent == x by { assumption(); }
                            have parent == y by { assumption(); }
                            mark before_recolor;
                            have root->rb_node == x by { assumption(); }
                            have ((x->__rb_parent_color & ~3) as (struct rb_node *)) == 0 by { assumption(); }
                            step();
                            have separate(memory(tmp->__rb_parent_color), memory(gparent->__rb_parent_color)) by solve();
                            have separate(statement(1).statement(4).statement(10).statement(0).footprint, memory(x->__rb_parent_color)) by {
                                normalize() using { separate(memory(tmp->__rb_parent_color), memory(gparent->__rb_parent_color)); };
                            }
                            have x->__rb_parent_color == at(before_recolor, x->__rb_parent_color) by {
                                transport_certificate {
                                    premise 0: separate(statement(1).statement(4).statement(10).statement(0).footprint, memory(x->__rb_parent_color)) => separate(statement(1).statement(4).statement(10).statement(0).footprint, memory(x->__rb_parent_color));
                                    preserve 0 => x->__rb_parent_color == at(before_recolor, x->__rb_parent_color);
                                    conclusion 1;
                                }
                            }
                            have ((x->__rb_parent_color & ~3) as (struct rb_node *)) == 0 by { rewrite(x->__rb_parent_color == at(before_recolor, x->__rb_parent_color)); assumption(); }
                            have separate(memory(root->rb_node), memory(tmp->__rb_parent_color)) by { rewrite(tmp == z); assumption(); }
                            have separate(statement(1).statement(4).statement(10).statement(0).footprint, memory(root->rb_node)) by {
                                normalize() using { separate(memory(root->rb_node), memory(tmp->__rb_parent_color)); };
                            }
                            have root->rb_node == at(before_recolor, root->rb_node) by {
                                transport_certificate {
                                    premise 0: separate(statement(1).statement(4).statement(10).statement(0).footprint, memory(root->rb_node)) => separate(statement(1).statement(4).statement(10).statement(0).footprint, memory(root->rb_node));
                                    preserve 0 => root->rb_node == at(before_recolor, root->rb_node);
                                    conclusion 1;
                                }
                            }
                            have root->rb_node == x by { rewrite(root->rb_node == at(before_recolor, root->rb_node)); assumption(); }
                            have separate(memory(z->rb_left), memory(tmp->__rb_parent_color)) by { rewrite(tmp == z); assumption(); }
                            have separate(statement(1).statement(4).statement(10).statement(0).footprint, memory(z->rb_left)) by {
                                normalize() using { separate(memory(z->rb_left), memory(tmp->__rb_parent_color)); };
                            }
                            have z->rb_left == at(before_recolor, z->rb_left) by {
                                transport_certificate {
                                    premise 0: separate(statement(1).statement(4).statement(10).statement(0).footprint, memory(z->rb_left)) => separate(statement(1).statement(4).statement(10).statement(0).footprint, memory(z->rb_left));
                                    preserve 0 => z->rb_left == at(before_recolor, z->rb_left);
                                    conclusion 1;
                                }
                            }
                            have separate(memory(z->rb_right), memory(tmp->__rb_parent_color)) by { rewrite(tmp == z); assumption(); }
                            have separate(statement(1).statement(4).statement(10).statement(0).footprint, memory(z->rb_right)) by {
                                normalize() using { separate(memory(z->rb_right), memory(tmp->__rb_parent_color)); };
                            }
                            have z->rb_right == at(before_recolor, z->rb_right) by {
                                transport_certificate {
                                    premise 0: separate(statement(1).statement(4).statement(10).statement(0).footprint, memory(z->rb_right)) => separate(statement(1).statement(4).statement(10).statement(0).footprint, memory(z->rb_right));
                                    preserve 0 => z->rb_right == at(before_recolor, z->rb_right);
                                    conclusion 1;
                                }
                            }
                            have separate(memory(y->rb_left), memory(tmp->__rb_parent_color)) by { rewrite(tmp == z); assumption(); }
                            have separate(statement(1).statement(4).statement(10).statement(0).footprint, memory(y->rb_left)) by {
                                normalize() using { separate(memory(y->rb_left), memory(tmp->__rb_parent_color)); };
                            }
                            have y->rb_left == at(before_recolor, y->rb_left) by {
                                transport_certificate {
                                    premise 0: separate(statement(1).statement(4).statement(10).statement(0).footprint, memory(y->rb_left)) => separate(statement(1).statement(4).statement(10).statement(0).footprint, memory(y->rb_left));
                                    preserve 0 => y->rb_left == at(before_recolor, y->rb_left);
                                    conclusion 1;
                                }
                            }
                            have separate(memory(y->rb_right), memory(tmp->__rb_parent_color)) by { rewrite(tmp == z); assumption(); }
                            have separate(statement(1).statement(4).statement(10).statement(0).footprint, memory(y->rb_right)) by {
                                normalize() using { separate(memory(y->rb_right), memory(tmp->__rb_parent_color)); };
                            }
                            have y->rb_right == at(before_recolor, y->rb_right) by {
                                transport_certificate {
                                    premise 0: separate(statement(1).statement(4).statement(10).statement(0).footprint, memory(y->rb_right)) => separate(statement(1).statement(4).statement(10).statement(0).footprint, memory(y->rb_right));
                                    preserve 0 => y->rb_right == at(before_recolor, y->rb_right);
                                    conclusion 1;
                                }
                            }
                            have separate(memory(x->rb_left), memory(tmp->__rb_parent_color)) by { rewrite(tmp == z); assumption(); }
                            have separate(statement(1).statement(4).statement(10).statement(0).footprint, memory(x->rb_left)) by {
                                normalize() using { separate(memory(x->rb_left), memory(tmp->__rb_parent_color)); };
                            }
                            have x->rb_left == at(before_recolor, x->rb_left) by {
                                transport_certificate {
                                    premise 0: separate(statement(1).statement(4).statement(10).statement(0).footprint, memory(x->rb_left)) => separate(statement(1).statement(4).statement(10).statement(0).footprint, memory(x->rb_left));
                                    preserve 0 => x->rb_left == at(before_recolor, x->rb_left);
                                    conclusion 1;
                                }
                            }
                            have separate(memory(x->rb_right), memory(tmp->__rb_parent_color)) by { rewrite(tmp == z); assumption(); }
                            have separate(statement(1).statement(4).statement(10).statement(0).footprint, memory(x->rb_right)) by {
                                normalize() using { separate(memory(x->rb_right), memory(tmp->__rb_parent_color)); };
                            }
                            have x->rb_right == at(before_recolor, x->rb_right) by {
                                transport_certificate {
                                    premise 0: separate(statement(1).statement(4).statement(10).statement(0).footprint, memory(x->rb_right)) => separate(statement(1).statement(4).statement(10).statement(0).footprint, memory(x->rb_right));
                                    preserve 0 => x->rb_right == at(before_recolor, x->rb_right);
                                    conclusion 1;
                                }
                            }
                            have z->__rb_parent_color == address(x) + 1 by {
                                arithmetic_certificate rules {
                                    premise 0: aligned(x, 8) => aligned(x, 8);
                                    pointer_word_from_alignment alignments [0] => (address(x) | 1) == address(x) + 1;
                                    conclusion 0;
                                }
                            }
                            have (z->__rb_parent_color & ~3) == address(x) by {
                                arithmetic_certificate rules {
                                    premise 0: aligned(x, 8) => aligned(x, 8);
                                    pointer_word_from_alignment alignments [0] => (address(x) & ~3) == address(x);
                                    conclusion 0;
                                }
                            }
                            have ((z->__rb_parent_color & ~3) as (struct rb_node *)) == x by { assumption(); }
                            have (z->__rb_parent_color & 1) == 1 by { normalize(); }
                            have z->__rb_parent_color == address(x) + (z->__rb_parent_color & 1) by { rewrite((z->__rb_parent_color & 1) == 1); assumption(); }
                            mark recolor_mid;
                            step();
                            have separate(memory(parent->__rb_parent_color), memory(gparent->__rb_parent_color)) by solve();
                            have separate(statement(1).statement(4).statement(10).statement(1).footprint, memory(x->__rb_parent_color)) by {
                                normalize() using { separate(memory(x->__rb_parent_color), memory(y->__rb_parent_color)); };
                            }
                            have x->__rb_parent_color == at(recolor_mid, x->__rb_parent_color) by {
                                transport_certificate {
                                    premise 0: separate(statement(1).statement(4).statement(10).statement(1).footprint, memory(x->__rb_parent_color)) => separate(statement(1).statement(4).statement(10).statement(1).footprint, memory(x->__rb_parent_color));
                                    preserve 0 => x->__rb_parent_color == at(recolor_mid, x->__rb_parent_color);
                                    conclusion 1;
                                }
                            }
                            have ((x->__rb_parent_color & ~3) as (struct rb_node *)) == 0 by { rewrite(x->__rb_parent_color == at(recolor_mid, x->__rb_parent_color)); assumption(); }
                            have separate(statement(1).statement(4).statement(10).statement(1).footprint, memory(root->rb_node)) by {
                                normalize() using { separate(memory(root->rb_node), memory(y->__rb_parent_color)); };
                            }
                            have root->rb_node == at(recolor_mid, root->rb_node) by {
                                transport_certificate {
                                    premise 0: separate(statement(1).statement(4).statement(10).statement(1).footprint, memory(root->rb_node)) => separate(statement(1).statement(4).statement(10).statement(1).footprint, memory(root->rb_node));
                                    preserve 0 => root->rb_node == at(recolor_mid, root->rb_node);
                                    conclusion 1;
                                }
                            }
                            have root->rb_node == x by { rewrite(root->rb_node == at(recolor_mid, root->rb_node)); assumption(); }
                            have separate(statement(1).statement(4).statement(10).statement(1).footprint, memory(z->rb_left)) by {
                                normalize() using { separate(memory(z->rb_left), memory(y->__rb_parent_color)); };
                            }
                            have z->rb_left == at(recolor_mid, z->rb_left) by {
                                transport_certificate {
                                    premise 0: separate(statement(1).statement(4).statement(10).statement(1).footprint, memory(z->rb_left)) => separate(statement(1).statement(4).statement(10).statement(1).footprint, memory(z->rb_left));
                                    preserve 0 => z->rb_left == at(recolor_mid, z->rb_left);
                                    conclusion 1;
                                }
                            }
                            have z->rb_left == at(before_recolor, z->rb_left) by { rewrite(z->rb_left == at(recolor_mid, z->rb_left)); assumption(); }
                            have separate(statement(1).statement(4).statement(10).statement(1).footprint, memory(z->rb_right)) by {
                                normalize() using { separate(memory(z->rb_right), memory(y->__rb_parent_color)); };
                            }
                            have z->rb_right == at(recolor_mid, z->rb_right) by {
                                transport_certificate {
                                    premise 0: separate(statement(1).statement(4).statement(10).statement(1).footprint, memory(z->rb_right)) => separate(statement(1).statement(4).statement(10).statement(1).footprint, memory(z->rb_right));
                                    preserve 0 => z->rb_right == at(recolor_mid, z->rb_right);
                                    conclusion 1;
                                }
                            }
                            have z->rb_right == at(before_recolor, z->rb_right) by { rewrite(z->rb_right == at(recolor_mid, z->rb_right)); assumption(); }
                            have separate(statement(1).statement(4).statement(10).statement(1).footprint, memory(y->rb_left)) by {
                                normalize() using { separate(memory(y->rb_left), memory(y->__rb_parent_color)); };
                            }
                            have y->rb_left == at(recolor_mid, y->rb_left) by {
                                transport_certificate {
                                    premise 0: separate(statement(1).statement(4).statement(10).statement(1).footprint, memory(y->rb_left)) => separate(statement(1).statement(4).statement(10).statement(1).footprint, memory(y->rb_left));
                                    preserve 0 => y->rb_left == at(recolor_mid, y->rb_left);
                                    conclusion 1;
                                }
                            }
                            have y->rb_left == at(before_recolor, y->rb_left) by { rewrite(y->rb_left == at(recolor_mid, y->rb_left)); assumption(); }
                            have separate(statement(1).statement(4).statement(10).statement(1).footprint, memory(y->rb_right)) by {
                                normalize() using { separate(memory(y->rb_right), memory(y->__rb_parent_color)); };
                            }
                            have y->rb_right == at(recolor_mid, y->rb_right) by {
                                transport_certificate {
                                    premise 0: separate(statement(1).statement(4).statement(10).statement(1).footprint, memory(y->rb_right)) => separate(statement(1).statement(4).statement(10).statement(1).footprint, memory(y->rb_right));
                                    preserve 0 => y->rb_right == at(recolor_mid, y->rb_right);
                                    conclusion 1;
                                }
                            }
                            have y->rb_right == at(before_recolor, y->rb_right) by { rewrite(y->rb_right == at(recolor_mid, y->rb_right)); assumption(); }
                            have separate(statement(1).statement(4).statement(10).statement(1).footprint, memory(x->rb_left)) by {
                                normalize() using { separate(memory(x->rb_left), memory(y->__rb_parent_color)); };
                            }
                            have x->rb_left == at(recolor_mid, x->rb_left) by {
                                transport_certificate {
                                    premise 0: separate(statement(1).statement(4).statement(10).statement(1).footprint, memory(x->rb_left)) => separate(statement(1).statement(4).statement(10).statement(1).footprint, memory(x->rb_left));
                                    preserve 0 => x->rb_left == at(recolor_mid, x->rb_left);
                                    conclusion 1;
                                }
                            }
                            have x->rb_left == at(before_recolor, x->rb_left) by { rewrite(x->rb_left == at(recolor_mid, x->rb_left)); assumption(); }
                            have separate(statement(1).statement(4).statement(10).statement(1).footprint, memory(x->rb_right)) by {
                                normalize() using { separate(memory(x->rb_right), memory(y->__rb_parent_color)); };
                            }
                            have x->rb_right == at(recolor_mid, x->rb_right) by {
                                transport_certificate {
                                    premise 0: separate(statement(1).statement(4).statement(10).statement(1).footprint, memory(x->rb_right)) => separate(statement(1).statement(4).statement(10).statement(1).footprint, memory(x->rb_right));
                                    preserve 0 => x->rb_right == at(recolor_mid, x->rb_right);
                                    conclusion 1;
                                }
                            }
                            have x->rb_right == at(before_recolor, x->rb_right) by { rewrite(x->rb_right == at(recolor_mid, x->rb_right)); assumption(); }
                            have separate(statement(1).statement(4).statement(10).statement(1).footprint, memory(z->__rb_parent_color)) by {
                                normalize() using { separate(memory(z->__rb_parent_color), memory(y->__rb_parent_color)); };
                            }
                            have z->__rb_parent_color == at(recolor_mid, z->__rb_parent_color) by {
                                transport_certificate {
                                    premise 0: separate(statement(1).statement(4).statement(10).statement(1).footprint, memory(z->__rb_parent_color)) => separate(statement(1).statement(4).statement(10).statement(1).footprint, memory(z->__rb_parent_color));
                                    preserve 0 => z->__rb_parent_color == at(recolor_mid, z->__rb_parent_color);
                                    conclusion 1;
                                }
                            }
                            have z->__rb_parent_color == address(x) + (z->__rb_parent_color & 1) by { rewrite(z->__rb_parent_color == at(recolor_mid, z->__rb_parent_color)); assumption(); }
                            have *((&z->__rb_parent_color) as (int32 **)) == at(recolor_mid, *((&z->__rb_parent_color) as (int32 **))) by {
                                transport_certificate {
                                    premise 0: separate(statement(1).statement(4).statement(10).statement(1).footprint, memory(z->__rb_parent_color)) => separate(statement(1).statement(4).statement(10).statement(1).footprint, memory(z->__rb_parent_color));
                                    preserve 0 => *((&z->__rb_parent_color) as (int32 **)) == at(recolor_mid, *((&z->__rb_parent_color) as (int32 **)));
                                    conclusion 1;
                                }
                            }
                            have (z->__rb_parent_color & ~3) == address(x) by {
                                rewrite(z->__rb_parent_color == at(recolor_mid, z->__rb_parent_color));
                                arithmetic_certificate rules {
                                    premise 0: aligned(x, 8) => aligned(x, 8);
                                    pointer_word_from_alignment alignments [0] => (address(x) & ~3) == address(x);
                                    conclusion 0;
                                }
                            }
                            transport(at(before_recolor, ((x->__rb_parent_color & ~3) as (struct rb_node *)) == 0),
                                      ((x->__rb_parent_color & ~3) as (struct rb_node *)) == 0) using {
                                at(before_recolor, ((x->__rb_parent_color & ~3) as (struct rb_node *)) == 0);
                                tmp == z;
                                parent == y;
                                separate(memory(x->__rb_parent_color), memory(y->__rb_parent_color));
                                separate(memory(x->__rb_parent_color), memory(z->__rb_parent_color));
                            };
                            mark recolor_node;
                            step();
                            have z->__rb_parent_color == at(recolor_node, z->__rb_parent_color) by solve();
                            have z->__rb_parent_color == address(x) + (z->__rb_parent_color & 1) by { rewrite(z->__rb_parent_color == at(recolor_node, z->__rb_parent_color)); assumption(); }
                            have root->rb_node == at(recolor_node, root->rb_node) by solve();
                            have root->rb_node == x by { rewrite(root->rb_node == at(recolor_node, root->rb_node)); assumption(); }
                            have z->rb_left == at(recolor_node, z->rb_left) by solve();
                            have z->rb_left == at(before_recolor, z->rb_left) by { rewrite(z->rb_left == at(recolor_node, z->rb_left)); assumption(); }
                            have z->rb_right == at(recolor_node, z->rb_right) by solve();
                            have z->rb_right == at(before_recolor, z->rb_right) by { rewrite(z->rb_right == at(recolor_node, z->rb_right)); assumption(); }
                            have y->rb_left == at(recolor_node, y->rb_left) by solve();
                            have y->rb_left == at(before_recolor, y->rb_left) by { rewrite(y->rb_left == at(recolor_node, y->rb_left)); assumption(); }
                            have y->rb_right == at(recolor_node, y->rb_right) by solve();
                            have y->rb_right == at(before_recolor, y->rb_right) by { rewrite(y->rb_right == at(recolor_node, y->rb_right)); assumption(); }
                            have x->rb_left == at(recolor_node, x->rb_left) by solve();
                            have x->rb_left == at(before_recolor, x->rb_left) by { rewrite(x->rb_left == at(recolor_node, x->rb_left)); assumption(); }
                            have x->rb_right == at(recolor_node, x->rb_right) by solve();
                            have x->rb_right == at(before_recolor, x->rb_right) by { rewrite(x->rb_right == at(recolor_node, x->rb_right)); assumption(); }
                            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == 0 by {
                                assumption();
                            }
                            mark recolor_parent;
                            step();
                            have z->__rb_parent_color == at(recolor_parent, z->__rb_parent_color) by solve();
                            have z->__rb_parent_color == address(x) + (z->__rb_parent_color & 1) by { rewrite(z->__rb_parent_color == at(recolor_parent, z->__rb_parent_color)); assumption(); }
                            have root->rb_node == at(recolor_parent, root->rb_node) by solve();
                            have root->rb_node == x by { rewrite(root->rb_node == at(recolor_parent, root->rb_node)); assumption(); }
                            have z->rb_left == at(recolor_parent, z->rb_left) by solve();
                            have z->rb_left == at(before_recolor, z->rb_left) by { rewrite(z->rb_left == at(recolor_parent, z->rb_left)); assumption(); }
                            have z->rb_right == at(recolor_parent, z->rb_right) by solve();
                            have z->rb_right == at(before_recolor, z->rb_right) by { rewrite(z->rb_right == at(recolor_parent, z->rb_right)); assumption(); }
                            have y->rb_left == at(recolor_parent, y->rb_left) by solve();
                            have y->rb_left == at(before_recolor, y->rb_left) by { rewrite(y->rb_left == at(recolor_parent, y->rb_left)); assumption(); }
                            have y->rb_right == at(recolor_parent, y->rb_right) by solve();
                            have y->rb_right == at(before_recolor, y->rb_right) by { rewrite(y->rb_right == at(recolor_parent, y->rb_right)); assumption(); }
                            have x->rb_left == at(recolor_parent, x->rb_left) by solve();
                            have x->rb_left == at(before_recolor, x->rb_left) by { rewrite(x->rb_left == at(recolor_parent, x->rb_left)); assumption(); }
                            have x->rb_right == at(recolor_parent, x->rb_right) by solve();
                            have x->rb_right == at(before_recolor, x->rb_right) by { rewrite(x->rb_right == at(recolor_parent, x->rb_right)); assumption(); }
                            have parent == 0 by { assumption(); }
                            mark recolor_last;
                            step();
                            have separate(statement(1).statement(4).statement(10).statement(4).footprint, memory(z->__rb_parent_color)) by {
                                normalize() using { separate(memory(x->__rb_parent_color), memory(z->__rb_parent_color)); };
                            }
                            have z->__rb_parent_color == at(recolor_last, z->__rb_parent_color) by {
                                transport_certificate {
                                    premise 0: separate(statement(1).statement(4).statement(10).statement(4).footprint, memory(z->__rb_parent_color)) => separate(statement(1).statement(4).statement(10).statement(4).footprint, memory(z->__rb_parent_color));
                                    preserve 0 => z->__rb_parent_color == at(recolor_last, z->__rb_parent_color);
                                    conclusion 1;
                                }
                            }
                            have z->__rb_parent_color == address(x) + (z->__rb_parent_color & 1) by { rewrite(z->__rb_parent_color == at(recolor_last, z->__rb_parent_color)); assumption(); }
                            have separate(statement(1).statement(4).statement(10).statement(4).footprint, memory(root->rb_node)) by {
                                normalize() using { separate(memory(root->rb_node), memory(x->__rb_parent_color)); };
                            }
                            have root->rb_node == at(recolor_last, root->rb_node) by {
                                transport_certificate {
                                    premise 0: separate(statement(1).statement(4).statement(10).statement(4).footprint, memory(root->rb_node)) => separate(statement(1).statement(4).statement(10).statement(4).footprint, memory(root->rb_node));
                                    preserve 0 => root->rb_node == at(recolor_last, root->rb_node);
                                    conclusion 1;
                                }
                            }
                            have root->rb_node == x by { rewrite(root->rb_node == at(recolor_last, root->rb_node)); assumption(); }
                            have separate(statement(1).statement(4).statement(10).statement(4).footprint, memory(z->rb_left)) by {
                                normalize() using { separate(memory(z->rb_left), memory(x->__rb_parent_color)); };
                            }
                            have z->rb_left == at(recolor_last, z->rb_left) by {
                                transport_certificate {
                                    premise 0: separate(statement(1).statement(4).statement(10).statement(4).footprint, memory(z->rb_left)) => separate(statement(1).statement(4).statement(10).statement(4).footprint, memory(z->rb_left));
                                    preserve 0 => z->rb_left == at(recolor_last, z->rb_left);
                                    conclusion 1;
                                }
                            }
                            have z->rb_left == at(before_recolor, z->rb_left) by { rewrite(z->rb_left == at(recolor_last, z->rb_left)); assumption(); }
                            have separate(statement(1).statement(4).statement(10).statement(4).footprint, memory(z->rb_right)) by {
                                normalize() using { separate(memory(z->rb_right), memory(x->__rb_parent_color)); };
                            }
                            have z->rb_right == at(recolor_last, z->rb_right) by {
                                transport_certificate {
                                    premise 0: separate(statement(1).statement(4).statement(10).statement(4).footprint, memory(z->rb_right)) => separate(statement(1).statement(4).statement(10).statement(4).footprint, memory(z->rb_right));
                                    preserve 0 => z->rb_right == at(recolor_last, z->rb_right);
                                    conclusion 1;
                                }
                            }
                            have z->rb_right == at(before_recolor, z->rb_right) by { rewrite(z->rb_right == at(recolor_last, z->rb_right)); assumption(); }
                            have separate(statement(1).statement(4).statement(10).statement(4).footprint, memory(y->rb_left)) by {
                                normalize() using { separate(memory(y->rb_left), memory(x->__rb_parent_color)); };
                            }
                            have y->rb_left == at(recolor_last, y->rb_left) by {
                                transport_certificate {
                                    premise 0: separate(statement(1).statement(4).statement(10).statement(4).footprint, memory(y->rb_left)) => separate(statement(1).statement(4).statement(10).statement(4).footprint, memory(y->rb_left));
                                    preserve 0 => y->rb_left == at(recolor_last, y->rb_left);
                                    conclusion 1;
                                }
                            }
                            have y->rb_left == at(before_recolor, y->rb_left) by { rewrite(y->rb_left == at(recolor_last, y->rb_left)); assumption(); }
                            have separate(statement(1).statement(4).statement(10).statement(4).footprint, memory(y->rb_right)) by {
                                normalize() using { separate(memory(y->rb_right), memory(x->__rb_parent_color)); };
                            }
                            have y->rb_right == at(recolor_last, y->rb_right) by {
                                transport_certificate {
                                    premise 0: separate(statement(1).statement(4).statement(10).statement(4).footprint, memory(y->rb_right)) => separate(statement(1).statement(4).statement(10).statement(4).footprint, memory(y->rb_right));
                                    preserve 0 => y->rb_right == at(recolor_last, y->rb_right);
                                    conclusion 1;
                                }
                            }
                            have y->rb_right == at(before_recolor, y->rb_right) by { rewrite(y->rb_right == at(recolor_last, y->rb_right)); assumption(); }
                            have separate(statement(1).statement(4).statement(10).statement(4).footprint, memory(x->rb_left)) by {
                                normalize() using { separate(memory(x->rb_left), memory(x->__rb_parent_color)); };
                            }
                            have x->rb_left == at(recolor_last, x->rb_left) by {
                                transport_certificate {
                                    premise 0: separate(statement(1).statement(4).statement(10).statement(4).footprint, memory(x->rb_left)) => separate(statement(1).statement(4).statement(10).statement(4).footprint, memory(x->rb_left));
                                    preserve 0 => x->rb_left == at(recolor_last, x->rb_left);
                                    conclusion 1;
                                }
                            }
                            have x->rb_left == at(before_recolor, x->rb_left) by { rewrite(x->rb_left == at(recolor_last, x->rb_left)); assumption(); }
                            have separate(statement(1).statement(4).statement(10).statement(4).footprint, memory(x->rb_right)) by {
                                normalize() using { separate(memory(x->rb_right), memory(x->__rb_parent_color)); };
                            }
                            have x->rb_right == at(recolor_last, x->rb_right) by {
                                transport_certificate {
                                    premise 0: separate(statement(1).statement(4).statement(10).statement(4).footprint, memory(x->rb_right)) => separate(statement(1).statement(4).statement(10).statement(4).footprint, memory(x->rb_right));
                                    preserve 0 => x->rb_right == at(recolor_last, x->rb_right);
                                    conclusion 1;
                                }
                            }
                            have x->rb_right == at(before_recolor, x->rb_right) by { rewrite(x->rb_right == at(recolor_last, x->rb_right)); assumption(); }
                            transport(at(before_recolor, root->rb_node == x), root->rb_node == x) using {
                                tmp == z;
                                gparent == x;
                                at(before_recolor, parent) == y;
                                at(before_recolor, root->rb_node == x);
                                separate(memory(root->rb_node), memory(x->__rb_parent_color));
                                separate(memory(root->rb_node), memory(y->__rb_parent_color));
                                separate(memory(root->rb_node), memory(z->__rb_parent_color));
                            };
                            transport(at(before_recolor, z->rb_left) == at(before_recolor, z->rb_left),
                                      z->rb_left == at(before_recolor, z->rb_left)) using {
                                tmp == z;
                                gparent == x;
                                at(before_recolor, parent) == y;
                                separate(memory(z->rb_left), memory(x->__rb_parent_color));
                                separate(memory(z->rb_left), memory(y->__rb_parent_color));
                                separate(memory(z->rb_left), memory(z->__rb_parent_color));
                            };
                            transport(at(before_recolor, z->rb_right) == at(before_recolor, z->rb_right),
                                      z->rb_right == at(before_recolor, z->rb_right)) using {
                                tmp == z;
                                gparent == x;
                                at(before_recolor, parent) == y;
                                separate(memory(z->rb_right), memory(x->__rb_parent_color));
                                separate(memory(z->rb_right), memory(y->__rb_parent_color));
                                separate(memory(z->rb_right), memory(z->__rb_parent_color));
                            };
                            transport(at(before_recolor, y->rb_left) == at(before_recolor, y->rb_left),
                                      y->rb_left == at(before_recolor, y->rb_left)) using {
                                tmp == z;
                                gparent == x;
                                at(before_recolor, parent) == y;
                                separate(memory(y->rb_left), memory(x->__rb_parent_color));
                                separate(memory(y->rb_left), memory(y->__rb_parent_color));
                                separate(memory(y->rb_left), memory(z->__rb_parent_color));
                            };
                            transport(at(before_recolor, y->rb_right) == at(before_recolor, y->rb_right),
                                      y->rb_right == at(before_recolor, y->rb_right)) using {
                                tmp == z;
                                gparent == x;
                                at(before_recolor, parent) == y;
                                separate(memory(y->rb_right), memory(x->__rb_parent_color));
                                separate(memory(y->rb_right), memory(y->__rb_parent_color));
                                separate(memory(y->rb_right), memory(z->__rb_parent_color));
                            };
                            transport(at(before_recolor, x->rb_left) == at(before_recolor, x->rb_left),
                                      x->rb_left == at(before_recolor, x->rb_left)) using {
                                tmp == z;
                                gparent == x;
                                at(before_recolor, parent) == y;
                                separate(memory(x->rb_left), memory(x->__rb_parent_color));
                                separate(memory(x->rb_left), memory(y->__rb_parent_color));
                                separate(memory(x->rb_left), memory(z->__rb_parent_color));
                            };
                            transport(at(before_recolor, x->rb_right) == at(before_recolor, x->rb_right),
                                      x->rb_right == at(before_recolor, x->rb_right)) using {
                                tmp == z;
                                gparent == x;
                                at(before_recolor, parent) == y;
                                separate(memory(x->rb_right), memory(x->__rb_parent_color));
                                separate(memory(x->rb_right), memory(y->__rb_parent_color));
                                separate(memory(x->rb_right), memory(z->__rb_parent_color));
                            };
                            let u_tree = fold(sized_at(z), { model: SizedTree::Node(z, x, Color::Black, 1, SizedTree::Empty, SizedTree::Empty) }, { metadata: u_size, right: u_left, left: u_right });
                            have sized_parent_is(focus.model,y) == 1 by {
                                rewrite(focus.model == SizedTree::Node(old(node), y, Color::Red, 1, SizedTree::Empty, SizedTree::Empty));
                                unfold(sized_parent_is(SizedTree::Node(old(node), y, Color::Red, 1, SizedTree::Empty, SizedTree::Empty),y)); normalize();
                            }
                            unfold(sized_parent_is(SizedTree::Empty,y));
                            unfold(sized_value(SizedTree::Empty));
                            unfold(sized_value(SizedTree::Node(old(node), y, Color::Red, 1, SizedTree::Empty, SizedTree::Empty)));
                            have to_integer(2) == 1 + to_integer(sized_value(SizedTree::Empty)) + to_integer(sized_value(SizedTree::Node(old(node), y, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))) by {
                                rewrite(sized_value(SizedTree::Node(old(node), y, Color::Red, 1, SizedTree::Empty, SizedTree::Empty)) == 1);
                                rewrite(sized_value(SizedTree::Empty) == 0); normalize();
                            }
                            let p_tree = fold(sized_at(y), { model: SizedTree::Node(y, x, Color::Black, 2, SizedTree::Empty, SizedTree::Node(old(node), y, Color::Red, 1, SizedTree::Empty, SizedTree::Empty)) }, { metadata: p_size, right: focus, left: p_right });
                            have sized_parent_is(p_tree.model,x) == 1 by {
                                rewrite(p_tree.model == SizedTree::Node(y, x, Color::Black, 2, SizedTree::Empty, SizedTree::Node(old(node), y, Color::Red, 1, SizedTree::Empty, SizedTree::Empty)));
                                unfold(sized_parent_is(SizedTree::Node(y, x, Color::Black, 2, SizedTree::Empty, SizedTree::Node(old(node), y, Color::Red, 1, SizedTree::Empty, SizedTree::Empty)),x)); normalize();
                            }
                            have sized_parent_is(u_tree.model,x) == 1 by {
                                rewrite(u_tree.model == SizedTree::Node(z, x, Color::Black, 1, SizedTree::Empty, SizedTree::Empty));
                                unfold(sized_parent_is(SizedTree::Node(z, x, Color::Black, 1, SizedTree::Empty, SizedTree::Empty),x)); normalize();
                            }
                            unfold(sized_value(SizedTree::Node(y, x, Color::Black, 2, SizedTree::Empty, SizedTree::Node(old(node), y, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))));
                            unfold(sized_value(SizedTree::Node(z, x, Color::Black, 1, SizedTree::Empty, SizedTree::Empty)));
                            have to_integer(4) == 1 + to_integer(sized_value(SizedTree::Node(z, x, Color::Black, 1, SizedTree::Empty, SizedTree::Empty))) + to_integer(sized_value(SizedTree::Node(y, x, Color::Black, 2, SizedTree::Empty, SizedTree::Node(old(node), y, Color::Red, 1, SizedTree::Empty, SizedTree::Empty)))) by {
                                rewrite(sized_value(SizedTree::Node(y, x, Color::Black, 2, SizedTree::Empty, SizedTree::Node(old(node), y, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))) == 2);
                                rewrite(sized_value(SizedTree::Node(z, x, Color::Black, 1, SizedTree::Empty, SizedTree::Empty)) == 1); normalize();
                            }
                            let focus = fold(sized_at(x), { model: SizedTree::Node(x, 0, Color::Red, 4, SizedTree::Node(z, x, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(y, x, Color::Black, 2, SizedTree::Empty, SizedTree::Node(old(node), y, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))) }, { metadata: g_size, right: p_tree, left: u_tree });
                            let state = fold(sized_mirrored_flip_at(old(node),root), { phase: SizedMirroredFlipPhase::After(x, y, z), model: SizedTree::Node(x, 0, Color::Red, 4, SizedTree::Node(z, x, Color::Black, 1, SizedTree::Empty, SizedTree::Empty), SizedTree::Node(y, x, Color::Black, 2, SizedTree::Empty, SizedTree::Node(old(node), y, Color::Red, 1, SizedTree::Empty, SizedTree::Empty))), context: SizedContext::Top }, { focus: focus, path: top });
                            unfold(sized_context_depth(SizedContext::Top));
                            have 0 <= sized_context_depth(state.context) by solve();
                            have sized_context_depth(state.context) < sized_context_depth(at(iteration,state.context)) by {
                                rewrite(state.context == SizedContext::Top);
                                rewrite(at(iteration,state.context) == SizedContext::Right(y, x, Color::Red, 2, SizedTree::Empty, SizedContext::Right(x, 0, Color::Black, 4, SizedTree::Node(z, x, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedContext::Top)));
                                unfold(sized_context_depth(SizedContext::Right(y, x, Color::Red, 2, SizedTree::Empty, SizedContext::Right(x, 0, Color::Black, 4, SizedTree::Node(z, x, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedContext::Top))));
                                unfold(sized_context_depth(SizedContext::Right(x, 0, Color::Black, 4, SizedTree::Node(z, x, Color::Red, 1, SizedTree::Empty, SizedTree::Empty), SizedContext::Top)));
                                unfold(sized_context_depth(SizedContext::Top)); normalize();
                            }
                            unfold(sized_mirrored_flip_focus(SizedMirroredFlipPhase::After(x, y, z),old(node)));
                            unfold(sized_mirrored_flip_parent(SizedMirroredFlipPhase::After(x, y, z)));
                            unfold(sized_mirrored_flip_finish(SizedMirroredFlipPhase::Before(x, y, z)));
                            have sized_mirrored_flip_finish(state.phase) == sized_mirrored_flip_finish(old(state.phase)) by {
                                rewrite(state.phase == SizedMirroredFlipPhase::After(x, y, z));
                                unfold(sized_mirrored_flip_finish(SizedMirroredFlipPhase::After(x, y, z)));
                                rewrite(SizedMirroredFlipPhase::Done(x, y, z) == sized_mirrored_flip_finish(SizedMirroredFlipPhase::Before(x, y, z)));
                                rewrite(SizedMirroredFlipPhase::Before(x, y, z) == at(iteration,state.phase)); assumption();
                            }
                            have sized_mirrored_flip_running(state.phase) == 1 by {
                                rewrite(state.phase == SizedMirroredFlipPhase::After(x, y, z));
                                unfold(sized_mirrored_flip_running(SizedMirroredFlipPhase::After(x, y, z))); normalize();
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
    owns state: sized_mirrored_flip_at(node, root);
    requires sized_mirrored_flip_pending(state.phase) == 1;
    ensures state.phase == sized_mirrored_flip_finish(old(state.phase));
} by {
    step(__rb_insert, { state: state });
}

void rb_insert_augmented(struct rb_node* node, struct rb_root* root,
                  const struct rb_augment_callbacks* augment) {
    views augment->rotate;
    owns state: sized_mirrored_flip_at(node, root);
    requires sized_mirrored_flip_pending(state.phase) == 1;
    ensures state.phase == sized_mirrored_flip_finish(old(state.phase));
} by {
    step(__rb_insert_augmented, { state: state });
}
