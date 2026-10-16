// One general contract for the unchanged Linux `__rb_erase_augmented`: any
// node of a valid, parent-consistent tree. Each C exit is one arm of a single
// proof, and the outcome resource says which exit was taken.
verifying "rb_erase.c";
import "rbtree_erase_callbacks.click";
import "rbtree_change_child.click";
import "../rbtree-model/rbtree_spine_resources.click";
import "rbtree_refold_to_root.click";
import "../rbtree-model/rbtree_erase_one_child.click";

// The subtree that replaces the erased node, before any erase-color repair.
function erase_deep_model(tree: RbTree) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(node, parent, color, left, right) => rb_successor_splice(erase_minimum_identity(rb_minimum(right)), parent, color, left, right),
    }
}

function erase_child_deep_model(tree: RbTree) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(node, parent, color, left, right) => rb_successor_child_splice(erase_minimum_identity(rb_minimum(right)), parent, color, left, right),
    }
}

function erase_deep_context(tree: RbTree, up: Context) -> Context {
    match tree {
        RbTree::Empty => up,
        RbTree::Node(node, parent, color, left, right) => rb_successor_context(erase_minimum_identity(rb_minimum(right)), parent, color, left, right, up),
    }
}

tactic refold_erase_spine(focus: struct rb_node*, anchor: struct rb_node*) {
    consumes c: erase_spine_at(focus, anchor);
    decreases erase_spine_depth(c.model);
    consumes t: rb_at(focus);
    requires rb_parent_consistent(plug(erase_context(c.model), t.model), anchor) == 1;
    produces whole: erase_left_at(anchor);
    ensures whole.model == plug(erase_context(old(c.model)), old(t.model));
} by {
    match c.model {
        EraseSpine::Top => {
            unfold(c);
            let whole = fold(erase_left_at(anchor), { model: t.model }, { tree: t });
            have plug(Context::Top, old(t.model)) == old(t.model) by {
                unfold(plug(Context::Top, old(t.model))); normalize();
            }
            have whole.model == plug(erase_context(old(c.model)), old(t.model)) by {
                rewrite(old(c.model) == EraseSpine::Top);
                unfold(erase_context(EraseSpine::Top));
                rewrite(plug(Context::Top, old(t.model)) == old(t.model)); simp();
            }
        },
        EraseSpine::Left(identity, grandparent, color, sibling_model, up_model) => {
            have erase_context(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model))
                == Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)) by {
                unfold(erase_context(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model))); normalize();
            }
            have rb_parent_consistent(plug(Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)), t.model), anchor) == 1 by {
                rewrite(Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)) == erase_context(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model)));
                rewrite(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model) == c.model);
                assumption();
            }
            apply(plug_parent_consistent_ctx(Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)), t.model, anchor)) using {
                rb_parent_consistent(plug(Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)), t.model), anchor) == 1;
            };
            apply(ctx_consistent_left_focus(identity, grandparent, color, sibling_model, erase_context(up_model), t.model, anchor)) using {
                ctx_consistent(Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)), t.model, anchor) == 1;
            };
            apply(erase_parent_consistent_parent_is(t.model, identity)) using {
                rb_parent_consistent(t.model, identity) == 1;
            };
            let { sibling: s, up: u } = unfold(c);
            let sub = fold(rb_at(identity), { model: RbTree::Node(identity, grandparent, color, old(t.model), sibling_model) }, { left: t, right: s });
            apply(erase_spine_depth_is_nonnegative(up_model));
            have 0 <= erase_spine_depth(u.model) by {
                rewrite(u.model == up_model);
                assumption();
            }
            have erase_spine_depth(old(c.model)) == erase_spine_depth(up_model) + 1 by {
                rewrite(old(c.model) == EraseSpine::Left(identity, grandparent, color, sibling_model, up_model));
                unfold(erase_spine_depth(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model)));
                normalize();
            }
            have erase_spine_depth(u.model) < erase_spine_depth(old(c.model)) by {
                rewrite(u.model == up_model);
                arithmetic() using { erase_spine_depth(old(c.model)) == erase_spine_depth(up_model) + 1; };
            }
            have plug(Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)), old(t.model)) == plug(erase_context(up_model), RbTree::Node(identity, grandparent, color, old(t.model), sibling_model)) by {
                unfold(plug(Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)), old(t.model)));
                normalize();
            }
            have rb_parent_consistent(plug(erase_context(u.model), sub.model), anchor) == 1 by {
                rewrite(u.model == up_model);
                rewrite(sub.model == RbTree::Node(identity, grandparent, color, old(t.model), sibling_model));
                rewrite(plug(erase_context(up_model), RbTree::Node(identity, grandparent, color, old(t.model), sibling_model)) == plug(Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)), old(t.model)));
                rewrite(Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)) == erase_context(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model)));
                rewrite(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model) == old(c.model));
                assumption();
            }
            let { whole: whole } = refold_erase_spine(identity, anchor, { c: u, t: sub });
            have whole.model == plug(erase_context(old(c.model)), old(t.model)) by {
                rewrite(old(c.model) == EraseSpine::Left(identity, grandparent, color, sibling_model, up_model));
                rewrite(erase_context(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model)) == Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)));
                rewrite(plug(Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)), old(t.model)) == plug(erase_context(up_model), RbTree::Node(identity, grandparent, color, old(t.model), sibling_model)));
                simp();
            }
        },
    }
}

// A nonempty focus is still the leftmost candidate through every spine frame.
tactic open_erase_spine_link(focus: struct rb_node*, parent: struct rb_node*, anchor: struct rb_node*) {
    consumes c: erase_spine_at(focus, anchor);
    requires parent == erase_spine_parent(c.model, anchor);
    produces parent->rb_left;
    produces frame: erase_spine_frame(parent, anchor);
    ensures parent->rb_left == focus;
    ensures parent != 0;
    ensures frame.model == old(c.model);
} by {
    match c.model {
        EraseSpine::Top => {
            have erase_spine_parent(c.model, anchor) == anchor by {
                rewrite(c.model == EraseSpine::Top);
                unfold(erase_spine_parent(EraseSpine::Top, anchor)); normalize();
            }
            have parent == anchor by { normalize() using { }; }
            unfold(c);
            have parent != 0;
            let frame = fold(erase_spine_frame(parent, anchor), { model: EraseSpine::Top });
            have parent->rb_left == focus;
            have frame.model == old(c.model);
        },
        EraseSpine::Left(identity, grandparent, color, sibling_model, up_model) => {
            have erase_spine_parent(c.model, anchor) == identity by {
                rewrite(c.model == EraseSpine::Left(identity, grandparent, color, sibling_model, up_model));
                unfold(erase_spine_parent(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model), anchor)); normalize();
            }
            have parent == identity by { normalize() using { }; }
            let { sibling: sibling, up: up } = unfold(c);
            let frame = fold(erase_spine_frame(parent, anchor), {
                model: EraseSpine::Left(identity, grandparent, color, sibling_model, up_model)
            });
        },
    }
}

tactic close_erase_spine_link(focus: struct rb_node*, parent: struct rb_node*, anchor: struct rb_node*) {
    consumes parent->rb_left;
    consumes frame: erase_spine_frame(parent, anchor);
    requires parent->rb_left == focus;
    produces c: erase_spine_at(focus, anchor);
    ensures c.model == old(frame.model);
} by {
    match frame.model {
        EraseSpine::Top => {
            unfold(frame);
            have anchor->rb_left == focus;
            let c = fold(erase_spine_at(focus, anchor), { model: EraseSpine::Top });
            have c.model == old(frame.model);
        },
        EraseSpine::Left(identity, grandparent, color, sibling_model, up_model) => {
            let { sibling: sibling, up: up } = unfold(frame);
            have parent != 0 by { rewrite(parent == identity); assumption(); }
            have aligned(parent, 8) by { rewrite(parent == identity); assumption(); }
            have rb_parent_is(sibling_model, parent) == 1 by { rewrite(parent == identity); assumption(); }
            let c = fold(erase_spine_at(focus, anchor), {
                model: EraseSpine::Left(identity, grandparent, color, sibling_model, up_model)
            });
        },
    }
}

tactic graft_erase_spine(focus: struct rb_node*, anchor: struct rb_node*, root: struct rb_root*) {
    consumes c: erase_spine_at(focus, anchor);
    consumes base: erase_anchor_frame(anchor, root);
    decreases erase_spine_depth(c.model);
    requires erase_spine_links(c.model, anchor) == 1;
    produces context: ctx_at(focus, root);
    ensures context.model == ctx_concat(erase_context(old(c.model)),
        erase_anchor_context(anchor, old(base.model)));
} by {
    match base.model {
        EraseAnchorFrame::At(ap, ac, ar, au) => {
    have erase_anchor_context(anchor, old(base.model)) == Context::Left(anchor, ap, ac, ar, au) by {
        rewrite(old(base.model) == EraseAnchorFrame::At(ap, ac, ar, au));
        unfold(erase_anchor_context(anchor, EraseAnchorFrame::At(ap, ac, ar, au))); normalize();
    }
    match c.model {
        EraseSpine::Top => {
            unfold(c);
            let { right: right, up: outer_context } = unfold(base);
            let context = fold(ctx_at(focus, root), {
                model: Context::Left(anchor, ap, ac, ar, au)
            }, { sibling: right, up: outer_context });
            have context.model == ctx_concat(erase_context(old(c.model)),
                Context::Left(anchor, ap, ac, ar, au)) by {
                rewrite(old(c.model) == EraseSpine::Top);
                unfold(erase_context(EraseSpine::Top));
                unfold(ctx_concat(Context::Top, Context::Left(anchor, ap, ac, ar, au)));
                simp();
            }
            have context.model == ctx_concat(erase_context(old(c.model)), erase_anchor_context(anchor, old(base.model))) by {
                rewrite(erase_anchor_context(anchor, old(base.model)) == Context::Left(anchor, ap, ac, ar, au)); assumption();
            }
        },
        EraseSpine::Left(identity, grandparent, color, sibling_model, up_model) => {
            unfold(erase_spine_links(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model), anchor));
            have grandparent == erase_spine_parent(up_model, anchor) by auto();
            have erase_spine_links(up_model, anchor) == 1 by auto();
            let { sibling: sibling, up: path_tail } = unfold(c);
            apply(erase_spine_depth_is_nonnegative(up_model));
            have erase_spine_depth(old(c.model)) == erase_spine_depth(up_model) + 1 by {
                rewrite(old(c.model) == EraseSpine::Left(identity, grandparent, color, sibling_model, up_model));
                unfold(erase_spine_depth(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model))); normalize();
            }
            have erase_spine_depth(path_tail.model) < erase_spine_depth(old(c.model)) by auto();
            mark grafting_tail;
            let { context: above } = graft_erase_spine(identity, anchor, root, { c: path_tail, base: base });
            have above.model == ctx_concat(erase_context(at(grafting_tail, path_tail.model)),
                erase_anchor_context(anchor, at(grafting_tail, base.model))) by { assumption(); }
            have erase_anchor_context(anchor, EraseAnchorFrame::At(ap, ac, ar, au)) == Context::Left(anchor, ap, ac, ar, au) by auto();
            have above.model == ctx_concat(erase_context(up_model),
                Context::Left(anchor, ap, ac, ar, au)) by {
                rewrite(up_model == at(grafting_tail, path_tail.model));
                rewrite(Context::Left(anchor, ap, ac, ar, au) == erase_anchor_context(anchor, EraseAnchorFrame::At(ap, ac, ar, au)));
                rewrite(EraseAnchorFrame::At(ap, ac, ar, au) == at(grafting_tail, base.model)); assumption();
            }
            apply(erase_spine_context_parent(up_model, anchor, ap, ac, ar, au));
            let context = fold(ctx_at(focus, root), {
                model: Context::Left(identity, grandparent, color, sibling_model,
                    ctx_concat(erase_context(up_model), Context::Left(anchor, ap, ac, ar, au)))
            }, { up: above });
            have context.model == ctx_concat(erase_context(old(c.model)),
                Context::Left(anchor, ap, ac, ar, au)) by {
                rewrite(old(c.model) == EraseSpine::Left(identity, grandparent, color, sibling_model, up_model));
                unfold(erase_context(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model)));
                unfold(ctx_concat(Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)),
                    Context::Left(anchor, ap, ac, ar, au)));
                simp();
            }
            have context.model == ctx_concat(erase_context(old(c.model)), erase_anchor_context(anchor, old(base.model))) by auto();
        },
    }
        },
    }
}

spec enum EraseOutcome {
    Balanced(RbTree),
    Deficit(Context),
}

// What the unlink hands to `rb_erase`: either the whole tree and a null
// rebalance pointer, or the context of an empty hole at 0 whose repair starts
// at the nonnull `rebalance`.
resource erase_out(root: struct rb_root*, rebalance: struct rb_node*) {
    field model: EraseOutcome;
    match model {
        EraseOutcome::Balanced(t) => {
            owns whole: rb_root_at(root);
            fact whole.model == t;
            fact rebalance == 0;
        },
        EraseOutcome::Deficit(c) => {
            owns deficit: ctx_at(0, root);
            fact deficit.model == c;
            fact rebalance != 0;
            fact c != Context::Top;
            fact ctx_node_is(c, rebalance) == 1;
        },
    }
}

function erase_leaf_outcome(color: Color, up: Context) -> EraseOutcome {
    match color {
        Color::Red => EraseOutcome::Balanced(plug(up, RbTree::Empty)),
        Color::Black => match up {
            Context::Top => EraseOutcome::Balanced(RbTree::Empty),
            Context::Left(id, above, pc, sibling, outer) => EraseOutcome::Deficit(up),
            Context::Right(id, above, pc, sibling, outer) => EraseOutcome::Deficit(up),
        },
    }
}

// Deeper successor: the minimum's replacement child and color decide whether
// splicing it out leaves a black deficit.
function erase_deep_outcome(tree: RbTree, up: Context, minimum: RbMinimum) -> EraseOutcome {
    match minimum {
        RbMinimum::Absent => EraseOutcome::Balanced(plug(up, erase_child_deep_model(tree))),
        RbMinimum::Found(successor, color, child) => match child {
            RbTree::Empty => match color {
                Color::Red => EraseOutcome::Balanced(plug(up, erase_child_deep_model(tree))),
                Color::Black => EraseOutcome::Deficit(erase_deep_context(tree, up)),
            },
            RbTree::Node(id, parent, child_color, left, right) =>
                EraseOutcome::Balanced(plug(up, erase_child_deep_model(tree))),
        },
    }
}

function erase_deep_splice(tree: RbTree, minimum: RbMinimum) -> RbTree {
    match minimum {
        RbMinimum::Absent => erase_child_deep_model(tree),
        RbMinimum::Found(successor, color, child) => match child {
            RbTree::Empty => match color {
                Color::Red => erase_child_deep_model(tree),
                Color::Black => erase_deep_model(tree),
            },
            RbTree::Node(id, parent, child_color, left, right) => erase_child_deep_model(tree),
        },
    }
}

theorem erase_unlink_red_if_not_black(c: Color) {
    requires not(c == Color::Black);
    ensures c == Color::Red by {
        induct(c) as ih {
            Color::Red => { normalize(); }
            Color::Black => {
                have Color::Black == Color::Black by normalize();
                contradiction(Color::Black == Color::Black);
            }
        }
    }
}

// A deeper minimum with a nonempty child, or a red leaf minimum, leaves the
// tree balanced.
theorem erase_deep_no_fixup(tree: RbTree, up: Context, successor: struct rb_node*,
    color: Color, child: RbTree) {
    requires not(child == RbTree::Empty) or color == Color::Red;
    ensures erase_deep_outcome(tree, up, RbMinimum::Found(successor, color, child))
        == EraseOutcome::Balanced(plug(up, erase_child_deep_model(tree))) by {
        induct(child) as ih {
            RbTree::Empty => {
                cases {
                    not(RbTree::Empty == RbTree::Empty) => {
                        have RbTree::Empty == RbTree::Empty by normalize();
                        contradiction(RbTree::Empty == RbTree::Empty);
                    }
                    color == Color::Red => {
                        rewrite(color == Color::Red);
                        unfold(erase_deep_outcome(tree, up, RbMinimum::Found(successor, Color::Red, RbTree::Empty)));
                        normalize();
                    }
                }
            }
            RbTree::Node(id, parent, child_color, left, right) => {
                unfold(erase_deep_outcome(tree, up, RbMinimum::Found(successor, color, RbTree::Node(id, parent, child_color, left, right))));
                normalize();
            }
        }
    }
    ensures erase_deep_splice(tree, RbMinimum::Found(successor, color, child)) == erase_child_deep_model(tree) by {
        induct(child) as ih {
            RbTree::Empty => {
                cases {
                    not(RbTree::Empty == RbTree::Empty) => {
                        have RbTree::Empty == RbTree::Empty by normalize();
                        contradiction(RbTree::Empty == RbTree::Empty);
                    }
                    color == Color::Red => {
                        rewrite(color == Color::Red);
                        unfold(erase_deep_splice(tree, RbMinimum::Found(successor, Color::Red, RbTree::Empty)));
                        normalize();
                    }
                }
            }
            RbTree::Node(id, parent, child_color, left, right) => {
                unfold(erase_deep_splice(tree, RbMinimum::Found(successor, color, RbTree::Node(id, parent, child_color, left, right))));
                normalize();
            }
        }
    }
}

// The C decision sequence: no left child, no right child, immediate
// successor, or deeper successor; then whether the spliced-out node leaves a
// black deficit.
function erase_outcome(tree: RbTree, up: Context) -> EraseOutcome {
    match tree {
        RbTree::Empty => EraseOutcome::Balanced(plug(up, RbTree::Empty)),
        RbTree::Node(node, parent, color, left, right) => match left {
            RbTree::Empty => match right {
                RbTree::Empty => erase_leaf_outcome(color, up),
                RbTree::Node(rid, rp, rc, rl, rr) =>
                    EraseOutcome::Balanced(plug(up, rb_erase_one_child_model(tree))),
            },
            RbTree::Node(lid, lp, lc, ll, lr) => match right {
                RbTree::Empty => EraseOutcome::Balanced(plug(up, rb_erase_one_child_model(tree))),
                RbTree::Node(rid, rp, rc, rl, rr) => match rl {
                    RbTree::Empty => match rr {
                        RbTree::Empty => match rc {
                            Color::Red => EraseOutcome::Balanced(plug(up, rb_erase_immediate_leaf_model(tree))),
                            Color::Black => EraseOutcome::Deficit(rb_erase_immediate_black_context(tree, up)),
                        },
                        RbTree::Node(cid, cp, cc, cl, cr) =>
                            EraseOutcome::Balanced(plug(up, rb_erase_immediate_child_model(tree))),
                    },
                    RbTree::Node(mid, mp, mc, ml, mr) => erase_deep_outcome(tree, up, rb_minimum(right)),
                },
            },
        },
    }
}

// The erased node's replacement subtree in its unchanged outer context.
function erase_splice(tree: RbTree) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(node, parent, color, left, right) => match left {
            RbTree::Empty => match right {
                RbTree::Empty => RbTree::Empty,
                RbTree::Node(rid, rp, rc, rl, rr) => rb_erase_one_child_model(tree),
            },
            RbTree::Node(lid, lp, lc, ll, lr) => match right {
                RbTree::Empty => rb_erase_one_child_model(tree),
                RbTree::Node(rid, rp, rc, rl, rr) => match rl {
                    RbTree::Empty => match rr {
                        RbTree::Empty => rb_erase_immediate_leaf_model(tree),
                        RbTree::Node(cid, cp, cc, cl, cr) => rb_erase_immediate_child_model(tree),
                    },
                    RbTree::Node(mid, mp, mc, ml, mr) => erase_deep_splice(tree, rb_minimum(right)),
                },
            },
        },
    }
}

// Below a two-child node whose right child has a left child, the outcome is
// decided by the right subtree's minimum.
theorem erase_outcome_deep(node: struct rb_node*, parent: struct rb_node*, color: Color,
    ln: struct rb_node*, lp: struct rb_node*, lc: Color, ll: RbTree, lr: RbTree,
    rn: struct rb_node*, rp: struct rb_node*, rc: Color,
    mn: struct rb_node*, mp: struct rb_node*, mc: Color, ml: RbTree, mr: RbTree,
    rr: RbTree, up: Context) {
    ensures erase_outcome(RbTree::Node(node, parent, color, RbTree::Node(ln, lp, lc, ll, lr), RbTree::Node(rn, rp, rc, RbTree::Node(mn, mp, mc, ml, mr), rr)), up) == erase_deep_outcome(RbTree::Node(node, parent, color, RbTree::Node(ln, lp, lc, ll, lr), RbTree::Node(rn, rp, rc, RbTree::Node(mn, mp, mc, ml, mr), rr)), up, rb_minimum(RbTree::Node(rn, rp, rc, RbTree::Node(mn, mp, mc, ml, mr), rr))) by {
        unfold(erase_outcome(RbTree::Node(node, parent, color, RbTree::Node(ln, lp, lc, ll, lr), RbTree::Node(rn, rp, rc, RbTree::Node(mn, mp, mc, ml, mr), rr)), up)); normalize();
    }
    ensures erase_splice(RbTree::Node(node, parent, color, RbTree::Node(ln, lp, lc, ll, lr), RbTree::Node(rn, rp, rc, RbTree::Node(mn, mp, mc, ml, mr), rr))) == erase_deep_splice(RbTree::Node(node, parent, color, RbTree::Node(ln, lp, lc, ll, lr), RbTree::Node(rn, rp, rc, RbTree::Node(mn, mp, mc, ml, mr), rr)), rb_minimum(RbTree::Node(rn, rp, rc, RbTree::Node(mn, mp, mc, ml, mr), rr))) by {
        unfold(erase_splice(RbTree::Node(node, parent, color, RbTree::Node(ln, lp, lc, ll, lr), RbTree::Node(rn, rp, rc, RbTree::Node(mn, mp, mc, ml, mr), rr)))); normalize();
    }
}

// The whole tree the outcome describes; a deficit context holds an empty hole.
function erase_out_tree(outcome: EraseOutcome) -> RbTree {
    match outcome {
        EraseOutcome::Balanced(t) => t,
        EraseOutcome::Deficit(c) => plug(c, RbTree::Empty),
    }
}

// A balanced outcome is red-black; a deficit context lacks one black level.
function erase_out_rb(outcome: EraseOutcome) -> int32 {
    match outcome {
        EraseOutcome::Balanced(t) => is_rb_root(t),
        EraseOutcome::Deficit(c) => ctx_rb(c, Nat::Succ(Nat::Zero), Color::Black),
    }
}

struct rb_node* __rb_erase_augmented(struct rb_node* node, struct rb_root* root,
                                    const struct rb_augment_callbacks* augment) {
    consumes tree: rb_at(node);
    consumes up: ctx_at(node, root);
    requires tree.model != RbTree::Empty;
    requires is_rb(tree.model) == 1;
    requires ctx_rb(up.model, black_height(tree.model), rb_color(tree.model)) == 1;
    requires ctx_consistent(up.model, tree.model, 0) == 1;
    views erase_callbacks(augment);
    produces node->__rb_parent_color;
    produces node->rb_left;
    produces node->rb_right;
    produces out: erase_out(root, result);
    ensures out.model == erase_outcome(old(tree.model), old(up.model));
    ensures erase_out_rb(out.model) == 1;
    ensures rb_tree_parent_consistent(erase_out_tree(out.model)) == 1;
    ensures erase_out_tree(out.model) == plug(old(up.model), erase_splice(old(tree.model)));
    ensures rb_inorder(erase_splice(old(tree.model)))
        == list::append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model))));
} by {
    // The deeper-successor exits come first: their proofs name the tree's
    // shape themselves.
    if rb_left(tree.model) != RbTree::Empty and rb_right(tree.model) != RbTree::Empty
        and rb_left(rb_right(tree.model)) != RbTree::Empty {
        // Deeper successor: descend to the minimum of the right subtree, splice it
        // out, and transplant it into the erased node's place. A black leaf minimum
        // leaves a deficit at its old parent; otherwise the tree stays balanced.
        if erase_minimum_child(rb_minimum(rb_right(tree.model))) == RbTree::Empty
            and erase_minimum_color(rb_minimum(rb_right(tree.model))) == Color::Black {
            match tree.model {
                RbTree::Empty => { contradiction(tree.model == RbTree::Empty); },
                RbTree::Node(identity, parent_model, color, left_model, right_model) => {
                    have rb_left(tree.model) == left_model by {
                        rewrite(tree.model == RbTree::Node(identity, parent_model, color, left_model, right_model));
                        unfold(rb_left(RbTree::Node(identity, parent_model, color, left_model, right_model))); normalize();
                    }
                    have rb_right(tree.model) == right_model by {
                        rewrite(tree.model == RbTree::Node(identity, parent_model, color, left_model, right_model));
                        unfold(rb_right(RbTree::Node(identity, parent_model, color, left_model, right_model))); normalize();
                    }
                    have left_model != RbTree::Empty by { rewrite(left_model == rb_left(tree.model)); assumption(); }
                    have right_model != RbTree::Empty by { rewrite(right_model == rb_right(tree.model)); assumption(); }
                    have erase_minimum_child(rb_minimum(right_model)) == RbTree::Empty by {
                        rewrite(right_model == rb_right(tree.model)); assumption();
                    }
                    have rb_left(right_model) != RbTree::Empty by auto();
                    apply(erase_context_parent(up.model, identity, parent_model, color, left_model, right_model));
                    apply(ctx_consistent_node_children(up.model, identity, parent_model, color, left_model, right_model, 0));
                    have is_rb(RbTree::Node(identity, parent_model, color, left_model, right_model)) == 1 by {
                        rewrite(RbTree::Node(identity, parent_model, color, left_model, right_model) == tree.model); assumption();
                    }
                    have ctx_rb(up.model, black_height(RbTree::Node(identity, parent_model, color, left_model, right_model)), rb_color(RbTree::Node(identity, parent_model, color, left_model, right_model))) == 1 by {
                        rewrite(RbTree::Node(identity, parent_model, color, left_model, right_model) == tree.model); assumption();
                    }
                    have rb_left(old(tree.model)) == left_model;
                    have rb_right(old(tree.model)) == right_model;
                    let { left: l, right: r } = unfold(tree);
                    match left_model {
                        RbTree::Empty => { contradiction(left_model == RbTree::Empty); },
                        RbTree::Node(lid, lp, lc, ll, lr) => {
                            let { left: ll_tree, right: lr_tree } = unfold(l);
                            match right_model {
                                RbTree::Empty => { contradiction(right_model == RbTree::Empty); },
                                RbTree::Node(rid, rp, rc, rl, rr) => {
                                    have rl != RbTree::Empty by {
                                        unfold(rb_left(RbTree::Node(rid, rp, rc, rl, rr)));
                                        rewrite(rl == rb_left(RbTree::Node(rid, rp, rc, rl, rr)));
                                        rewrite(RbTree::Node(rid, rp, rc, rl, rr) == right_model); assumption();
                                    }
                                    apply(rb_parent_consistent_node_left(rid, rp, rc, rl, rr, identity));
                                    let { left: t, right: right_sibling } = unfold(r);
                                    match rl {
                                        RbTree::Empty => { contradiction(rl == RbTree::Empty); },
                                        RbTree::Node(iid, ip, ic, il, ir) => {
                                            let { left: init_l, right: init_r } = unfold(t);
                                            let t = fold(rb_at(iid), { model: RbTree::Node(iid, ip, ic, il, ir) }, { left: init_l, right: init_r });
                                            step(); step(); step(); step(); step(); step(); step(); step(); step(); step(); step(); step(); step(); step();
                                            let c = fold(erase_spine_at(tmp, child), { model: EraseSpine::Top });
                                            have plug(erase_context(c.model), t.model) == rl by {
                                                rewrite(c.model == EraseSpine::Top);
                                                unfold(erase_context(EraseSpine::Top));
                                                unfold(plug(old(up.model), t.model)); simp();
                                            }
                                            have successor == erase_spine_parent(c.model, child) by {
                                                rewrite(c.model == EraseSpine::Top);
                                                unfold(erase_spine_parent(EraseSpine::Top, child)); simp();
                                            }
                                            loop {
                                                owns c: erase_spine_at(tmp, child);
                                                owns t: rb_at(tmp);
                                                decreases t;
                                                invariant tmp != 0;
                                                invariant successor == erase_spine_parent(c.model, child);
                                                invariant plug(erase_context(c.model), t.model) == rl;
                                                initialize by simp();
                                                preserve by {
                                                    match t.model {
                                                        RbTree::Empty => { unfold(t); have tmp != 0 by { simp(); } contradiction(tmp == 0); },
                                                        RbTree::Node(tid, tp, tc, tl, tr) => {
                                                            have plug(erase_context(EraseSpine::Left(tid, tp, tc, tr, c.model)), tl) == rl by {
                                                                unfold(erase_context(EraseSpine::Left(tid, tp, tc, tr, c.model)));
                                                                unfold(plug(Context::Left(tid, tp, tc, tr, erase_context(c.model)), tl));
                                                                rewrite(RbTree::Node(tid, tp, tc, tl, tr) == t.model); assumption();
                                                            }
                                                            let { left: next, right: sibling } = unfold(t);
                                                            have tmp == tid by auto();
                                                            have tid != 0 by auto();
                                                            have erase_spine_parent(EraseSpine::Left(tid, tp, tc, tr, c.model), child) == tid by auto();
                                                            let frame = fold(erase_spine_at(tmp->rb_left, child),
                                                                { model: EraseSpine::Left(tid, tp, tc, tr, c.model) }, { up: c });
                                                            step(); step(); step();
                                                            have successor == erase_spine_parent(frame.model, child);
                                                            if tmp == 0 {
                                                            } else {
                                                                close_invariants();
                                                            }
                                                        },
                                                    }
                                                }
                                            }
                                            have node->rb_left == lid;
                                            have tmp == 0;
                                            match t.model {
                                                RbTree::Node(a, b, col, lt, rt) => {
                                                    have t.model == RbTree::Empty by auto();
                                                    have t.model != RbTree::Empty by { rewrite(t.model == RbTree::Node(a, b, col, lt, rt)); normalize(); }
                                                    contradiction(t.model == RbTree::Empty);
                                                },
                                                RbTree::Empty => {
                                                    have c.model != EraseSpine::Top by auto();
                                                    match c.model {
                                                        EraseSpine::Top => { contradiction(c.model == EraseSpine::Top); },
                                                        EraseSpine::Left(mid, mp, mc, mr, mu) => {
                                                            apply(erase_spine_minimum(mu, RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                            have rb_minimum(rl) == RbMinimum::Found(mid, mc, mr) by {
                                                                rewrite(rl == plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                                rewrite(rb_minimum(plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)))
                                                                    == rb_minimum(RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                                unfold(rb_minimum(RbTree::Node(mid, mp, mc, RbTree::Empty, mr))); normalize();
                                                            }
                                                            apply(rb_minimum_nonempty_left(rid, rp, rc, rl, rr));
                                                            have rb_minimum(right_model) == RbMinimum::Found(mid, mc, mr) by {
                                                                rewrite(right_model == RbTree::Node(rid, rp, rc, rl, rr));
                                                                rewrite(rb_minimum(RbTree::Node(rid, rp, rc, rl, rr)) == rb_minimum(rl)); assumption();
                                                            }
                                                            have erase_minimum_child(rb_minimum(right_model)) == mr by {
                                                                rewrite(rb_minimum(right_model) == RbMinimum::Found(mid, mc, mr));
                                                                unfold(erase_minimum_child(RbMinimum::Found(mid, mc, mr))); normalize();
                                                            }
                                                            have erase_minimum_color(rb_minimum(right_model)) == mc by {
                                                                rewrite(rb_minimum(right_model) == RbMinimum::Found(mid, mc, mr));
                                                                unfold(erase_minimum_color(RbMinimum::Found(mid, mc, mr))); normalize();
                                                            }
                                                            apply(rb_erase_black_successor_splice(identity, mid, parent_model, color, left_model, right_model, up.model, 0));
                                                            have erase_minimum_identity(rb_minimum(right_model)) == mid by {
                                                                rewrite(rb_minimum(right_model) == RbMinimum::Found(mid, mc, mr));
                                                                unfold(erase_minimum_identity(RbMinimum::Found(mid, mc, mr))); normalize();
                                                            }
                                                            apply(erase_spine_focus_parent_consistent(mu, RbTree::Node(mid, mp, mc, RbTree::Empty, mr), rid));
                                                            apply(erase_parent_consistent_parent_is(RbTree::Node(mid, mp, mc, RbTree::Empty, mr), erase_spine_parent(mu, rid)));
                                                            apply(rb_parent_is_node_parent(mid, mp, mc, RbTree::Empty, mr, erase_spine_parent(mu, rid)));
                                                            apply(erase_spine_links_from_tree(mu, RbTree::Node(mid, mp, mc, RbTree::Empty, mr), rid));
                                                            apply(erase_spine_min_parent(mu, RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                            apply(rb_min_parent_nonempty_left(rid, rp, rc, rl, rr));
                                                            have rb_min_parent(right_model) == mp by {
                                                                rewrite(right_model == RbTree::Node(rid, rp, rc, rl, rr));
                                                                rewrite(rb_min_parent(RbTree::Node(rid, rp, rc, rl, rr)) == rb_min_parent(rl));
                                                                rewrite(rl == plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                                rewrite(rb_min_parent(plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)))
                                                                    == rb_min_parent(RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                                unfold(rb_min_parent(RbTree::Node(mid, mp, mc, RbTree::Empty, mr))); normalize();
                                                            }
                                                            let { sibling: min_right, up: path } = unfold(c);
                                                            have (mid->__rb_parent_color & 1) == color_bit(mc) by auto();
                                                            unfold(t);
                                                            have parent == erase_spine_parent(path.model, child);
                                                            have parent == mp by {
                                                                rewrite(parent == erase_spine_parent(path.model, child));
                                                                rewrite(path.model == mu); rewrite(child == rid);
                                                                rewrite(erase_spine_parent(mu, rid) == mp); normalize();
                                                            }
                                                            have path.model == mu;
                                                            mark opened_spine;
                                                            let { frame: link_frame } = open_erase_spine_link(successor, parent, child, { c: path });
                                                            have link_frame.model == at(opened_spine, path.model) by assumption();
                                                            mark moving;
                                                            step(); step(); step(); step();
                                                            apply(packed_parent_word(mid, at(moving, child->__rb_parent_color)));
                                                            have child->__rb_parent_color == address(mid) + (child->__rb_parent_color & 1) by {
                                                                rewrite(child->__rb_parent_color == ((at(moving, child->__rb_parent_color) & 1) | address(mid)));
                                                                assumption();
                                                            }
                                                            have (child->__rb_parent_color & 1) == (at(moving, child->__rb_parent_color) & 1) by {
                                                                rewrite(child->__rb_parent_color == ((at(moving, child->__rb_parent_color) & 1) | address(mid)));
                                                                assumption();
                                                            }
                                                            have (child->__rb_parent_color & 1) == color_bit(rc);
                                                            observe(erase_callbacks(augment));
                                                            have min_right.model == RbTree::Empty by { rewrite(min_right.model == mr); assumption(); }
                                                            unfold(min_right);
                                                            have color_bit(mc) == 1 by { rewrite(mc == Color::Black); unfold(color_bit(Color::Black)); normalize(); }
                                                            have (successor->__rb_parent_color & 1) == 1;
                                                            execute_until(statement(54));
                                                            have separate(memory(child->rb_right), memory(mid->rb_right));
                                                            have separate(memory(child->rb_right), memory(lid->__rb_parent_color));
                                                            have separate(memory(child->rb_right), memory(node->__rb_parent_color));
                                                            have separate(memory(child->rb_right), memory(parent->rb_left));
                                                            have separate(memory(child->rb_right), memory(mid->rb_left));
                                                            have separate(memory(child->rb_right), memory(child->__rb_parent_color));
                                                            let moved_left = fold(rb_at(lid), {
                                                                model: RbTree::Node(lid, mid, lc, ll, lr)
                                                            }, { left: ll_tree, right: lr_tree });
                                                            have moved_left.model == rb_reparent(left_model, mid) by {
                                                                rewrite(left_model == RbTree::Node(lid, lp, lc, ll, lr));
                                                                unfold(rb_reparent(RbTree::Node(lid, lp, lc, ll, lr), mid)); normalize();
                                                            }
                                                            have tmp == parent_model;
                                                            have ctx_node_is(up.model, tmp) == 1 by {
                                                                rewrite(tmp == parent_model); assumption();
                                                            }
                                                            have parent->rb_left == 0;
                                                            have successor == mid;
                                                            have aligned(successor, 8);
                                                            have child->__rb_parent_color == address(mid) + (child->__rb_parent_color & 1);
                                                            have child == rid;
                                                            have separate(memory(child->__rb_parent_color), memory(mid->__rb_parent_color));

                                                            mark transplant;
                                                            let { after: root_context } = step(__rb_change_child(node, successor, tmp, root), { before: up });
                                                            have child->rb_right == at(transplant, child->rb_right);
                                                            have child->__rb_parent_color == at(transplant, child->__rb_parent_color) by { normalize() using { child == rid; }; }
                                                            have parent->rb_left == at(transplant, parent->rb_left) by normalize();
                                                            have parent->rb_left == 0;
                                                            have root_context.model == at(transplant, up.model) by assumption();
                                                            have root_context.model == old(up.model);
                                                            have mid->__rb_parent_color == at(transplant, mid->__rb_parent_color);
                                                            have (successor->__rb_parent_color & 1) == 1 by {
                                                                rewrite(successor == mid); assumption();
                                                            }
                                                            mark parent_link_changed;
                                                            execute_until(statement(62));
                                                            have tmp == mid;
                                                            let hole = fold(rb_at(0), { model: RbTree::Empty });
                                                            have parent->rb_left == 0;
                                                            mark closing_spine;
                                                            let { c: path2 } = close_erase_spine_link(0, parent, child, { frame: link_frame });
                                                            apply(rb_reparent_parent_is(left_model, mid));
                                                            have rb_parent_is(rb_reparent(left_model, mid), mid) == 1 by assumption();
                                                            have mid->rb_left == lid;
                                                            have mid->rb_right == child;
                                                            let above = fold(ctx_at(child, root), {
                                                                model: Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model))
                                                            }, { sibling: moved_left, up: root_context });
                                                            have ctx_node_is(above.model, mid) == 1 by {
                                                                rewrite(above.model == Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)));
                                                                unfold(ctx_node_is(Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)), mid)); normalize();
                                                            }
                                                            have above.model == ctx_reroot(above.model, mid) by {
                                                                rewrite(above.model == Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)));
                                                                unfold(ctx_reroot(Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)), mid)); normalize();
                                                            }
                                                            have child->rb_right == at(transplant, child->rb_right) by auto();
                                                            have child->__rb_parent_color == at(transplant, child->__rb_parent_color) by auto();
                                                            have right_sibling.model == rr;
                                                            let anchor_frame = fold(erase_anchor_frame(child, root), {
                                                                model: EraseAnchorFrame::At(mid, rc, rr, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)))
                                                            }, { right: right_sibling, up: above });
                                                            have erase_spine_links(path2.model, child) == 1 by {
                                                                rewrite(path2.model == mu); rewrite(child == rid); assumption();
                                                            }
                                                            mark grafting;
                                                            let { context: deficit } = graft_erase_spine(0, child, root, { c: path2, base: anchor_frame });
                                                            have deficit.model == ctx_concat(erase_context(at(grafting, path2.model)),
                                                                erase_anchor_context(child, EraseAnchorFrame::At(mid, rc, rr, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model))))) by { assumption(); }
                                                            have at(grafting, path2.model) == mu by assumption();
                                                            have erase_anchor_context(child, EraseAnchorFrame::At(mid, rc, rr,
                                                                Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model))))
                                                                == Context::Left(rid, mid, rc, rr, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model))) by {
                                                                unfold(erase_anchor_context(child, EraseAnchorFrame::At(mid, rc, rr,
                                                                    Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)))));
                                                                rewrite(child == rid); normalize();
                                                            }
                                                            have deficit.model == ctx_concat(erase_context(mu),
                                                                Context::Left(rid, mid, rc, rr, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)))) by {
                                                                rewrite(mu == at(grafting, path2.model));
                                                                rewrite(Context::Left(rid, mid, rc, rr, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)))
                                                                    == erase_anchor_context(child, EraseAnchorFrame::At(mid, rc, rr,
                                                                        Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)))));
                                                                assumption();
                                                            }
                                                            apply(erase_spine_min_context(mu, RbTree::Node(mid, mp, mc, RbTree::Empty, mr),
                                                                Context::Left(rid, mid, rc, rr, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)))));
                                                            apply(rb_min_context_nonempty_left(rid, mid, rc, rl, rr,
                                                                Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model))));
                                                            have rb_successor_context(mid, parent_model, color, left_model, right_model, old(up.model))
                                                                == ctx_concat(erase_context(mu), Context::Left(rid, mid, rc, rr,
                                                                    Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)))) by {
                                                                unfold(rb_successor_context(mid, parent_model, color, left_model, right_model, old(up.model)));
                                                                rewrite(right_model == RbTree::Node(rid, rp, rc, rl, rr));
                                                                unfold(rb_reparent(RbTree::Node(rid, rp, rc, rl, rr), mid));
                                                                rewrite(rb_min_context(RbTree::Node(rid, mid, rc, rl, rr),
                                                                    Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)))
                                                                    == rb_min_context(rl, Context::Left(rid, mid, rc, rr,
                                                                        Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)))));
                                                                rewrite(rl == plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                                rewrite(rb_min_context(plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)),
                                                                    Context::Left(rid, mid, rc, rr, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model))))
                                                                    == rb_min_context(RbTree::Node(mid, mp, mc, RbTree::Empty, mr),
                                                                        ctx_concat(erase_context(mu), Context::Left(rid, mid, rc, rr, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model))))));
                                                                unfold(rb_min_context(RbTree::Node(mid, mp, mc, RbTree::Empty, mr),
                                                                    ctx_concat(erase_context(mu), Context::Left(rid, mid, rc, rr, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)))))); normalize();
                                                            }
                                                            have deficit.model == rb_successor_context(mid, parent_model, color, left_model, right_model, old(up.model)) by {
                                                                rewrite(rb_successor_context(mid, parent_model, color, left_model, right_model, old(up.model))
                                                                    == ctx_concat(erase_context(mu), Context::Left(rid, mid, rc, rr,
                                                                        Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model))))); assumption();
                                                            }
                                                            have deficit.model == erase_deep_context(old(tree.model), old(up.model)) by {
                                                                rewrite(old(tree.model) == RbTree::Node(identity, parent_model, color, left_model, right_model));
                                                                unfold(erase_deep_context(RbTree::Node(identity, parent_model, color, left_model, right_model), old(up.model)));
                                                                rewrite(erase_minimum_identity(rb_minimum(right_model)) == mid); assumption();
                                                            }
                                                            have ctx_rb(deficit.model, Nat::Succ(Nat::Zero), Color::Black) == 1 by {
                                                                rewrite(deficit.model == rb_successor_context(mid, parent_model, color, left_model, right_model, old(up.model))); assumption();
                                                            }
                                                            have ctx_consistent(deficit.model, hole.model, 0) == 1 by {
                                                                rewrite(hole.model == RbTree::Empty);
                                                                rewrite(deficit.model == rb_successor_context(mid, parent_model, color, left_model, right_model, old(up.model))); assumption();
                                                            }
                                                            have plug(deficit.model, hole.model) == plug(old(up.model), erase_deep_model(old(tree.model))) by {
                                                                rewrite(hole.model == RbTree::Empty);
                                                                rewrite(old(tree.model) == RbTree::Node(identity, parent_model, color, left_model, right_model));
                                                                unfold(erase_deep_model(RbTree::Node(identity, parent_model, color, left_model, right_model)));
                                                                rewrite(erase_minimum_identity(rb_minimum(right_model)) == mid);
                                                                rewrite(deficit.model == rb_successor_context(mid, parent_model, color, left_model, right_model, old(up.model))); assumption();
                                                            }
                                                            have rb_inorder(erase_deep_model(old(tree.model))) == list::append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model)))) by {
                                                                rewrite(old(tree.model) == RbTree::Node(identity, parent_model, color, left_model, right_model));
                                                                unfold(erase_deep_model(RbTree::Node(identity, parent_model, color, left_model, right_model)));
                                                                unfold(rb_left(RbTree::Node(identity, parent_model, color, left_model, right_model)));
                                                                unfold(rb_right(RbTree::Node(identity, parent_model, color, left_model, right_model)));
                                                                rewrite(erase_minimum_identity(rb_minimum(right_model)) == mid); assumption();
                                                            }
                                                            apply(erase_spine_context_parent(mu, rid, mid, rc, rr, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model))));
                                                            have ctx_node_is(deficit.model, rebalance) == 1 by {
                                                                rewrite(deficit.model == ctx_concat(erase_context(mu), Context::Left(rid, mid, rc, rr, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)))));
                                                                rewrite(rebalance == mp); rewrite(mp == erase_spine_parent(mu, rid)); assumption();
                                                            }
                                                            have deficit.model != Context::Top by {
                                                                if deficit.model == Context::Top {
                                                                    have ctx_node_is(Context::Top, rebalance) == 1 by { rewrite(Context::Top == deficit.model); assumption(); }
                                                                    have rebalance != 0;
                                                                    have ctx_node_is(Context::Top, rebalance) != 1 by {
                                                                        unfold(ctx_node_is(Context::Top, rebalance)); normalize() using { not(rebalance == 0); };
                                                                    }
                                                                    contradiction(ctx_node_is(Context::Top, rebalance) == 1);
                                                                } else { assumption(); }
                                                            }
                                                            have ctx_consistent(erase_deep_context(old(tree.model), old(up.model)), RbTree::Empty, 0) == 1 by {
                                                                rewrite(erase_deep_context(old(tree.model), old(up.model)) == deficit.model); rewrite(RbTree::Empty == hole.model); assumption();
                                                            }
                                                            apply(plug_parent_consistent_transport(erase_deep_context(old(tree.model), old(up.model)), RbTree::Empty, 0));
                                                            have rb_tree_parent_consistent(plug(erase_deep_context(old(tree.model), old(up.model)), RbTree::Empty)) == 1 by {
                                                                unfold(rb_tree_parent_consistent(plug(erase_deep_context(old(tree.model), old(up.model)), RbTree::Empty)));
                                                            }
                                                            apply(erase_outcome_deep(identity, parent_model, color, lid, lp, lc, ll, lr, rid, rp, rc, iid, ip, ic, il, ir, rr, old(up.model)));
                                                            have old(tree.model) == RbTree::Node(identity, parent_model, color, RbTree::Node(lid, lp, lc, ll, lr), RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)) by {
                                                                rewrite(old(tree.model) == RbTree::Node(identity, parent_model, color, left_model, right_model));
                                                                rewrite(left_model == RbTree::Node(lid, lp, lc, ll, lr));
                                                                rewrite(right_model == RbTree::Node(rid, rp, rc, rl, rr));
                                                                rewrite(rl == RbTree::Node(iid, ip, ic, il, ir)); normalize();
                                                            }
                                                            have rb_minimum(RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)) == RbMinimum::Found(mid, Color::Black, RbTree::Empty) by {
                                                                rewrite(RbTree::Node(iid, ip, ic, il, ir) == rl);
                                                                rewrite(RbTree::Node(rid, rp, rc, rl, rr) == right_model); assumption();
                                                            }
                                                            have erase_outcome(old(tree.model), old(up.model)) == EraseOutcome::Deficit(erase_deep_context(old(tree.model), old(up.model))) by {
                                                                rewrite(old(tree.model) == RbTree::Node(identity, parent_model, color, RbTree::Node(lid, lp, lc, ll, lr), RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)));
                                                                rewrite(erase_outcome(RbTree::Node(identity, parent_model, color, RbTree::Node(lid, lp, lc, ll, lr), RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)), old(up.model)) == erase_deep_outcome(RbTree::Node(identity, parent_model, color, RbTree::Node(lid, lp, lc, ll, lr), RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)), old(up.model), rb_minimum(RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr))));
                                                                rewrite(rb_minimum(RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)) == RbMinimum::Found(mid, Color::Black, RbTree::Empty));
                                                                unfold(erase_deep_outcome(RbTree::Node(identity, parent_model, color, RbTree::Node(lid, lp, lc, ll, lr), RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)), old(up.model), RbMinimum::Found(mid, Color::Black, RbTree::Empty)));
                                                                normalize();
                                                            }
                                                            have erase_splice(old(tree.model)) == erase_deep_model(old(tree.model)) by {
                                                                rewrite(old(tree.model) == RbTree::Node(identity, parent_model, color, RbTree::Node(lid, lp, lc, ll, lr), RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)));
                                                                rewrite(erase_splice(RbTree::Node(identity, parent_model, color, RbTree::Node(lid, lp, lc, ll, lr), RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr))) == erase_deep_splice(RbTree::Node(identity, parent_model, color, RbTree::Node(lid, lp, lc, ll, lr), RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)), rb_minimum(RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr))));
                                                                rewrite(rb_minimum(RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)) == RbMinimum::Found(mid, Color::Black, RbTree::Empty));
                                                                unfold(erase_deep_splice(RbTree::Node(identity, parent_model, color, RbTree::Node(lid, lp, lc, ll, lr), RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)), RbMinimum::Found(mid, Color::Black, RbTree::Empty)));
                                                                normalize();
                                                            }
                                                            have rb_inorder(erase_splice(old(tree.model))) == list::append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model)))) by {
                                                                rewrite(erase_splice(old(tree.model)) == erase_deep_model(old(tree.model))); assumption();
                                                            }
                                                            unfold(hole);
                                                            open(erase_callbacks(augment)) { execute(); }
                                                            have erase_deep_context(old(tree.model), old(up.model)) != Context::Top by {
                                                                rewrite(erase_deep_context(old(tree.model), old(up.model)) == deficit.model); assumption();
                                                            }
                                                            have ctx_node_is(erase_deep_context(old(tree.model), old(up.model)), result) == 1 by {
                                                                rewrite(erase_deep_context(old(tree.model), old(up.model)) == deficit.model); assumption();
                                                            }
                                                            let out = fold(erase_out(root, result), { model: EraseOutcome::Deficit(erase_deep_context(old(tree.model), old(up.model))) }, { deficit: deficit });
                                                            have erase_out_rb(out.model) == 1 by {
                                                                rewrite(out.model == EraseOutcome::Deficit(erase_deep_context(old(tree.model), old(up.model))));
                                                                unfold(erase_out_rb(EraseOutcome::Deficit(erase_deep_context(old(tree.model), old(up.model))))); assumption();
                                                            }
                                                            have erase_out_tree(out.model) == plug(erase_deep_context(old(tree.model), old(up.model)), RbTree::Empty) by {
                                                                rewrite(out.model == EraseOutcome::Deficit(erase_deep_context(old(tree.model), old(up.model))));
                                                                unfold(erase_out_tree(EraseOutcome::Deficit(erase_deep_context(old(tree.model), old(up.model))))); normalize();
                                                            }
                                                            have rb_tree_parent_consistent(erase_out_tree(out.model)) == 1 by {
                                                                rewrite(erase_out_tree(out.model) == plug(erase_deep_context(old(tree.model), old(up.model)), RbTree::Empty)); assumption();
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
                },
            }
        } else {
            have not(erase_minimum_child(rb_minimum(rb_right(tree.model))) == RbTree::Empty)
                or erase_minimum_color(rb_minimum(rb_right(tree.model))) == Color::Red by {
                if erase_minimum_child(rb_minimum(rb_right(tree.model))) == RbTree::Empty {
                    have not(erase_minimum_color(rb_minimum(rb_right(tree.model))) == Color::Black) by {
                        if erase_minimum_color(rb_minimum(rb_right(tree.model))) == Color::Black {
                            have erase_minimum_child(rb_minimum(rb_right(tree.model))) == RbTree::Empty
                                and erase_minimum_color(rb_minimum(rb_right(tree.model))) == Color::Black by assumption();
                            contradiction(erase_minimum_child(rb_minimum(rb_right(tree.model))) == RbTree::Empty
                                and erase_minimum_color(rb_minimum(rb_right(tree.model))) == Color::Black);
                        } else {
                            assumption();
                        }
                    }
                    apply(erase_unlink_red_if_not_black(erase_minimum_color(rb_minimum(rb_right(tree.model)))));
                    assumption();
                } else {
                    assumption();
                }
            }
            match tree.model {
                RbTree::Empty => { contradiction(tree.model == RbTree::Empty); },
                RbTree::Node(identity, parent_model, color, left_model, right_model) => {
                    have rb_left(tree.model) == left_model by {
                        rewrite(tree.model == RbTree::Node(identity, parent_model, color, left_model, right_model));
                        unfold(rb_left(RbTree::Node(identity, parent_model, color, left_model, right_model))); normalize();
                    }
                    have rb_right(tree.model) == right_model by {
                        rewrite(tree.model == RbTree::Node(identity, parent_model, color, left_model, right_model));
                        unfold(rb_right(RbTree::Node(identity, parent_model, color, left_model, right_model))); normalize();
                    }
                    have left_model != RbTree::Empty by { rewrite(left_model == rb_left(tree.model)); assumption(); }
                    have right_model != RbTree::Empty by { rewrite(right_model == rb_right(tree.model)); assumption(); }
                    have not(erase_minimum_child(rb_minimum(right_model)) == RbTree::Empty)
                        or erase_minimum_color(rb_minimum(right_model)) == Color::Red by {
                        rewrite(right_model == rb_right(tree.model)); assumption();
                    }
                    have rb_left(right_model) != RbTree::Empty by { rewrite(right_model == rb_right(tree.model)); assumption(); }
                    apply(erase_context_parent(up.model, identity, parent_model, color, left_model, right_model));
                    apply(ctx_consistent_node_children(up.model, identity, parent_model, color, left_model, right_model, 0));
                    have is_rb(RbTree::Node(identity, parent_model, color, left_model, right_model)) == 1 by {
                        rewrite(RbTree::Node(identity, parent_model, color, left_model, right_model) == tree.model); assumption();
                    }
                    have ctx_rb(up.model, black_height(RbTree::Node(identity, parent_model, color, left_model, right_model)), rb_color(RbTree::Node(identity, parent_model, color, left_model, right_model))) == 1 by {
                        rewrite(RbTree::Node(identity, parent_model, color, left_model, right_model) == tree.model); assumption();
                    }
                    let { left: l, right: r } = unfold(tree);
                    match left_model {
                        RbTree::Empty => { contradiction(left_model == RbTree::Empty); },
                        RbTree::Node(lid, lp, lc, ll, lr) => {
                            let { left: ll_tree, right: lr_tree } = unfold(l);
                            match right_model {
                                RbTree::Empty => { contradiction(right_model == RbTree::Empty); },
                                RbTree::Node(rid, rp, rc, rl, rr) => {
                                    have rl != RbTree::Empty by {
                                        unfold(rb_left(RbTree::Node(rid, rp, rc, rl, rr)));
                                        rewrite(rl == rb_left(RbTree::Node(rid, rp, rc, rl, rr)));
                                        rewrite(RbTree::Node(rid, rp, rc, rl, rr) == right_model); assumption();
                                    }
                                    apply(rb_parent_consistent_node_left(rid, rp, rc, rl, rr, identity));
                                    apply(rb_remove_min_blackened_parent_consistent(rl, rid));
                                    let { left: t, right: right_sibling } = unfold(r);
                                    match rl {
                                        RbTree::Empty => { contradiction(rl == RbTree::Empty); },
                                        RbTree::Node(iid, ip, ic, il, ir) => {
                                            let { left: init_l, right: init_r } = unfold(t);
                                            let t = fold(rb_at(iid), { model: RbTree::Node(iid, ip, ic, il, ir) }, { left: init_l, right: init_r });
                                            step(); step(); step(); step(); step(); step(); step(); step(); step(); step(); step(); step(); step(); step();
                                            let c = fold(erase_spine_at(tmp, child), { model: EraseSpine::Top });
                                            have plug(erase_context(c.model), t.model) == rl by {
                                                rewrite(c.model == EraseSpine::Top);
                                                unfold(erase_context(EraseSpine::Top));
                                                unfold(plug(Context::Top, t.model)); simp();
                                            }
                                            have successor == erase_spine_parent(c.model, child) by {
                                                rewrite(c.model == EraseSpine::Top);
                                                unfold(erase_spine_parent(EraseSpine::Top, child)); simp();
                                            }
                                            loop {
                                                owns c: erase_spine_at(tmp, child);
                                                owns t: rb_at(tmp);
                                                decreases t;
                                                invariant tmp != 0;
                                                invariant successor == erase_spine_parent(c.model, child);
                                                invariant plug(erase_context(c.model), t.model) == rl;
                                                initialize by simp();
                                                preserve by {
                                                    match t.model {
                                                        RbTree::Empty => { unfold(t); have tmp != 0 by { simp(); } contradiction(tmp == 0); },
                                                        RbTree::Node(tid, tp, tc, tl, tr) => {
                                                            have plug(erase_context(EraseSpine::Left(tid, tp, tc, tr, c.model)), tl) == rl by {
                                                                unfold(erase_context(EraseSpine::Left(tid, tp, tc, tr, c.model)));
                                                                unfold(plug(Context::Left(tid, tp, tc, tr, erase_context(c.model)), tl));
                                                                rewrite(RbTree::Node(tid, tp, tc, tl, tr) == t.model); assumption();
                                                            }
                                                            let { left: next, right: sibling } = unfold(t);
                                                            have tmp == tid by assumption();
                                                            have tid != 0 by { rewrite(tid == tmp); assumption(); }
                                                            have erase_spine_parent(EraseSpine::Left(tid, tp, tc, tr, c.model), child) == tid by {
                                                                unfold(erase_spine_parent(EraseSpine::Left(tid, tp, tc, tr, c.model), child)); normalize();
                                                            }
                                                            let frame = fold(erase_spine_at(tmp->rb_left, child),
                                                                { model: EraseSpine::Left(tid, tp, tc, tr, c.model) }, { up: c });
                                                            step(); step(); step();
                                                            if tmp == 0 {
                                                            } else {
                                                                close_invariants();
                                                            }
                                                        },
                                                    }
                                                }
                                            }
                                            match t.model {
                                                RbTree::Node(a, b, col, lt, rt) => {
                                                    have t.model == RbTree::Empty by assumption();
                                                    have t.model != RbTree::Empty by { rewrite(t.model == RbTree::Node(a, b, col, lt, rt)); normalize(); }
                                                    contradiction(t.model == RbTree::Empty);
                                                },
                                                RbTree::Empty => {
                                                    have c.model != EraseSpine::Top by normalize();
                                                    match c.model {
                                                        EraseSpine::Top => { contradiction(c.model == EraseSpine::Top); },
                                                        EraseSpine::Left(mid, mp, mc, mr, mu) => {
                                                            apply(erase_spine_minimum(mu, RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                            have rb_minimum(rl) == RbMinimum::Found(mid, mc, mr) by {
                                                                rewrite(rl == plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                                rewrite(rb_minimum(plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)))
                                                                    == rb_minimum(RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                                unfold(rb_minimum(RbTree::Node(mid, mp, mc, RbTree::Empty, mr))); normalize();
                                                            }
                                                            apply(rb_minimum_nonempty_left(rid, rp, rc, rl, rr));
                                                            have rb_minimum(right_model) == RbMinimum::Found(mid, mc, mr) by {
                                                                rewrite(right_model == RbTree::Node(rid, rp, rc, rl, rr));
                                                                rewrite(rb_minimum(RbTree::Node(rid, rp, rc, rl, rr)) == rb_minimum(rl)); assumption();
                                                            }
                                                            have not(mr == RbTree::Empty) or mc == Color::Red by {
                                                                have erase_minimum_child(rb_minimum(right_model)) == mr by {
                                                                    rewrite(rb_minimum(right_model) == RbMinimum::Found(mid, mc, mr));
                                                                    unfold(erase_minimum_child(RbMinimum::Found(mid, mc, mr))); normalize();
                                                                }
                                                                have erase_minimum_color(rb_minimum(right_model)) == mc by {
                                                                    rewrite(rb_minimum(right_model) == RbMinimum::Found(mid, mc, mr));
                                                                    unfold(erase_minimum_color(RbMinimum::Found(mid, mc, mr))); normalize();
                                                                }
                                                                rewrite(mr == erase_minimum_child(rb_minimum(right_model)));
                                                                rewrite(mc == erase_minimum_color(rb_minimum(right_model))); assumption();
                                                            }
                                                            apply(rb_erase_no_fixup_successor_splice(identity, mid, parent_model, color,
                                                                left_model, right_model, up.model, 0, mc, mr));
                                                            apply(rb_remove_min_blackened_nonempty_left(rid, rp, rc, rl, rr));
                                                            have erase_minimum_identity(rb_minimum(right_model)) == mid by {
                                                                rewrite(rb_minimum(right_model) == RbMinimum::Found(mid, mc, mr));
                                                                unfold(erase_minimum_identity(RbMinimum::Found(mid, mc, mr))); normalize();
                                                            }
                                                            apply(erase_spine_focus_parent_consistent(mu, RbTree::Node(mid, mp, mc, RbTree::Empty, mr), rid));
                                                            apply(erase_parent_consistent_parent_is(RbTree::Node(mid, mp, mc, RbTree::Empty, mr), erase_spine_parent(mu, rid)));
                                                            apply(rb_parent_is_node_parent(mid, mp, mc, RbTree::Empty, mr, erase_spine_parent(mu, rid)));
                                                            apply(erase_spine_remove_min_blackened(mu, RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                            have rb_remove_min_blackened(rl) == plug(erase_context(mu), rb_reparent(rb_recolor(mr, Color::Black), mp)) by {
                                                                rewrite(rl == plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                                rewrite(rb_remove_min_blackened(plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)))
                                                                        == plug(erase_context(mu), rb_remove_min_blackened(RbTree::Node(mid, mp, mc, RbTree::Empty, mr))));
                                                                unfold(rb_remove_min_blackened(RbTree::Node(mid, mp, mc, RbTree::Empty, mr))); normalize();
                                                            }
                                                            let { sibling: min_right, up: path } = unfold(c);
                                                            have (mid->__rb_parent_color & 1) == color_bit(mc) by assumption();
                                                            unfold(t);
                                                            have parent == mp by {
                                                                rewrite(parent == erase_spine_parent(path.model, child));
                                                                rewrite(path.model == mu); rewrite(child == rid);
                                                                rewrite(erase_spine_parent(mu, rid) == mp); normalize();
                                                            }
                                                            mark opened_spine;
                                                            let { frame: link_frame } = open_erase_spine_link(successor, parent, child, { c: path });
                                                            mark moving;
                                                            step(); step(); step(); step();
                                                            apply(packed_parent_word(mid, at(moving, child->__rb_parent_color)));
                                                            have child->__rb_parent_color == address(mid) + (child->__rb_parent_color & 1) by {
                                                                rewrite(child->__rb_parent_color == ((at(moving, child->__rb_parent_color) & 1) | address(mid)));
                                                                assumption();
                                                            }
                                                            have (child->__rb_parent_color & 1) == (at(moving, child->__rb_parent_color) & 1) by {
                                                                rewrite(child->__rb_parent_color == ((at(moving, child->__rb_parent_color) & 1) | address(mid)));
                                                                assumption();
                                                            }
                                                            have node->rb_left == lid;
                                                            observe(erase_callbacks(augment));
                                                            execute_until(statement(54));
                                                            have separate(memory(child->rb_right), memory(mid->__rb_parent_color));
                                                            let moved_left = fold(rb_at(lid), {
                                                                model: RbTree::Node(lid, mid, lc, ll, lr)
                                                            }, { left: ll_tree, right: lr_tree });
                                                            have moved_left.model == rb_reparent(left_model, mid) by {
                                                                rewrite(left_model == RbTree::Node(lid, lp, lc, ll, lr));
                                                                unfold(rb_reparent(RbTree::Node(lid, lp, lc, ll, lr), mid)); normalize();
                                                            }
                                                            have ctx_node_is(up.model, tmp) == 1 by {
                                                                rewrite(tmp == parent_model); assumption();
                                                            }

                                                            have parent->rb_left == child2;
                                                            mark transplant;
                                                            let { after: context } = step(__rb_change_child(node, successor, tmp, root), { before: up });
                                                            have child->rb_right == at(transplant, child->rb_right);
                                                            have child->__rb_parent_color == at(transplant, child->__rb_parent_color) by { normalize() using { child == rid; }; }
                                                            have parent->rb_left == at(transplant, parent->rb_left) by normalize();
                                                            have parent->rb_left == child2 by {
                                                                rewrite(parent->rb_left == at(transplant, parent->rb_left)); assumption();
                                                            }
                                                            have context.model == at(transplant, up.model) by assumption();
                                                            have context.model == old(up.model);
                                                            have mid->__rb_parent_color == at(transplant, mid->__rb_parent_color);
                                                            mark parent_link_changed;
                                                            // Join the replacement link and the successor fields needed
                                                            // by the shared descent-spine and outer-context rebuild.
                                                            match min_right.model ensuring {
                                                                owns moved_link: erase_left_at(parent);
                                                                fact moved_link.model == rb_reparent(rb_recolor(mr, Color::Black), mp);
                                                                fact child->rb_right == at(transplant, child->rb_right);
                                                                fact child->__rb_parent_color == address(mid) + (child->__rb_parent_color & 1);
                                                                fact (child->__rb_parent_color & 1) == color_bit(rc);
                                                                fact child->__rb_parent_color == address(mid) + color_bit(rc);
                                                                fact mid->rb_left == lid;
                                                                fact mid->rb_right == child;
                                                            } {
                                                                RbTree::Empty => {
                                                                    have mr == RbTree::Empty by { rewrite(mr == min_right.model); assumption(); }
                                                                    have mc == Color::Red by {
                                                                        cases {
                                                                            not(mr == RbTree::Empty) => { contradiction(mr == RbTree::Empty); }
                                                                            mc == Color::Red => { assumption(); }
                                                                        }
                                                                    }
                                                                    unfold(min_right);
                                                                    have color_bit(mc) == 0 by { rewrite(mc == Color::Red); unfold(color_bit(Color::Red)); normalize(); }
                                                                    have (successor->__rb_parent_color & 1) == 0 by {
                                                                        rewrite(successor == mid);
                                                                        rewrite(mid->__rb_parent_color == at(transplant, mid->__rb_parent_color));
                                                                        rewrite((at(transplant, mid->__rb_parent_color) & 1) == color_bit(mc));
                                                                        rewrite(color_bit(mc) == 0);
                                                                        normalize();
                                                                    }
                                                                    have child2 == 0;
                                                                    have parent->rb_left == 0;
                                                                    execute_until(statement(62));
                                                                    let moved_child = fold(rb_at(parent->rb_left), { model: RbTree::Empty });
                                                                    have moved_child.model == rb_reparent(rb_recolor(mr, Color::Black), mp) by {
                                                                        rewrite(mr == RbTree::Empty);
                                                                        unfold(rb_recolor(RbTree::Empty, Color::Black));
                                                                        unfold(rb_reparent(RbTree::Empty, mp)); normalize();
                                                                    }
                                                                    have child->rb_right == at(transplant, child->rb_right);
                                                                    have child->__rb_parent_color == at(transplant, child->__rb_parent_color) by {
                                                                        transport(at(parent_link_changed, child->__rb_parent_color) == at(transplant, child->__rb_parent_color), child->__rb_parent_color == at(transplant, child->__rb_parent_color)) using {
                                                                            at(parent_link_changed, child->__rb_parent_color) == at(transplant, child->__rb_parent_color);
                                                                            at(parent_link_changed, successor) == mid;
                                                                            at(parent_link_changed, child) == rid;
                                                                            separate(memory(child->__rb_parent_color), memory(mid->__rb_parent_color));
                                                                            child == rid;
                                                                            tmp == mid;
                                                                        };
                                                                    }
                                                                    have child->__rb_parent_color == address(mid) + (child->__rb_parent_color & 1);
                                                                    have (child->__rb_parent_color & 1) == color_bit(rc);
                                                                    have child->__rb_parent_color == address(mid) + color_bit(rc) by {
                                                                        rewrite(color_bit(rc) == (child->__rb_parent_color & 1)); assumption();
                                                                    }
                                                                    have mid->rb_left == lid;
                                                                    have mid->rb_right == child;
                                                                    let moved_link = fold(erase_left_at(parent), { model: moved_child.model }, { tree: moved_child });
                                                                },
                                                                RbTree::Node(cid, cp, cc, cl, cr) => {
                                                                    have mr == RbTree::Node(cid, cp, cc, cl, cr) by { rewrite(mr == min_right.model); assumption(); }
                                                                    have rb_reparent(rb_recolor(mr, Color::Black), mp) == RbTree::Node(cid, mp, Color::Black, cl, cr) by {
                                                                        rewrite(mr == RbTree::Node(cid, cp, cc, cl, cr));
                                                                        unfold(rb_recolor(RbTree::Node(cid, cp, cc, cl, cr), Color::Black));
                                                                        unfold(rb_reparent(RbTree::Node(cid, cp, Color::Black, cl, cr), mp)); normalize();
                                                                    }
                                                                    let { left: child_left, right: child_right } = unfold(min_right);
                                                                    have child2 == cid;
                                                                    have parent == mp;
                                                                    have parent->rb_left == cid by { rewrite(parent == mp); simp(); }
                                                                    have child_left.model == cl;
                                                                    have child_right.model == cr;
                                                                    have mid->rb_left == lid;
                                                                    have mid->rb_right == child;
                                                                    execute_until(statement(62));
                                                                    have cid->__rb_parent_color == (address(mp) | 1);
                                                                    have aligned(mp, 8);
                                                                    have ((address(mp) | 1) & 1) == 1 by { arithmetic() using { aligned(mp, 8); }; }
                                                                    have (cid->__rb_parent_color & 1) == color_bit(Color::Black) by {
                                                                        unfold(color_bit(Color::Black));
                                                                    }
                                                                    have (address(mp) | 1) == address(mp) + ((address(mp) | 1) & 1) by {
                                                                        arithmetic() using { aligned(mp, 8); };
                                                                    }
                                                                    have cid->__rb_parent_color == address(mp) + (cid->__rb_parent_color & 1) by {
                                                                        rewrite(cid->__rb_parent_color == (address(mp) | 1)); assumption();
                                                                    }

                                                                    have parent->rb_left == cid;
                                                                    let moved_child = fold(rb_at(cid), { model: RbTree::Node(cid, mp, Color::Black, cl, cr) }, { left: child_left, right: child_right });
                                                                    have moved_child.model == rb_reparent(rb_recolor(mr, Color::Black), mp) by {
                                                                        rewrite(rb_reparent(rb_recolor(mr, Color::Black), mp) == RbTree::Node(cid, mp, Color::Black, cl, cr)); normalize();
                                                                    }
                                                                    have child->rb_right == at(transplant, child->rb_right);
                                                                    have child->__rb_parent_color == at(transplant, child->__rb_parent_color) by {
                                                                        transport(at(parent_link_changed, child->__rb_parent_color) == at(transplant, child->__rb_parent_color), child->__rb_parent_color == at(transplant, child->__rb_parent_color)) using {
                                                                            at(parent_link_changed, child->__rb_parent_color) == at(transplant, child->__rb_parent_color);
                                                                            at(parent_link_changed, successor) == mid;
                                                                            at(parent_link_changed, child) == rid;
                                                                            separate(memory(child->__rb_parent_color), memory(mid->__rb_parent_color));
                                                                            child == rid;
                                                                            tmp == mid;
                                                                        };
                                                                    }
                                                                    have child->__rb_parent_color == address(mid) + (child->__rb_parent_color & 1);
                                                                    have (child->__rb_parent_color & 1) == color_bit(rc);
                                                                    have child->__rb_parent_color == address(mid) + color_bit(rc) by {
                                                                        rewrite(color_bit(rc) == (child->__rb_parent_color & 1)); assumption();
                                                                    }
                                                                    have mid->rb_left == lid;
                                                                    have mid->rb_right == child;
                                                                    let moved_link = fold(erase_left_at(parent), { model: moved_child.model }, { tree: moved_child });
                                                                },
                                                            }
                                                            have separate(memory(child->__rb_parent_color), memory(parent->rb_left));
                                                            have child->__rb_parent_color == address(mid) + color_bit(rc);
                                                            mark replacement_joined;
                                                            let { tree: moved_child } = unfold(moved_link);
                                                            have moved_child.model == rb_reparent(rb_recolor(mr, Color::Black), mp);
                                                            mark closing_spine;
                                                            let { c: path2 } = close_erase_spine_link(parent->rb_left, parent, child, { frame: link_frame });
                                                            have path2.model == at(closing_spine, link_frame.model) by assumption();
                                                            have path2.model == mu;
                                                            have rb_parent_consistent(plug(erase_context(path2.model), moved_child.model), child) == 1 by {
                                                                rewrite(path2.model == mu);
                                                                rewrite(moved_child.model == rb_reparent(rb_recolor(mr, Color::Black), mp));
                                                                rewrite(plug(erase_context(mu), rb_reparent(rb_recolor(mr, Color::Black), mp)) == rb_remove_min_blackened(rl));
                                                                rewrite(child == rid); assumption();
                                                            }
                                                            mark rebuilding_spine;
                                                            let { whole: spine_left } = refold_erase_spine(parent->rb_left, child, { c: path2, t: moved_child });
                                                            have at(rebuilding_spine, path2.model) == mu by assumption();
                                                            have spine_left.model == plug(erase_context(at(rebuilding_spine, path2.model)), at(rebuilding_spine, moved_child.model)) by assumption();
                                                            have at(rebuilding_spine, moved_child.model) == rb_reparent(rb_recolor(mr, Color::Black), mp) by assumption();
                                                            let { tree: rebuilt_left } = unfold(spine_left);
                                                            apply(erase_parent_consistent_parent_is(rb_remove_min_blackened(rl), rid));
                                                            have child->rb_left == rid->rb_left;
                                                            have child->rb_right == rid->rb_right;
                                                            have rid->rb_right == at(transplant, rid->rb_right);
                                                            have child->__rb_parent_color == at(replacement_joined, child->__rb_parent_color);
                                                            have child->__rb_parent_color == address(mid) + (child->__rb_parent_color & 1) by {
                                                                rewrite(child->__rb_parent_color == at(replacement_joined, child->__rb_parent_color)); assumption();
                                                            }
                                                            have (child->__rb_parent_color & 1) == color_bit(rc) by {
                                                                rewrite(child->__rb_parent_color == at(replacement_joined, child->__rb_parent_color)); assumption();
                                                            }
                                                            let moved_right = fold(rb_at(child), {
                                                                model: RbTree::Node(rid, mid, rc, rb_remove_min_blackened(rl), rr)
                                                            }, { left: rebuilt_left, right: right_sibling });
                                                            have rb_parent_is(RbTree::Node(lid, mid, lc, ll, lr), mid) == 1 by { unfold(rb_parent_is(RbTree::Node(lid, mid, lc, ll, lr), mid)); normalize(); }
                                                            have rb_parent_is(RbTree::Node(rid, mid, rc, rb_remove_min_blackened(rl), rr), mid) == 1 by { unfold(rb_parent_is(RbTree::Node(rid, mid, rc, rb_remove_min_blackened(rl), rr), mid)); normalize(); }
                                                            let subtree = fold(rb_at(mid), {
                                                                model: RbTree::Node(mid, parent_model, color, RbTree::Node(lid, mid, lc, ll, lr),
                                                                    RbTree::Node(rid, mid, rc, rb_remove_min_blackened(rl), rr))
                                                            }, { left: moved_left, right: moved_right });
                                                            have subtree.model == rb_successor_child_splice(mid, parent_model, color, left_model, right_model) by {
                                                                unfold(rb_successor_child_splice(mid, parent_model, color, left_model, right_model));
                                                                rewrite(left_model == RbTree::Node(lid, lp, lc, ll, lr));
                                                                rewrite(right_model == RbTree::Node(rid, rp, rc, rl, rr));
                                                                rewrite(rb_remove_min_blackened(RbTree::Node(rid, rp, rc, rl, rr)) == RbTree::Node(rid, rp, rc, rb_remove_min_blackened(rl), rr));
                                                                unfold(rb_reparent(RbTree::Node(lid, lp, lc, ll, lr), mid));
                                                                unfold(rb_reparent(RbTree::Node(rid, rp, rc, rb_remove_min_blackened(rl), rr), mid));
                                                                normalize();
                                                            }
                                                            have subtree.model == erase_child_deep_model(old(tree.model)) by {
                                                                rewrite(old(tree.model) == RbTree::Node(identity, parent_model, color, left_model, right_model));
                                                                unfold(erase_child_deep_model(RbTree::Node(identity, parent_model, color, left_model, right_model)));
                                                                rewrite(erase_minimum_identity(rb_minimum(right_model)) == mid); assumption();
                                                            }
                                                            have is_rb_root(plug(context.model, subtree.model)) == 1 by {
                                                                rewrite(context.model == old(up.model));
                                                                rewrite(subtree.model == rb_successor_child_splice(mid, parent_model, color, left_model, right_model)); assumption();
                                                            }
                                                            apply(plug_parent_consistent_transport(context.model, subtree.model, 0));
                                                            have rb_tree_parent_consistent(plug(context.model, subtree.model)) == 1 by {
                                                                unfold(rb_tree_parent_consistent(plug(context.model, subtree.model))); assumption();
                                                            }
                                                            have plug(context.model, subtree.model) == plug(old(up.model), erase_child_deep_model(old(tree.model))) by {
                                                                rewrite(context.model == old(up.model));
                                                                rewrite(subtree.model == erase_child_deep_model(old(tree.model))); normalize();
                                                            }
                                                            have rb_inorder(erase_child_deep_model(old(tree.model))) == list::append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model)))) by {
                                                                rewrite(erase_child_deep_model(old(tree.model)) == subtree.model); assumption();
                                                            }
                                                            mark closing_root;
                                                            let { whole: deep_whole } = refold_to_root(mid, root, { c: context, t: subtree });
                                                            have deep_whole.model == plug(old(up.model), erase_child_deep_model(old(tree.model))) by {
                                                                rewrite(deep_whole.model == plug(at(closing_root, context.model),
                                                                    RbTree::Node(mid, parent_model, color, RbTree::Node(lid, mid, lc, ll, lr),
                                                                        RbTree::Node(rid, mid, rc, rb_remove_min_blackened(rl), rr))));
                                                                assumption();
                                                            }
                                                            have is_rb_root(deep_whole.model) == 1 by {
                                                                rewrite(deep_whole.model == plug(at(closing_root, context.model),
                                                                    RbTree::Node(mid, parent_model, color, RbTree::Node(lid, mid, lc, ll, lr),
                                                                        RbTree::Node(rid, mid, rc, rb_remove_min_blackened(rl), rr)))); assumption();
                                                            }
                                                            observe(erase_callbacks(augment));
                                                            execute();
                                                            apply(erase_deep_no_fixup(old(tree.model), old(up.model), mid, mc, mr));
                                                            apply(erase_outcome_deep(identity, parent_model, color, lid, lp, lc, ll, lr, rid, rp, rc, iid, ip, ic, il, ir, rr, old(up.model)));
                                                            have old(tree.model) == RbTree::Node(identity, parent_model, color, RbTree::Node(lid, lp, lc, ll, lr), RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)) by {
                                                                rewrite(old(tree.model) == RbTree::Node(identity, parent_model, color, left_model, right_model));
                                                                rewrite(left_model == RbTree::Node(lid, lp, lc, ll, lr));
                                                                rewrite(right_model == RbTree::Node(rid, rp, rc, rl, rr));
                                                                rewrite(rl == RbTree::Node(iid, ip, ic, il, ir)); normalize();
                                                            }
                                                            have rb_minimum(RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)) == RbMinimum::Found(mid, mc, mr) by {
                                                                rewrite(RbTree::Node(iid, ip, ic, il, ir) == rl);
                                                                rewrite(RbTree::Node(rid, rp, rc, rl, rr) == right_model); assumption();
                                                            }
                                                            have erase_outcome(old(tree.model), old(up.model)) == EraseOutcome::Balanced(plug(old(up.model), erase_child_deep_model(old(tree.model)))) by {
                                                                rewrite(old(tree.model) == RbTree::Node(identity, parent_model, color, RbTree::Node(lid, lp, lc, ll, lr), RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)));
                                                                rewrite(erase_outcome(RbTree::Node(identity, parent_model, color, RbTree::Node(lid, lp, lc, ll, lr), RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)), old(up.model)) == erase_deep_outcome(RbTree::Node(identity, parent_model, color, RbTree::Node(lid, lp, lc, ll, lr), RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)), old(up.model), rb_minimum(RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr))));
                                                                rewrite(rb_minimum(RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)) == RbMinimum::Found(mid, mc, mr));
                                                                rewrite(RbTree::Node(identity, parent_model, color, RbTree::Node(lid, lp, lc, ll, lr), RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)) == old(tree.model)); assumption();
                                                            }
                                                            have erase_splice(old(tree.model)) == erase_child_deep_model(old(tree.model)) by {
                                                                rewrite(old(tree.model) == RbTree::Node(identity, parent_model, color, RbTree::Node(lid, lp, lc, ll, lr), RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)));
                                                                rewrite(erase_splice(RbTree::Node(identity, parent_model, color, RbTree::Node(lid, lp, lc, ll, lr), RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr))) == erase_deep_splice(RbTree::Node(identity, parent_model, color, RbTree::Node(lid, lp, lc, ll, lr), RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)), rb_minimum(RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr))));
                                                                rewrite(rb_minimum(RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)) == RbMinimum::Found(mid, mc, mr));
                                                                rewrite(RbTree::Node(identity, parent_model, color, RbTree::Node(lid, lp, lc, ll, lr), RbTree::Node(rid, rp, rc, RbTree::Node(iid, ip, ic, il, ir), rr)) == old(tree.model)); assumption();
                                                            }
                                                            have rb_inorder(erase_splice(old(tree.model))) == list::append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model)))) by {
                                                                rewrite(erase_splice(old(tree.model)) == erase_child_deep_model(old(tree.model))); assumption();
                                                            }
                                                            have rb_tree_parent_consistent(plug(old(up.model), erase_child_deep_model(old(tree.model)))) == 1 by {
                                                            unfold(rb_tree_parent_consistent(plug(old(up.model), erase_child_deep_model(old(tree.model))))); rewrite(plug(old(up.model), erase_child_deep_model(old(tree.model))) == deep_whole.model); assumption();
                                                            }
                                                            have is_rb_root(plug(old(up.model), erase_child_deep_model(old(tree.model)))) == 1 by { rewrite(plug(old(up.model), erase_child_deep_model(old(tree.model))) == deep_whole.model); assumption(); }
                                                            let out = fold(erase_out(root, result), { model: EraseOutcome::Balanced(plug(old(up.model), erase_child_deep_model(old(tree.model)))) }, { whole: deep_whole });
                                                            have erase_out_rb(out.model) == 1 by {
                                                            rewrite(out.model == EraseOutcome::Balanced(plug(old(up.model), erase_child_deep_model(old(tree.model)))));
                                                            unfold(erase_out_rb(EraseOutcome::Balanced(plug(old(up.model), erase_child_deep_model(old(tree.model)))))); assumption();
                                                            }
                                                            have erase_out_tree(out.model) == plug(old(up.model), erase_child_deep_model(old(tree.model))) by {
                                                            rewrite(out.model == EraseOutcome::Balanced(plug(old(up.model), erase_child_deep_model(old(tree.model)))));
                                                            unfold(erase_out_tree(EraseOutcome::Balanced(plug(old(up.model), erase_child_deep_model(old(tree.model)))))); normalize();
                                                            }
                                                            have rb_tree_parent_consistent(erase_out_tree(out.model)) == 1 by {
                                                            rewrite(erase_out_tree(out.model) == plug(old(up.model), erase_child_deep_model(old(tree.model)))); assumption();
                                                            }
                                                            have out.model == erase_outcome(old(tree.model), old(up.model)) by {
                                                            rewrite(erase_outcome(old(tree.model), old(up.model)) == EraseOutcome::Balanced(plug(old(up.model), erase_child_deep_model(old(tree.model))))); rewrite(out.model == EraseOutcome::Balanced(plug(old(up.model), erase_child_deep_model(old(tree.model))))); normalize();
                                                            }
                                                            have erase_out_tree(out.model) == plug(old(up.model), erase_splice(old(tree.model))) by {
                                                            rewrite(erase_splice(old(tree.model)) == erase_child_deep_model(old(tree.model))); assumption();
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
                },
            }
        }
    } else {
    match tree.model {
        RbTree::Empty => { contradiction(tree.model == RbTree::Empty); },
        RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right) => {
            match erased_left {
                RbTree::Empty => {
                    match erased_right {
                        RbTree::Empty => {
                            // Leaf: unlink it. A black leaf below the root leaves a deficit at its parent.
                            have rb_left(old(tree.model)) == RbTree::Empty by auto();
                            have rb_right(old(tree.model)) == RbTree::Empty by auto();
                            have erase_outcome(old(tree.model), old(up.model)) == erase_leaf_outcome(erased_color, old(up.model)) by auto();
                            have erase_splice(old(tree.model)) == RbTree::Empty by auto();
                            have rb_inorder(erase_splice(old(tree.model))) == list::append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model)))) by {
                                rewrite(erase_splice(old(tree.model)) == RbTree::Empty);
                                rewrite(rb_left(old(tree.model)) == RbTree::Empty); rewrite(rb_right(old(tree.model)) == RbTree::Empty);
                                unfold(rb_inorder(RbTree::Empty));
                                unfold(list::append(List<struct rb_node*>::Nil, List<struct rb_node*>::Nil)); normalize();
                            }
                            apply(rb_parent_consistent_empty(erased_parent));
                            apply(ctx_consistent_swap(up.model, erased, erased_parent, erased_color, erased_left, erased_right, RbTree::Empty, 0));
                            let { left: l, right: r } = unfold(tree);
                            unfold(l); unfold(r);
                            have rb_color(old(tree.model)) == erased_color by {
                                rewrite(old(tree.model) == RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right));
                                unfold(rb_color(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right))); normalize();
                            }
                            apply(erase_context_parent(up.model, erased, erased_parent, erased_color, erased_left, erased_right));
                            apply(plug_parent_consistent_transport(old(up.model), RbTree::Empty, 0));
                            have rb_tree_parent_consistent(plug(old(up.model), RbTree::Empty)) == 1 by {
                                unfold(rb_tree_parent_consistent(plug(old(up.model), RbTree::Empty))); assumption();
                            }
                            match erased_color {
                                Color::Black => {
                                    have black_height(old(tree.model)) == Nat::Succ(Nat::Zero) by {
                                        rewrite(old(tree.model) == RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right));
                                        rewrite(erased_color == Color::Black); rewrite(erased_left == RbTree::Empty);
                                        unfold(black_height(RbTree::Node(erased, erased_parent, Color::Black, RbTree::Empty, erased_right)));
                                        unfold(black_height(RbTree::Empty)); normalize();
                                    }
                                    have ctx_rb(old(up.model), Nat::Succ(Nat::Zero), Color::Black) == 1 by {
                                        rewrite(Nat::Succ(Nat::Zero) == black_height(old(tree.model)));
                                        rewrite(Color::Black == erased_color);
                                        rewrite(erased_color == rb_color(old(tree.model))); assumption();
                                    }
                                    have (node->__rb_parent_color & 1) == 1 by {
                                        rewrite((node->__rb_parent_color & 1) == color_bit(erased_color));
                                        rewrite(erased_color == Color::Black); unfold(color_bit(Color::Black)); normalize();
                                    }
                                    execute_until(statement(10));
                                    have parent == erased_parent;
                                    let { after: remaining } = step(__rb_change_child(node, child, parent, root), { before: up });
                                    have remaining.model == old(up.model);
                                    match remaining.model {
                                        Context::Top => {
                                            have ctx_node_is(Context::Top, erased_parent) == 1 by {
                                                rewrite(Context::Top == remaining.model); rewrite(remaining.model == old(up.model)); assumption();
                                            }
                                            have erased_parent == 0 by auto();
                                            have old(up.model) == Context::Top by { rewrite(old(up.model) == remaining.model); assumption(); }
                                            have is_rb_root(RbTree::Empty) == 1 by {
                                                unfold(is_rb_root(RbTree::Empty)); unfold(is_rb(RbTree::Empty)); unfold(rb_root_black(RbTree::Empty)); normalize();
                                            }
                                            have plug(old(up.model), RbTree::Empty) == RbTree::Empty by {
                                                rewrite(old(up.model) == Context::Top); unfold(plug(Context::Top, RbTree::Empty)); normalize();
                                            }
                                            have rb_tree_parent_consistent(RbTree::Empty) == 1 by {
                                                rewrite(RbTree::Empty == plug(old(up.model), RbTree::Empty)); assumption();
                                            }
                                            have erase_leaf_outcome(erased_color, old(up.model)) == EraseOutcome::Balanced(RbTree::Empty) by {
                                                rewrite(erased_color == Color::Black); rewrite(old(up.model) == Context::Top);
                                                unfold(erase_leaf_outcome(Color::Black, Context::Top)); normalize();
                                            }
                                            unfold(remaining);
                                            open(erase_callbacks(augment)) { execute(); }
                                            let hole = fold(rb_at(0), { model: RbTree::Empty });
                                            let whole = fold(rb_root_at(root), { model: RbTree::Empty }, { tree: hole });
                                            have result == 0;
                                            let out = fold(erase_out(root, result), { model: EraseOutcome::Balanced(RbTree::Empty) }, { whole: whole });
                                            have erase_out_rb(out.model) == 1 by {
                                                rewrite(out.model == EraseOutcome::Balanced(RbTree::Empty));
                                                unfold(erase_out_rb(EraseOutcome::Balanced(RbTree::Empty))); assumption();
                                            }
                                            have erase_out_tree(out.model) == RbTree::Empty by {
                                                rewrite(out.model == EraseOutcome::Balanced(RbTree::Empty));
                                                unfold(erase_out_tree(EraseOutcome::Balanced(RbTree::Empty))); normalize();
                                            }
                                            have out.model == erase_outcome(old(tree.model), old(up.model)) by {
                                                rewrite(out.model == EraseOutcome::Balanced(RbTree::Empty));
                                                rewrite(erase_outcome(old(tree.model), old(up.model)) == erase_leaf_outcome(erased_color, old(up.model)));
                                                rewrite(erase_leaf_outcome(erased_color, old(up.model)) == EraseOutcome::Balanced(RbTree::Empty));
                                                normalize();
                                            }
                                            have rb_tree_parent_consistent(erase_out_tree(out.model)) == 1 by {
                                                rewrite(out.model == EraseOutcome::Balanced(RbTree::Empty));
                                                unfold(erase_out_tree(EraseOutcome::Balanced(RbTree::Empty)));
                                                assumption();
                                            }
                                            have erase_out_tree(out.model) == plug(old(up.model), erase_splice(old(tree.model))) by {
                                                rewrite(out.model == EraseOutcome::Balanced(RbTree::Empty));
                                                unfold(erase_out_tree(EraseOutcome::Balanced(RbTree::Empty)));
                                                rewrite(erase_splice(old(tree.model)) == RbTree::Empty);
                                                rewrite(plug(old(up.model), RbTree::Empty) == RbTree::Empty);
                                                normalize();
                                            }
                                            simp();
                                        },
                                        Context::Left(pid, gp, pc_model, sibling_model, above_model) => {
                                            have Context::Left(pid, gp, pc_model, sibling_model, above_model) == old(up.model) by {
                                                rewrite(Context::Left(pid, gp, pc_model, sibling_model, above_model) == remaining.model); assumption();
                                            }
                                            have ctx_node_is(Context::Left(pid, gp, pc_model, sibling_model, above_model), erased_parent) == 1 by {
                                                rewrite(Context::Left(pid, gp, pc_model, sibling_model, above_model) == old(up.model)); assumption();
                                            }
                                            have erased_parent == pid by auto();
                                            have erase_leaf_outcome(erased_color, old(up.model)) == EraseOutcome::Deficit(old(up.model)) by {
                                                rewrite(erased_color == Color::Black);
                                                rewrite(old(up.model) == Context::Left(pid, gp, pc_model, sibling_model, above_model));
                                                unfold(erase_leaf_outcome(Color::Black, Context::Left(pid, gp, pc_model, sibling_model, above_model))); normalize();
                                            }
                                            let { sibling: sibling, up: above } = unfold(remaining);
                                            have erased_parent != 0;
                                            let remaining = fold(ctx_at(0, root), { model: Context::Left(pid, gp, pc_model, sibling_model, above_model) }, { up: above });
                                            have remaining.model == old(up.model) by { rewrite(remaining.model == Context::Left(pid, gp, pc_model, sibling_model, above_model)); assumption(); }
                                            have remaining.model != Context::Top by { rewrite(remaining.model == Context::Left(pid, gp, pc_model, sibling_model, above_model)); normalize(); }
                                            open(erase_callbacks(augment)) { execute(); }
                                            have result != 0;
                                            have ctx_node_is(old(up.model), result) == 1 by { rewrite(result == erased_parent); assumption(); }
                                            have old(up.model) != Context::Top by { rewrite(old(up.model) == remaining.model); assumption(); }
                                            let out = fold(erase_out(root, result), { model: EraseOutcome::Deficit(old(up.model)) }, { deficit: remaining });
                                            have erase_out_rb(out.model) == 1 by {
                                                rewrite(out.model == EraseOutcome::Deficit(old(up.model)));
                                                unfold(erase_out_rb(EraseOutcome::Deficit(old(up.model)))); assumption();
                                            }
                                            have erase_out_tree(out.model) == plug(old(up.model), RbTree::Empty) by {
                                                rewrite(out.model == EraseOutcome::Deficit(old(up.model)));
                                                unfold(erase_out_tree(EraseOutcome::Deficit(old(up.model)))); normalize();
                                            }
                                            have out.model == erase_outcome(old(tree.model), old(up.model)) by {
                                                rewrite(out.model == EraseOutcome::Deficit(old(up.model)));
                                                rewrite(erase_outcome(old(tree.model), old(up.model)) == erase_leaf_outcome(erased_color, old(up.model)));
                                                rewrite(erase_leaf_outcome(erased_color, old(up.model)) == EraseOutcome::Deficit(old(up.model)));
                                                normalize();
                                            }
                                            have rb_tree_parent_consistent(erase_out_tree(out.model)) == 1 by {
                                                rewrite(out.model == EraseOutcome::Deficit(old(up.model)));
                                                unfold(erase_out_tree(EraseOutcome::Deficit(old(up.model))));
                                                assumption();
                                            }
                                            have erase_out_tree(out.model) == plug(old(up.model), erase_splice(old(tree.model))) by {
                                                rewrite(out.model == EraseOutcome::Deficit(old(up.model)));
                                                unfold(erase_out_tree(EraseOutcome::Deficit(old(up.model))));
                                                rewrite(erase_splice(old(tree.model)) == RbTree::Empty);
                                                normalize();
                                            }
                                            simp();
                                        },
                                        Context::Right(pid, gp, pc_model, sibling_model, above_model) => {
                                            have Context::Right(pid, gp, pc_model, sibling_model, above_model) == old(up.model) by {
                                                rewrite(Context::Right(pid, gp, pc_model, sibling_model, above_model) == remaining.model); assumption();
                                            }
                                            have ctx_node_is(Context::Right(pid, gp, pc_model, sibling_model, above_model), erased_parent) == 1 by {
                                                rewrite(Context::Right(pid, gp, pc_model, sibling_model, above_model) == old(up.model)); assumption();
                                            }
                                            have erased_parent == pid by auto();
                                            have erase_leaf_outcome(erased_color, old(up.model)) == EraseOutcome::Deficit(old(up.model)) by {
                                                rewrite(erased_color == Color::Black);
                                                rewrite(old(up.model) == Context::Right(pid, gp, pc_model, sibling_model, above_model));
                                                unfold(erase_leaf_outcome(Color::Black, Context::Right(pid, gp, pc_model, sibling_model, above_model))); normalize();
                                            }
                                            let { sibling: sibling, up: above } = unfold(remaining);
                                            let remaining = fold(ctx_at(0, root), { model: Context::Right(pid, gp, pc_model, sibling_model, above_model) }, { up: above });
                                            have remaining.model == old(up.model) by { rewrite(remaining.model == Context::Right(pid, gp, pc_model, sibling_model, above_model)); assumption(); }
                                            have remaining.model != Context::Top by { rewrite(remaining.model == Context::Right(pid, gp, pc_model, sibling_model, above_model)); normalize(); }
                                            open(erase_callbacks(augment)) { execute(); }
                                            have ctx_node_is(old(up.model), result) == 1 by { rewrite(result == erased_parent); assumption(); }
                                            have old(up.model) != Context::Top by { rewrite(old(up.model) == remaining.model); assumption(); }
                                            let out = fold(erase_out(root, result), { model: EraseOutcome::Deficit(old(up.model)) }, { deficit: remaining });
                                            have erase_out_rb(out.model) == 1 by {
                                                rewrite(out.model == EraseOutcome::Deficit(old(up.model)));
                                                unfold(erase_out_rb(EraseOutcome::Deficit(old(up.model)))); assumption();
                                            }
                                            have erase_out_tree(out.model) == plug(old(up.model), RbTree::Empty) by {
                                                rewrite(out.model == EraseOutcome::Deficit(old(up.model)));
                                                unfold(erase_out_tree(EraseOutcome::Deficit(old(up.model)))); normalize();
                                            }
                                            have out.model == erase_outcome(old(tree.model), old(up.model)) by {
                                                rewrite(out.model == EraseOutcome::Deficit(old(up.model)));
                                                rewrite(erase_outcome(old(tree.model), old(up.model)) == erase_leaf_outcome(erased_color, old(up.model)));
                                                rewrite(erase_leaf_outcome(erased_color, old(up.model)) == EraseOutcome::Deficit(old(up.model)));
                                                normalize();
                                            }
                                            have rb_tree_parent_consistent(erase_out_tree(out.model)) == 1 by {
                                                rewrite(out.model == EraseOutcome::Deficit(old(up.model)));
                                                unfold(erase_out_tree(EraseOutcome::Deficit(old(up.model))));
                                                assumption();
                                            }
                                            have erase_out_tree(out.model) == plug(old(up.model), erase_splice(old(tree.model))) by {
                                                rewrite(out.model == EraseOutcome::Deficit(old(up.model)));
                                                unfold(erase_out_tree(EraseOutcome::Deficit(old(up.model))));
                                                rewrite(erase_splice(old(tree.model)) == RbTree::Empty);
                                                normalize();
                                            }
                                            simp();
                                        },
                                    }
                                },
                                Color::Red => {
                                    have black_height(old(tree.model)) == Nat::Zero by {
                                        rewrite(old(tree.model) == RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right));
                                        rewrite(erased_color == Color::Red); rewrite(erased_left == RbTree::Empty);
                                        unfold(black_height(RbTree::Node(erased, erased_parent, Color::Red, RbTree::Empty, erased_right)));
                                        unfold(black_height(RbTree::Empty)); normalize();
                                    }
                                    have ctx_rb(old(up.model), Nat::Zero, Color::Red) == 1 by {
                                        rewrite(Nat::Zero == black_height(old(tree.model)));
                                        rewrite(Color::Red == erased_color);
                                        rewrite(erased_color == rb_color(old(tree.model))); assumption();
                                    }
                                    have erase_leaf_outcome(erased_color, old(up.model)) == EraseOutcome::Balanced(plug(old(up.model), RbTree::Empty)) by {
                                        rewrite(erased_color == Color::Red);
                                        unfold(erase_leaf_outcome(Color::Red, old(up.model))); normalize();
                                    }
                                    have (node->__rb_parent_color & 1) == 0 by {
                                        rewrite((node->__rb_parent_color & 1) == color_bit(erased_color));
                                        rewrite(erased_color == Color::Red); unfold(color_bit(Color::Red)); normalize();
                                    }
                                    execute_until(statement(10));
                                    let { after: remaining } = step(__rb_change_child(node, child, parent, root), { before: up });
                                    apply(ctx_rb_black_focus(old(up.model), Nat::Zero, Color::Red));
                                    have ctx_rb(old(up.model), black_height(RbTree::Empty), rb_color(RbTree::Empty)) == 1 by {
                                        unfold(black_height(RbTree::Empty)); unfold(rb_color(RbTree::Empty)); assumption();
                                    }
                                    apply(plug_rb_from_ctx_rb(old(up.model), RbTree::Empty));
                                    let hole = fold(rb_at(0), { model: RbTree::Empty });
                                    have rb_tree_parent_consistent(plug(remaining.model, hole.model)) == 1 by {
                                        rewrite(remaining.model == old(up.model)); rewrite(hole.model == RbTree::Empty); assumption();
                                    }
                                    have plug(remaining.model, hole.model) == plug(old(up.model), RbTree::Empty) by {
                                        rewrite(remaining.model == old(up.model)); rewrite(hole.model == RbTree::Empty); normalize();
                                    }
                                    mark balanced;
                                    let { whole: whole } = refold_to_root(0, root, { c: remaining, t: hole });
                                    have whole.model == plug(old(up.model), RbTree::Empty) by {
                                        rewrite(whole.model == plug(at(balanced, remaining.model), RbTree::Empty));
                                        rewrite(at(balanced, remaining.model) == old(up.model)); normalize();
                                    }
                                    open(erase_callbacks(augment)) { execute(); }
                                    let out = fold(erase_out(root, result), { model: EraseOutcome::Balanced(plug(old(up.model), RbTree::Empty)) }, { whole: whole });
                                    have erase_out_rb(out.model) == 1 by {
                                        rewrite(out.model == EraseOutcome::Balanced(plug(old(up.model), RbTree::Empty)));
                                        unfold(erase_out_rb(EraseOutcome::Balanced(plug(old(up.model), RbTree::Empty)))); assumption();
                                    }
                                    have erase_out_tree(out.model) == plug(old(up.model), RbTree::Empty) by {
                                        rewrite(out.model == EraseOutcome::Balanced(plug(old(up.model), RbTree::Empty)));
                                        unfold(erase_out_tree(EraseOutcome::Balanced(plug(old(up.model), RbTree::Empty)))); normalize();
                                    }
                                    have out.model == erase_outcome(old(tree.model), old(up.model)) by {
                                        rewrite(out.model == EraseOutcome::Balanced(plug(old(up.model), RbTree::Empty)));
                                        rewrite(erase_outcome(old(tree.model), old(up.model)) == erase_leaf_outcome(erased_color, old(up.model)));
                                        rewrite(erase_leaf_outcome(erased_color, old(up.model)) == EraseOutcome::Balanced(plug(old(up.model), RbTree::Empty)));
                                        normalize();
                                    }
                                    have rb_tree_parent_consistent(erase_out_tree(out.model)) == 1 by {
                                        rewrite(out.model == EraseOutcome::Balanced(plug(old(up.model), RbTree::Empty)));
                                        unfold(erase_out_tree(EraseOutcome::Balanced(plug(old(up.model), RbTree::Empty))));
                                        assumption();
                                    }
                                    have erase_out_tree(out.model) == plug(old(up.model), erase_splice(old(tree.model))) by {
                                        rewrite(out.model == EraseOutcome::Balanced(plug(old(up.model), RbTree::Empty)));
                                        unfold(erase_out_tree(EraseOutcome::Balanced(plug(old(up.model), RbTree::Empty))));
                                        rewrite(erase_splice(old(tree.model)) == RbTree::Empty);
                                        normalize();
                                    }
                                    simp();
                                },
                            }
                        },
                        RbTree::Node(er_id, er_parent, er_color, er_left, er_right) => {
                            // Only a right child: the black erased node's red child takes its parent
                            // word and becomes black, so no repair is needed.
                            have rb_left(old(tree.model)) == RbTree::Empty by auto();
                            have rb_right(old(tree.model)) == erased_right by auto();
                            have erase_outcome(old(tree.model), old(up.model)) == EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model)))) by auto();
                            have erase_splice(old(tree.model)) == rb_erase_one_child_model(old(tree.model)) by auto();
                            have erased_right != RbTree::Empty by auto();
                            have ctx_rb(up.model, black_height(RbTree::Node(erased, erased_parent, erased_color, RbTree::Empty, erased_right)),
                                rb_color(RbTree::Node(erased, erased_parent, erased_color, RbTree::Empty, erased_right))) == 1 by {
                                rewrite(RbTree::Empty == erased_left);
                                rewrite(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right) == tree.model); assumption();
                            }
                            apply(rb_erase_only_right_child(erased, erased_parent, erased_color, erased_right, up.model));
                            apply(ctx_consistent_node_children(up.model, erased, erased_parent, erased_color, erased_left, erased_right, 0));
                            apply(rb_erase_child_keeps_parents(up.model, erased, erased_parent, erased_color, erased_left, erased_right, erased_right));
                            apply(erase_context_parent(up.model, erased, erased_parent, erased_color, erased_left, erased_right));
                            apply(plug_parent_consistent_transport(up.model, rb_reparent(rb_recolor(erased_right, Color::Black), erased_parent), 0));
                            have rb_tree_parent_consistent(plug(old(up.model), rb_reparent(rb_recolor(erased_right, Color::Black), erased_parent))) == 1 by {
                                unfold(rb_tree_parent_consistent(plug(old(up.model), rb_reparent(rb_recolor(erased_right, Color::Black), erased_parent))));
                            }
                            have rb_reparent(rb_recolor(erased_right, Color::Black), erased_parent)
                                == RbTree::Node(er_id, erased_parent, Color::Black, er_left, er_right) by {
                                rewrite(erased_right == RbTree::Node(er_id, er_parent, er_color, er_left, er_right));
                                unfold(rb_recolor(RbTree::Node(er_id, er_parent, er_color, er_left, er_right), Color::Black));
                                unfold(rb_reparent(RbTree::Node(er_id, er_parent, Color::Black, er_left, er_right), erased_parent)); normalize();
                            }
                            have rb_erase_one_child_model(old(tree.model)) == rb_reparent(rb_recolor(erased_right, Color::Black), erased_parent) by {
                                rewrite(old(tree.model) == RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right));
                                unfold(rb_erase_one_child_model(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right)));
                                rewrite(erased_left == RbTree::Empty);
                                unfold(rb_erase_root_child(RbTree::Node(erased, erased_parent, erased_color, RbTree::Empty, erased_right))); normalize();
                            }
                            have rb_inorder(erase_splice(old(tree.model))) == list::append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model)))) by {
                                rewrite(erase_splice(old(tree.model)) == rb_erase_one_child_model(old(tree.model)));
                                rewrite(rb_erase_one_child_model(old(tree.model)) == rb_reparent(rb_recolor(erased_right, Color::Black), erased_parent));
                                rewrite(rb_inorder(rb_reparent(rb_recolor(erased_right, Color::Black), erased_parent)) == rb_inorder(erased_right));
                                rewrite(rb_left(old(tree.model)) == RbTree::Empty); rewrite(rb_right(old(tree.model)) == erased_right);
                                unfold(rb_inorder(RbTree::Empty));
                                unfold(list::append(List<struct rb_node*>::Nil, rb_inorder(erased_right))); normalize();
                            }
                            let { left: l, right: r } = unfold(tree);
                            unfold(l);
                            let { left: child_left, right: child_right } = unfold(r);
                            have (node->__rb_parent_color & 1) == 1 by {
                                rewrite((node->__rb_parent_color & 1) == color_bit(erased_color));
                                rewrite(erased_color == Color::Black); unfold(color_bit(Color::Black)); normalize();
                            }
                            have (old(node->__rb_parent_color) & 1) == 1 by { rewrite(old(node->__rb_parent_color) == node->__rb_parent_color); assumption(); }
                            execute_until(statement(10));
                            let { after: remaining } = step(__rb_change_child(node, child, parent, root), { before: up });
                            open(erase_callbacks(augment)) { execute_until(statement(15)); }
                            have er_id->__rb_parent_color == pc;
                            have pc == old(node->__rb_parent_color);
                            have (pc & 1) == color_bit(Color::Black) by {
                                rewrite(pc == old(node->__rb_parent_color)); unfold(color_bit(Color::Black)); assumption();
                            }
                            let replacement = fold(rb_at(er_id), {
                                model: RbTree::Node(er_id, erased_parent, Color::Black, er_left, er_right)
                            }, { left: child_left, right: child_right });
                            have rb_tree_parent_consistent(plug(remaining.model, replacement.model)) == 1 by {
                                rewrite(remaining.model == old(up.model));
                                rewrite(replacement.model == rb_reparent(rb_recolor(erased_right, Color::Black), erased_parent));
                                unfold(rb_tree_parent_consistent(plug(old(up.model), rb_reparent(rb_recolor(erased_right, Color::Black), erased_parent))));
                                assumption();
                            }
                            mark balanced;
                            let { whole: whole } = refold_to_root(er_id, root, { c: remaining, t: replacement });
                            have whole.model == plug(old(up.model), rb_erase_one_child_model(old(tree.model))) by {
                                rewrite(whole.model == plug(at(balanced, remaining.model), RbTree::Node(er_id, erased_parent, Color::Black, er_left, er_right)));
                                rewrite(at(balanced, remaining.model) == old(up.model));
                                rewrite(rb_erase_one_child_model(old(tree.model)) == rb_reparent(rb_recolor(erased_right, Color::Black), erased_parent));
                                rewrite(rb_reparent(rb_recolor(erased_right, Color::Black), erased_parent) == RbTree::Node(er_id, erased_parent, Color::Black, er_left, er_right));
                                normalize();
                            }
                            open(erase_callbacks(augment)) { execute(); }
                            let out = fold(erase_out(root, result), { model: EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model)))) }, { whole: whole });
                            have erase_out_rb(out.model) == 1 by {
                                rewrite(out.model == EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model)))));
                                unfold(erase_out_rb(EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model))))));
                                rewrite(rb_erase_one_child_model(old(tree.model)) == rb_reparent(rb_recolor(erased_right, Color::Black), erased_parent));
                                assumption();
                            }
                            have erase_out_tree(out.model) == plug(old(up.model), rb_erase_one_child_model(old(tree.model))) by {
                                rewrite(out.model == EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model)))));
                                unfold(erase_out_tree(EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model)))))); normalize();
                            }
                            have out.model == erase_outcome(old(tree.model), old(up.model)) by {
                                rewrite(out.model == EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model)))));
                                rewrite(erase_outcome(old(tree.model), old(up.model)) == EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model)))));
                                normalize();
                            }
                            have rb_tree_parent_consistent(erase_out_tree(out.model)) == 1 by {
                                rewrite(out.model == EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model)))));
                                unfold(erase_out_tree(EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model))))));
                                rewrite(rb_erase_one_child_model(old(tree.model)) == rb_reparent(rb_recolor(erased_right, Color::Black), erased_parent));
                                assumption();
                            }
                            have erase_out_tree(out.model) == plug(old(up.model), erase_splice(old(tree.model))) by {
                                rewrite(out.model == EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model)))));
                                unfold(erase_out_tree(EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model))))));
                                rewrite(erase_splice(old(tree.model)) == rb_erase_one_child_model(old(tree.model)));
                                normalize();
                            }
                            simp();
                        },
                    }
                },
                RbTree::Node(el_id, el_parent, el_color, el_left, el_right) => {
                    match erased_right {
                        RbTree::Empty => {
                            // Only a left child: symmetric, but the C copies the parent word into the
                            // child before replacing the link.
                            have rb_left(old(tree.model)) == erased_left by auto();
                            have rb_right(old(tree.model)) == RbTree::Empty by auto();
                            have erase_outcome(old(tree.model), old(up.model)) == EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model)))) by auto();
                            have erase_splice(old(tree.model)) == rb_erase_one_child_model(old(tree.model)) by auto();
                            have erased_left != RbTree::Empty by auto();
                            have ctx_rb(up.model, black_height(RbTree::Node(erased, erased_parent, erased_color, erased_left, RbTree::Empty)),
                                rb_color(RbTree::Node(erased, erased_parent, erased_color, erased_left, RbTree::Empty))) == 1 by {
                                rewrite(RbTree::Empty == erased_right);
                                rewrite(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right) == tree.model); assumption();
                            }
                            apply(rb_erase_only_left_child(erased, erased_parent, erased_color, erased_left, up.model));
                            apply(ctx_consistent_node_children(up.model, erased, erased_parent, erased_color, erased_left, erased_right, 0));
                            apply(rb_erase_child_keeps_parents(up.model, erased, erased_parent, erased_color, erased_left, erased_right, erased_left));
                            apply(erase_context_parent(up.model, erased, erased_parent, erased_color, erased_left, erased_right));
                            apply(plug_parent_consistent_transport(up.model, rb_reparent(rb_recolor(erased_left, Color::Black), erased_parent), 0));
                            have rb_tree_parent_consistent(plug(old(up.model), rb_reparent(rb_recolor(erased_left, Color::Black), erased_parent))) == 1 by {
                                unfold(rb_tree_parent_consistent(plug(old(up.model), rb_reparent(rb_recolor(erased_left, Color::Black), erased_parent))));
                            }
                            have rb_reparent(rb_recolor(erased_left, Color::Black), erased_parent)
                                == RbTree::Node(el_id, erased_parent, Color::Black, el_left, el_right) by {
                                rewrite(erased_left == RbTree::Node(el_id, el_parent, el_color, el_left, el_right));
                                unfold(rb_recolor(RbTree::Node(el_id, el_parent, el_color, el_left, el_right), Color::Black));
                                unfold(rb_reparent(RbTree::Node(el_id, el_parent, Color::Black, el_left, el_right), erased_parent)); normalize();
                            }
                            have rb_erase_one_child_model(old(tree.model)) == rb_reparent(rb_recolor(erased_left, Color::Black), erased_parent) by {
                                rewrite(old(tree.model) == RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right));
                                unfold(rb_erase_one_child_model(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right)));
                                rewrite(erased_right == RbTree::Empty);
                                rewrite(erased_left == RbTree::Node(el_id, el_parent, el_color, el_left, el_right));
                                unfold(rb_erase_root_child(RbTree::Node(erased, erased_parent, erased_color, RbTree::Node(el_id, el_parent, el_color, el_left, el_right), RbTree::Empty)));
                                normalize();
                            }
                            have rb_inorder(erase_splice(old(tree.model))) == list::append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model)))) by {
                                rewrite(erase_splice(old(tree.model)) == rb_erase_one_child_model(old(tree.model)));
                                rewrite(rb_erase_one_child_model(old(tree.model)) == rb_reparent(rb_recolor(erased_left, Color::Black), erased_parent));
                                rewrite(rb_inorder(rb_reparent(rb_recolor(erased_left, Color::Black), erased_parent)) == rb_inorder(erased_left));
                                rewrite(rb_left(old(tree.model)) == erased_left); rewrite(rb_right(old(tree.model)) == RbTree::Empty);
                                unfold(rb_inorder(RbTree::Empty));
                                apply(list::append_right_identity(rb_inorder(erased_left)));
                                rewrite(list::append(rb_inorder(erased_left), List<struct rb_node*>::Nil) == rb_inorder(erased_left)); normalize();
                            }
                            let { left: l, right: r } = unfold(tree);
                            unfold(r);
                            let { left: child_left, right: child_right } = unfold(l);
                            have (node->__rb_parent_color & 1) == 1 by {
                                rewrite((node->__rb_parent_color & 1) == color_bit(erased_color));
                                rewrite(erased_color == Color::Black); unfold(color_bit(Color::Black)); normalize();
                            }
                            have (old(node->__rb_parent_color) & 1) == 1 by { rewrite(old(node->__rb_parent_color) == node->__rb_parent_color); assumption(); }
                            execute_until(statement(22));
                            let { after: remaining } = step(__rb_change_child(node, tmp, parent, root), { before: up });
                            have el_id->__rb_parent_color == pc;
                            have (pc & 1) == color_bit(Color::Black) by {
                                rewrite(pc == old(node->__rb_parent_color)); unfold(color_bit(Color::Black)); assumption();
                            }
                            let replacement = fold(rb_at(el_id), {
                                model: RbTree::Node(el_id, erased_parent, Color::Black, el_left, el_right)
                            }, { left: child_left, right: child_right });
                            have rb_tree_parent_consistent(plug(remaining.model, replacement.model)) == 1 by {
                                rewrite(remaining.model == old(up.model));
                                rewrite(replacement.model == rb_reparent(rb_recolor(erased_left, Color::Black), erased_parent));
                                unfold(rb_tree_parent_consistent(plug(old(up.model), rb_reparent(rb_recolor(erased_left, Color::Black), erased_parent))));
                                assumption();
                            }
                            mark balanced;
                            let { whole: whole } = refold_to_root(el_id, root, { c: remaining, t: replacement });
                            have whole.model == plug(old(up.model), rb_erase_one_child_model(old(tree.model))) by {
                                rewrite(whole.model == plug(at(balanced, remaining.model), RbTree::Node(el_id, erased_parent, Color::Black, el_left, el_right)));
                                rewrite(at(balanced, remaining.model) == old(up.model));
                                rewrite(rb_erase_one_child_model(old(tree.model)) == rb_reparent(rb_recolor(erased_left, Color::Black), erased_parent));
                                rewrite(rb_reparent(rb_recolor(erased_left, Color::Black), erased_parent) == RbTree::Node(el_id, erased_parent, Color::Black, el_left, el_right));
                                normalize();
                            }
                            open(erase_callbacks(augment)) { execute(); }
                            let out = fold(erase_out(root, result), { model: EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model)))) }, { whole: whole });
                            have erase_out_rb(out.model) == 1 by {
                                rewrite(out.model == EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model)))));
                                unfold(erase_out_rb(EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model))))));
                                rewrite(rb_erase_one_child_model(old(tree.model)) == rb_reparent(rb_recolor(erased_left, Color::Black), erased_parent));
                                assumption();
                            }
                            have erase_out_tree(out.model) == plug(old(up.model), rb_erase_one_child_model(old(tree.model))) by {
                                rewrite(out.model == EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model)))));
                                unfold(erase_out_tree(EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model)))))); normalize();
                            }
                            have out.model == erase_outcome(old(tree.model), old(up.model)) by {
                                rewrite(out.model == EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model)))));
                                rewrite(erase_outcome(old(tree.model), old(up.model)) == EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model)))));
                                normalize();
                            }
                            have rb_tree_parent_consistent(erase_out_tree(out.model)) == 1 by {
                                rewrite(out.model == EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model)))));
                                unfold(erase_out_tree(EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model))))));
                                rewrite(rb_erase_one_child_model(old(tree.model)) == rb_reparent(rb_recolor(erased_left, Color::Black), erased_parent));
                                assumption();
                            }
                            have erase_out_tree(out.model) == plug(old(up.model), erase_splice(old(tree.model))) by {
                                rewrite(out.model == EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model)))));
                                unfold(erase_out_tree(EraseOutcome::Balanced(plug(old(up.model), rb_erase_one_child_model(old(tree.model))))));
                                rewrite(erase_splice(old(tree.model)) == rb_erase_one_child_model(old(tree.model)));
                                normalize();
                            }
                            simp();
                        },
                        RbTree::Node(er_id, er_parent, er_color, er_left, er_right) => {
                            match er_left {
                                RbTree::Empty => {
                                    match er_right {
                                        RbTree::Empty => {
                                            match er_color {
                                                Color::Red => {
                                                    // Immediate red-leaf successor: it takes the erased node's place and color.
                                                    have rb_left(old(tree.model)) == erased_left by auto();
                                                    have rb_right(old(tree.model)) == erased_right by auto();
                                                    have erase_outcome(old(tree.model), old(up.model)) == EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_leaf_model(old(tree.model)))) by auto();
                                                    have erase_splice(old(tree.model)) == rb_erase_immediate_leaf_model(old(tree.model)) by auto();
                                                    have is_rb(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right)) == 1 by {
                                                        rewrite(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right) == tree.model); assumption();
                                                    }
                                                    have ctx_rb(up.model, black_height(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right)),
                                                        rb_color(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right))) == 1 by {
                                                        rewrite(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right) == tree.model); assumption();
                                                    }
                                                    apply(rb_erase_red_successor_splice(erased, er_id, erased_parent, erased_color, erased_left, erased_right, up.model, 0));
                                                    apply(erase_context_parent(up.model, erased, erased_parent, erased_color, erased_left, erased_right));
                                                    have rb_successor_splice(er_id, erased_parent, erased_color, erased_left, erased_right)
                                                        == RbTree::Node(er_id, erased_parent, erased_color, RbTree::Node(el_id, er_id, el_color, el_left, el_right), RbTree::Empty) by {
                                                        unfold(rb_successor_splice(er_id, erased_parent, erased_color, erased_left, erased_right));
                                                        rewrite(erased_left == RbTree::Node(el_id, el_parent, el_color, el_left, el_right));
                                                        rewrite(erased_right == RbTree::Node(er_id, er_parent, er_color, er_left, er_right));
                                                        rewrite(er_left == RbTree::Empty); rewrite(er_right == RbTree::Empty);
                                                        unfold(rb_remove_min(RbTree::Node(er_id, er_parent, er_color, RbTree::Empty, RbTree::Empty)));
                                                        unfold(rb_reparent(RbTree::Empty, er_parent)); unfold(rb_reparent(RbTree::Empty, er_id));
                                                        unfold(rb_reparent(RbTree::Node(el_id, el_parent, el_color, el_left, el_right), er_id));
                                                        normalize();
                                                    }
                                                    have rb_erase_immediate_leaf_model(old(tree.model)) == rb_successor_splice(er_id, erased_parent, erased_color, erased_left, erased_right) by {
                                                        rewrite(old(tree.model) == RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right));
                                                        rewrite(erased_right == RbTree::Node(er_id, er_parent, er_color, er_left, er_right));
                                                        unfold(rb_erase_immediate_leaf_model(RbTree::Node(erased, erased_parent, erased_color, erased_left, RbTree::Node(er_id, er_parent, er_color, er_left, er_right))));
                                                        normalize();
                                                    }
                                                    have rb_inorder(erase_splice(old(tree.model))) == list::append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model)))) by {
                                                        rewrite(erase_splice(old(tree.model)) == rb_erase_immediate_leaf_model(old(tree.model)));
                                                        rewrite(rb_erase_immediate_leaf_model(old(tree.model)) == rb_successor_splice(er_id, erased_parent, erased_color, erased_left, erased_right));
                                                        rewrite(rb_left(old(tree.model)) == erased_left); rewrite(rb_right(old(tree.model)) == erased_right); assumption();
                                                    }
                                                    have rb_tree_parent_consistent(plug(old(up.model), rb_successor_splice(er_id, erased_parent, erased_color, erased_left, erased_right))) == 1 by {
                                                        unfold(rb_tree_parent_consistent(plug(old(up.model), rb_successor_splice(er_id, erased_parent, erased_color, erased_left, erased_right))));
                                                    }
                                                    have is_rb_root(plug(old(up.model), rb_successor_splice(er_id, erased_parent, erased_color, erased_left, erased_right))) == 1 by {
                                                        rewrite(old(up.model) == up.model); assumption();
                                                    }
                                                    let { left: l, right: r } = unfold(tree);
                                                    let { left: sleft, right: sright } = unfold(r);
                                                    unfold(sleft); unfold(sright);
                                                    let { left: lleft, right: lright } = unfold(l);
                                                    have (er_id->__rb_parent_color & 1) == 0 by {
                                                        rewrite((er_id->__rb_parent_color & 1) == color_bit(er_color));
                                                        rewrite(er_color == Color::Red); unfold(color_bit(Color::Red)); normalize();
                                                    }
                                                    have (old(node->__rb_parent_color) & 1) == color_bit(erased_color) by {
                                                        rewrite(old(node->__rb_parent_color) == node->__rb_parent_color); assumption();
                                                    }
                                                    have old(node->__rb_parent_color) == address(erased_parent) + (old(node->__rb_parent_color) & 1) by {
                                                        rewrite(old(node->__rb_parent_color) == node->__rb_parent_color); assumption();
                                                    }
                                                    open(erase_callbacks(augment)) { execute_until(statement(52)); }
                                                    let moved_left = fold(rb_at(el_id), {
                                                        model: RbTree::Node(el_id, er_id, el_color, el_left, el_right)
                                                    }, { left: lleft, right: lright });
                                                    let empty_right = fold(rb_at(0), { model: RbTree::Empty });
                                                    have rb_parent_is(RbTree::Node(el_id, er_id, el_color, el_left, el_right), er_id) == 1 by {
                                                        unfold(rb_parent_is(RbTree::Node(el_id, er_id, el_color, el_left, el_right), er_id)); normalize();
                                                    }
                                                    have rb_parent_is(RbTree::Empty, er_id) == 1 by { unfold(rb_parent_is(RbTree::Empty, er_id)); normalize(); }
                                                    execute_until(statement(54));
                                                    have tmp == erased_parent;
                                                    mark transplant;
                                                    let { after: remaining } = step(__rb_change_child(node, successor, tmp, root), { before: up });
                                                    have successor == er_id;
                                                    have er_id->__rb_parent_color == at(transplant, er_id->__rb_parent_color) by normalize();
                                                    have (er_id->__rb_parent_color & 1) == 0 by {
                                                        rewrite(er_id->__rb_parent_color == at(transplant, er_id->__rb_parent_color)); assumption();
                                                    }
                                                    have er_id->rb_left == at(transplant, er_id->rb_left) by { normalize() using { successor == er_id; }; }
                                                    have er_id->rb_right == at(transplant, er_id->rb_right) by { normalize() using { successor == er_id; }; }
                                                    open(erase_callbacks(augment)) { execute_until(statement(60)); }
                                                    have (pc & 1) == color_bit(erased_color) by { rewrite(pc == old(node->__rb_parent_color)); assumption(); }
                                                    have pc == address(erased_parent) + (pc & 1) by { rewrite(pc == old(node->__rb_parent_color)); assumption(); }
                                                    let replacement = fold(rb_at(er_id), { model: RbTree::Node(er_id, erased_parent, erased_color, RbTree::Node(el_id, er_id, el_color, el_left, el_right), RbTree::Empty) },
                                                        { left: moved_left, right: empty_right });
                                                    have rb_tree_parent_consistent(plug(remaining.model, replacement.model)) == 1 by {
                                                        rewrite(remaining.model == old(up.model));
                                                        rewrite(replacement.model == RbTree::Node(er_id, erased_parent, erased_color, RbTree::Node(el_id, er_id, el_color, el_left, el_right), RbTree::Empty));
                                                        rewrite(RbTree::Node(er_id, erased_parent, erased_color, RbTree::Node(el_id, er_id, el_color, el_left, el_right), RbTree::Empty)
                                                            == rb_successor_splice(er_id, erased_parent, erased_color, erased_left, erased_right));
                                                        assumption();
                                                    }
                                                    mark balanced;
                                                    let { whole: whole } = refold_to_root(er_id, root, { c: remaining, t: replacement });
                                                    have whole.model == plug(old(up.model), rb_erase_immediate_leaf_model(old(tree.model))) by {
                                                        rewrite(whole.model == plug(at(balanced, remaining.model), RbTree::Node(er_id, erased_parent, erased_color, RbTree::Node(el_id, er_id, el_color, el_left, el_right), RbTree::Empty)));
                                                        rewrite(at(balanced, remaining.model) == old(up.model));
                                                        rewrite(rb_erase_immediate_leaf_model(old(tree.model)) == rb_successor_splice(er_id, erased_parent, erased_color, erased_left, erased_right));
                                                        rewrite(rb_successor_splice(er_id, erased_parent, erased_color, erased_left, erased_right)
                                                            == RbTree::Node(er_id, erased_parent, erased_color, RbTree::Node(el_id, er_id, el_color, el_left, el_right), RbTree::Empty));
                                                        normalize();
                                                    }
                                                    open(erase_callbacks(augment)) { execute(); }
                                                    let out = fold(erase_out(root, result), { model: EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_leaf_model(old(tree.model)))) }, { whole: whole });
                                                    have erase_out_rb(out.model) == 1 by {
                                                        rewrite(out.model == EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_leaf_model(old(tree.model)))));
                                                        unfold(erase_out_rb(EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_leaf_model(old(tree.model))))));
                                                        rewrite(rb_erase_immediate_leaf_model(old(tree.model)) == rb_successor_splice(er_id, erased_parent, erased_color, erased_left, erased_right));
                                                        assumption();
                                                    }
                                                    have erase_out_tree(out.model) == plug(old(up.model), rb_erase_immediate_leaf_model(old(tree.model))) by {
                                                        rewrite(out.model == EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_leaf_model(old(tree.model)))));
                                                        unfold(erase_out_tree(EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_leaf_model(old(tree.model)))))); normalize();
                                                    }
                                                    have out.model == erase_outcome(old(tree.model), old(up.model)) by {
                                                        rewrite(out.model == EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_leaf_model(old(tree.model)))));
                                                        rewrite(erase_outcome(old(tree.model), old(up.model)) == EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_leaf_model(old(tree.model)))));
                                                        normalize();
                                                    }
                                                    have rb_tree_parent_consistent(erase_out_tree(out.model)) == 1 by {
                                                        rewrite(out.model == EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_leaf_model(old(tree.model)))));
                                                        unfold(erase_out_tree(EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_leaf_model(old(tree.model))))));
                                                        rewrite(rb_erase_immediate_leaf_model(old(tree.model)) == rb_successor_splice(er_id, erased_parent, erased_color, erased_left, erased_right));
                                                        assumption();
                                                    }
                                                    have erase_out_tree(out.model) == plug(old(up.model), erase_splice(old(tree.model))) by {
                                                        rewrite(out.model == EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_leaf_model(old(tree.model)))));
                                                        unfold(erase_out_tree(EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_leaf_model(old(tree.model))))));
                                                        rewrite(erase_splice(old(tree.model)) == rb_erase_immediate_leaf_model(old(tree.model)));
                                                        normalize();
                                                    }
                                                    simp();
                                                },
                                                Color::Black => {
                                                    // Immediate black-leaf successor: it takes the erased node's place and color,
                                                    // leaving an empty right hole one black level short; repair starts there.
                                                    have rb_left(old(tree.model)) == erased_left by auto();
                                                    have rb_right(old(tree.model)) == erased_right by auto();
                                                    have erase_outcome(old(tree.model), old(up.model)) == EraseOutcome::Deficit(rb_erase_immediate_black_context(old(tree.model), old(up.model))) by auto();
                                                    have erase_splice(old(tree.model)) == rb_erase_immediate_leaf_model(old(tree.model)) by auto();
                                                    have is_rb(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right)) == 1 by {
                                                        rewrite(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right) == tree.model); assumption();
                                                    }
                                                    have ctx_rb(up.model, black_height(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right)),
                                                        rb_color(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right))) == 1 by {
                                                        rewrite(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right) == tree.model); assumption();
                                                    }
                                                    apply(rb_erase_black_successor_splice(erased, er_id, erased_parent, erased_color, erased_left, erased_right, up.model, 0));
                                                    apply(erase_context_parent(up.model, erased, erased_parent, erased_color, erased_left, erased_right));
                                                    have rb_successor_splice(er_id, erased_parent, erased_color, erased_left, erased_right)
                                                        == RbTree::Node(er_id, erased_parent, erased_color, RbTree::Node(el_id, er_id, el_color, el_left, el_right), RbTree::Empty) by {
                                                        unfold(rb_successor_splice(er_id, erased_parent, erased_color, erased_left, erased_right));
                                                        rewrite(erased_left == RbTree::Node(el_id, el_parent, el_color, el_left, el_right));
                                                        rewrite(erased_right == RbTree::Node(er_id, er_parent, er_color, er_left, er_right));
                                                        rewrite(er_left == RbTree::Empty); rewrite(er_right == RbTree::Empty);
                                                        unfold(rb_remove_min(RbTree::Node(er_id, er_parent, er_color, RbTree::Empty, RbTree::Empty)));
                                                        unfold(rb_reparent(RbTree::Empty, er_parent)); unfold(rb_reparent(RbTree::Empty, er_id));
                                                        unfold(rb_reparent(RbTree::Node(el_id, el_parent, el_color, el_left, el_right), er_id));
                                                        normalize();
                                                    }
                                                    have rb_erase_immediate_leaf_model(old(tree.model)) == rb_successor_splice(er_id, erased_parent, erased_color, erased_left, erased_right) by {
                                                        rewrite(old(tree.model) == RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right));
                                                        rewrite(erased_right == RbTree::Node(er_id, er_parent, er_color, er_left, er_right));
                                                        unfold(rb_erase_immediate_leaf_model(RbTree::Node(erased, erased_parent, erased_color, erased_left, RbTree::Node(er_id, er_parent, er_color, er_left, er_right))));
                                                        normalize();
                                                    }
                                                    have rb_inorder(erase_splice(old(tree.model))) == list::append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model)))) by {
                                                        rewrite(erase_splice(old(tree.model)) == rb_erase_immediate_leaf_model(old(tree.model)));
                                                        rewrite(rb_erase_immediate_leaf_model(old(tree.model)) == rb_successor_splice(er_id, erased_parent, erased_color, erased_left, erased_right));
                                                        rewrite(rb_left(old(tree.model)) == erased_left); rewrite(rb_right(old(tree.model)) == erased_right); assumption();
                                                    }
                                                    have rb_successor_context(er_id, erased_parent, erased_color, erased_left, erased_right, old(up.model))
                                                        == Context::Right(er_id, erased_parent, erased_color, RbTree::Node(el_id, er_id, el_color, el_left, el_right), old(up.model)) by {
                                                        unfold(rb_successor_context(er_id, erased_parent, erased_color, erased_left, erased_right, old(up.model)));
                                                        rewrite(erased_left == RbTree::Node(el_id, el_parent, el_color, el_left, el_right));
                                                        rewrite(erased_right == RbTree::Node(er_id, er_parent, er_color, er_left, er_right));
                                                        unfold(rb_reparent(RbTree::Node(er_id, er_parent, er_color, er_left, er_right), er_id));
                                                        rewrite(er_left == RbTree::Empty);
                                                        unfold(rb_min_context(RbTree::Node(er_id, er_id, er_color, RbTree::Empty, er_right),
                                                            Context::Right(er_id, erased_parent, erased_color, rb_reparent(RbTree::Node(el_id, el_parent, el_color, el_left, el_right), er_id), old(up.model))));
                                                        unfold(rb_reparent(RbTree::Node(el_id, el_parent, el_color, el_left, el_right), er_id)); normalize();
                                                    }
                                                    have rb_erase_immediate_black_context(old(tree.model), old(up.model))
                                                        == rb_successor_context(er_id, erased_parent, erased_color, erased_left, erased_right, old(up.model)) by {
                                                        rewrite(old(tree.model) == RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right));
                                                        rewrite(erased_right == RbTree::Node(er_id, er_parent, er_color, er_left, er_right));
                                                        unfold(rb_erase_immediate_black_context(RbTree::Node(erased, erased_parent, erased_color, erased_left, RbTree::Node(er_id, er_parent, er_color, er_left, er_right)), old(up.model)));
                                                        normalize();
                                                    }
                                                    have ctx_rb(rb_successor_context(er_id, erased_parent, erased_color, erased_left, erased_right, old(up.model)), Nat::Succ(Nat::Zero), Color::Black) == 1 by {
                                                        rewrite(old(up.model) == up.model); assumption();
                                                    }
                                                    have plug(rb_successor_context(er_id, erased_parent, erased_color, erased_left, erased_right, old(up.model)), RbTree::Empty)
                                                        == plug(old(up.model), rb_successor_splice(er_id, erased_parent, erased_color, erased_left, erased_right)) by {
                                                        rewrite(old(up.model) == up.model); assumption();
                                                    }
                                                    apply(plug_parent_consistent_transport(rb_successor_context(er_id, erased_parent, erased_color, erased_left, erased_right, old(up.model)), RbTree::Empty, 0));
                                                    have rb_tree_parent_consistent(plug(rb_successor_context(er_id, erased_parent, erased_color, erased_left, erased_right, old(up.model)), RbTree::Empty)) == 1 by {
                                                        unfold(rb_tree_parent_consistent(plug(rb_successor_context(er_id, erased_parent, erased_color, erased_left, erased_right, old(up.model)), RbTree::Empty)));
                                                    }
                                                    have ctx_node_is(old(up.model), erased_parent) == 1 by { rewrite(old(up.model) == up.model); assumption(); }
                                                    have old(up.model) == ctx_reroot(old(up.model), erased_parent) by { rewrite(old(up.model) == up.model); assumption(); }
                                                    let { left: l, right: r } = unfold(tree);
                                                    let { left: sleft, right: sright } = unfold(r);
                                                    unfold(sleft); unfold(sright);
                                                    let { left: lleft, right: lright } = unfold(l);
                                                    have (er_id->__rb_parent_color & 1) == 1 by {
                                                        rewrite((er_id->__rb_parent_color & 1) == color_bit(er_color));
                                                        rewrite(er_color == Color::Black); unfold(color_bit(Color::Black)); normalize();
                                                    }
                                                    have (old(node->__rb_parent_color) & 1) == color_bit(erased_color) by {
                                                        rewrite(old(node->__rb_parent_color) == node->__rb_parent_color); assumption();
                                                    }
                                                    have old(node->__rb_parent_color) == address(erased_parent) + (old(node->__rb_parent_color) & 1) by {
                                                        rewrite(old(node->__rb_parent_color) == node->__rb_parent_color); assumption();
                                                    }
                                                    open(erase_callbacks(augment)) { execute_until(statement(52)); }
                                                    let moved_left = fold(rb_at(el_id), {
                                                        model: RbTree::Node(el_id, er_id, el_color, el_left, el_right)
                                                    }, { left: lleft, right: lright });
                                                    let empty_right = fold(rb_at(0), { model: RbTree::Empty });
                                                    have rb_parent_is(RbTree::Node(el_id, er_id, el_color, el_left, el_right), er_id) == 1 by {
                                                        unfold(rb_parent_is(RbTree::Node(el_id, er_id, el_color, el_left, el_right), er_id)); normalize();
                                                    }
                                                    have rb_parent_is(RbTree::Empty, er_id) == 1 by { unfold(rb_parent_is(RbTree::Empty, er_id)); normalize(); }
                                                    execute_until(statement(54));
                                                    mark transplant;
                                                    let { after: remaining } = step(__rb_change_child(node, successor, tmp, root), { before: up });
                                                    have er_id->__rb_parent_color == at(transplant, er_id->__rb_parent_color) by normalize();
                                                    have (er_id->__rb_parent_color & 1) == 1 by {
                                                        rewrite(er_id->__rb_parent_color == at(transplant, er_id->__rb_parent_color)); assumption();
                                                    }
                                                    have er_id->rb_left == at(transplant, er_id->rb_left) by { normalize() using { successor == er_id; }; }
                                                    have er_id->rb_right == at(transplant, er_id->rb_right) by { normalize() using { successor == er_id; }; }
                                                    open(erase_callbacks(augment)) { execute_until(statement(60)); }
                                                    have (pc & 1) == color_bit(erased_color) by { rewrite(pc == old(node->__rb_parent_color)); assumption(); }
                                                    have pc == address(erased_parent) + (pc & 1) by { rewrite(pc == old(node->__rb_parent_color)); assumption(); }
                                                    let deficit = fold(ctx_at(0, root), { model: Context::Right(er_id, erased_parent, erased_color, RbTree::Node(el_id, er_id, el_color, el_left, el_right), old(up.model)) },
                                                        { sibling: moved_left, up: remaining });
                                                    have deficit.model == rb_erase_immediate_black_context(old(tree.model), old(up.model)) by {
                                                        rewrite(rb_erase_immediate_black_context(old(tree.model), old(up.model))
                                                            == rb_successor_context(er_id, erased_parent, erased_color, erased_left, erased_right, old(up.model)));
                                                        rewrite(rb_successor_context(er_id, erased_parent, erased_color, erased_left, erased_right, old(up.model))
                                                            == Context::Right(er_id, erased_parent, erased_color, RbTree::Node(el_id, er_id, el_color, el_left, el_right), old(up.model)));
                                                        normalize();
                                                    }
                                                    unfold(empty_right);
                                                    open(erase_callbacks(augment)) { execute(); }
                                                    have result == er_id;
                                                    have deficit.model != Context::Top by {
                                                        rewrite(deficit.model == Context::Right(er_id, erased_parent, erased_color, RbTree::Node(el_id, er_id, el_color, el_left, el_right), old(up.model))); normalize();
                                                    }
                                                    have ctx_node_is(deficit.model, result) == 1 by {
                                                        rewrite(deficit.model == Context::Right(er_id, erased_parent, erased_color, RbTree::Node(el_id, er_id, el_color, el_left, el_right), old(up.model))); rewrite(result == er_id);
                                                        unfold(ctx_node_is(Context::Right(er_id, erased_parent, erased_color, RbTree::Node(el_id, er_id, el_color, el_left, el_right), old(up.model)), er_id)); normalize();
                                                    }
                                                    have rb_erase_immediate_black_context(old(tree.model), old(up.model)) != Context::Top by { rewrite(rb_erase_immediate_black_context(old(tree.model), old(up.model)) == deficit.model); assumption(); }
                                                    have ctx_node_is(rb_erase_immediate_black_context(old(tree.model), old(up.model)), result) == 1 by { rewrite(rb_erase_immediate_black_context(old(tree.model), old(up.model)) == deficit.model); assumption(); }
                                                    let out = fold(erase_out(root, result), { model: EraseOutcome::Deficit(rb_erase_immediate_black_context(old(tree.model), old(up.model))) }, { deficit: deficit });
                                                    have erase_out_rb(out.model) == 1 by {
                                                        rewrite(out.model == EraseOutcome::Deficit(rb_erase_immediate_black_context(old(tree.model), old(up.model))));
                                                        unfold(erase_out_rb(EraseOutcome::Deficit(rb_erase_immediate_black_context(old(tree.model), old(up.model)))));
                                                        rewrite(rb_erase_immediate_black_context(old(tree.model), old(up.model))
                                                            == rb_successor_context(er_id, erased_parent, erased_color, erased_left, erased_right, old(up.model)));
                                                        assumption();
                                                    }
                                                    have erase_out_tree(out.model) == plug(old(up.model), rb_erase_immediate_leaf_model(old(tree.model))) by {
                                                        rewrite(out.model == EraseOutcome::Deficit(rb_erase_immediate_black_context(old(tree.model), old(up.model))));
                                                        unfold(erase_out_tree(EraseOutcome::Deficit(rb_erase_immediate_black_context(old(tree.model), old(up.model)))));
                                                        rewrite(rb_erase_immediate_black_context(old(tree.model), old(up.model))
                                                            == rb_successor_context(er_id, erased_parent, erased_color, erased_left, erased_right, old(up.model)));
                                                        rewrite(rb_erase_immediate_leaf_model(old(tree.model)) == rb_successor_splice(er_id, erased_parent, erased_color, erased_left, erased_right));
                                                        assumption();
                                                    }
                                                    have rb_tree_parent_consistent(erase_out_tree(out.model)) == 1 by {
                                                        rewrite(out.model == EraseOutcome::Deficit(rb_erase_immediate_black_context(old(tree.model), old(up.model))));
                                                        unfold(erase_out_tree(EraseOutcome::Deficit(rb_erase_immediate_black_context(old(tree.model), old(up.model)))));
                                                        rewrite(rb_erase_immediate_black_context(old(tree.model), old(up.model))
                                                            == rb_successor_context(er_id, erased_parent, erased_color, erased_left, erased_right, old(up.model)));
                                                        assumption();
                                                    }
                                                    have out.model == erase_outcome(old(tree.model), old(up.model)) by {
                                                        rewrite(out.model == EraseOutcome::Deficit(rb_erase_immediate_black_context(old(tree.model), old(up.model))));
                                                        rewrite(erase_outcome(old(tree.model), old(up.model)) == EraseOutcome::Deficit(rb_erase_immediate_black_context(old(tree.model), old(up.model))));
                                                        normalize();
                                                    }
                                                    have rb_tree_parent_consistent(erase_out_tree(out.model)) == 1 by {
                                                        rewrite(out.model == EraseOutcome::Deficit(rb_erase_immediate_black_context(old(tree.model), old(up.model))));
                                                        unfold(erase_out_tree(EraseOutcome::Deficit(rb_erase_immediate_black_context(old(tree.model), old(up.model)))));
                                                        rewrite(rb_erase_immediate_black_context(old(tree.model), old(up.model)) == rb_successor_context(er_id, erased_parent, erased_color, erased_left, erased_right, old(up.model)));
                                                        assumption();
                                                    }
                                                    have erase_out_tree(out.model) == plug(old(up.model), erase_splice(old(tree.model))) by {
                                                        rewrite(out.model == EraseOutcome::Deficit(rb_erase_immediate_black_context(old(tree.model), old(up.model))));
                                                        unfold(erase_out_tree(EraseOutcome::Deficit(rb_erase_immediate_black_context(old(tree.model), old(up.model)))));
                                                        rewrite(erase_splice(old(tree.model)) == rb_erase_immediate_leaf_model(old(tree.model)));
                                                        rewrite(rb_erase_immediate_black_context(old(tree.model), old(up.model)) == rb_successor_context(er_id, erased_parent, erased_color, erased_left, erased_right, old(up.model)));
                                                        rewrite(rb_erase_immediate_leaf_model(old(tree.model)) == rb_successor_splice(er_id, erased_parent, erased_color, erased_left, erased_right));
                                                        rewrite(plug(rb_successor_context(er_id, erased_parent, erased_color, erased_left, erased_right, old(up.model)), RbTree::Empty) == plug(old(up.model), rb_successor_splice(er_id, erased_parent, erased_color, erased_left, erased_right)));
                                                        normalize();
                                                    }
                                                    simp();
                                                },
                                            }
                                        },
                                        RbTree::Node(ec_id, ec_parent, ec_color, ec_left, ec_right) => {
                                            // Immediate successor with a right child: the successor takes the erased
                                            // node's place and color; its child is blackened, so no repair is needed.
                                            have rb_left(old(tree.model)) == erased_left by auto();
                                            have rb_right(old(tree.model)) == erased_right by auto();
                                            have erase_outcome(old(tree.model), old(up.model)) == EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_child_model(old(tree.model)))) by auto();
                                            have erase_splice(old(tree.model)) == rb_erase_immediate_child_model(old(tree.model)) by auto();
                                            have is_rb(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right)) == 1 by {
                                                rewrite(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right) == tree.model); assumption();
                                            }
                                            have ctx_rb(up.model, black_height(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right)),
                                                rb_color(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right))) == 1 by {
                                                rewrite(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right) == tree.model); assumption();
                                            }
                                            apply(ctx_consistent_node_children(up.model, erased, erased_parent, erased_color, erased_left, erased_right, 0));
                                            apply(rb_node_is_reflexive(erased_parent));
                                            apply(rb_parent_consistent_node(erased, erased_parent, erased_color, erased_left, erased_right, erased_parent));
                                            apply(erase_context_parent(up.model, erased, erased_parent, erased_color, erased_left, erased_right));
                                            have ctx_rb(up.model, black_height(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right)), erased_color)
                                                == ctx_rb(up.model, black_height(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right)),
                                                    rb_color(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right))) by {
                                                unfold(rb_color(RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right))); normalize();
                                            }
                                            let { left: l, right: r } = unfold(tree);
                                            apply(rb_parent_is_node_parent(er_id, er_parent, er_color, er_left, er_right, erased));
                                            have is_rb(RbTree::Node(erased, erased_parent, erased_color, erased_left,
                                                RbTree::Node(er_id, erased, er_color, RbTree::Empty, er_right))) == 1 by {
                                                rewrite(erased == er_parent);
                                                rewrite(RbTree::Empty == er_left);
                                                rewrite(RbTree::Node(er_id, er_parent, er_color, er_left, er_right) == erased_right);
                                                rewrite(er_parent == erased); assumption();
                                            }
                                            have rb_parent_consistent(RbTree::Node(erased, erased_parent, erased_color, erased_left,
                                                RbTree::Node(er_id, erased, er_color, RbTree::Empty, er_right)), erased_parent) == 1 by {
                                                rewrite(erased == er_parent); rewrite(RbTree::Empty == er_left);
                                                rewrite(RbTree::Node(er_id, er_parent, er_color, er_left, er_right) == erased_right);
                                                rewrite(er_parent == erased); assumption();
                                            }
                                            have ctx_rb(up.model, black_height(RbTree::Node(erased, erased_parent, erased_color, erased_left,
                                                RbTree::Node(er_id, erased, er_color, RbTree::Empty, er_right))), erased_color) == 1 by {
                                                rewrite(erased == er_parent); rewrite(RbTree::Empty == er_left);
                                                rewrite(RbTree::Node(er_id, er_parent, er_color, er_left, er_right) == erased_right);
                                                rewrite(er_parent == erased); assumption();
                                            }
                                            apply(rb_erase_immediate_successor_child(erased, er_id, erased_parent, erased_color, erased_left, er_color, er_right, up.model));
                                            apply(ctx_consistent_swap(up.model, erased, erased_parent, erased_color, erased_left, erased_right,
                                                rb_immediate_successor_child(er_id, erased_parent, erased_color, erased_left, er_right), 0));
                                            apply(plug_parent_consistent_transport(up.model, rb_immediate_successor_child(er_id, erased_parent, erased_color, erased_left, er_right), 0));
                                            have rb_tree_parent_consistent(plug(old(up.model), rb_immediate_successor_child(er_id, erased_parent, erased_color, erased_left, er_right))) == 1 by {
                                                unfold(rb_tree_parent_consistent(plug(old(up.model), rb_immediate_successor_child(er_id, erased_parent, erased_color, erased_left, er_right))));
                                            }
                                            have is_rb_root(plug(old(up.model), rb_immediate_successor_child(er_id, erased_parent, erased_color, erased_left, er_right))) == 1 by {
                                                rewrite(old(up.model) == up.model); assumption();
                                            }
                                            have rb_erase_immediate_child_model(old(tree.model)) == rb_immediate_successor_child(er_id, erased_parent, erased_color, erased_left, er_right) by {
                                                rewrite(old(tree.model) == RbTree::Node(erased, erased_parent, erased_color, erased_left, erased_right));
                                                rewrite(erased_right == RbTree::Node(er_id, er_parent, er_color, er_left, er_right));
                                                unfold(rb_erase_immediate_child_model(RbTree::Node(erased, erased_parent, erased_color, erased_left, RbTree::Node(er_id, er_parent, er_color, er_left, er_right))));
                                                normalize();
                                            }
                                            have rb_inorder(erase_splice(old(tree.model))) == list::append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model)))) by {
                                                rewrite(erase_splice(old(tree.model)) == rb_erase_immediate_child_model(old(tree.model)));
                                                rewrite(rb_erase_immediate_child_model(old(tree.model)) == rb_immediate_successor_child(er_id, erased_parent, erased_color, erased_left, er_right));
                                                rewrite(rb_left(old(tree.model)) == erased_left); rewrite(rb_right(old(tree.model)) == erased_right);
                                                rewrite(erased_right == RbTree::Node(er_id, er_parent, er_color, er_left, er_right));
                                                rewrite(er_left == RbTree::Empty); rewrite(er_parent == erased); assumption();
                                            }
                                            have rb_immediate_successor_child(er_id, erased_parent, erased_color, erased_left, er_right)
                                                == RbTree::Node(er_id, erased_parent, erased_color, RbTree::Node(el_id, er_id, el_color, el_left, el_right), RbTree::Node(ec_id, er_id, Color::Black, ec_left, ec_right)) by {
                                                unfold(rb_immediate_successor_child(er_id, erased_parent, erased_color, erased_left, er_right));
                                                rewrite(erased_left == RbTree::Node(el_id, el_parent, el_color, el_left, el_right));
                                                rewrite(er_right == RbTree::Node(ec_id, ec_parent, ec_color, ec_left, ec_right));
                                                unfold(rb_reparent(RbTree::Node(el_id, el_parent, el_color, el_left, el_right), er_id));
                                                unfold(rb_recolor(RbTree::Node(ec_id, ec_parent, ec_color, ec_left, ec_right), Color::Black));
                                                unfold(rb_reparent(RbTree::Node(ec_id, ec_parent, Color::Black, ec_left, ec_right), er_id));
                                                normalize();
                                            }
                                            let { left: sleft, right: sright } = unfold(r);
                                            unfold(sleft);
                                            let { left: lleft, right: lright } = unfold(l);
                                            have (old(node->__rb_parent_color) & 1) == color_bit(erased_color) by {
                                                rewrite(old(node->__rb_parent_color) == node->__rb_parent_color); assumption();
                                            }
                                            have old(node->__rb_parent_color) == address(erased_parent) + (old(node->__rb_parent_color) & 1) by {
                                                rewrite(old(node->__rb_parent_color) == node->__rb_parent_color); assumption();
                                            }
                                            open(erase_callbacks(augment)) { execute_until(statement(52)); }
                                            let moved_left = fold(rb_at(el_id), {
                                                model: RbTree::Node(el_id, er_id, el_color, el_left, el_right)
                                            }, { left: lleft, right: lright });
                                            have rb_parent_is(RbTree::Node(el_id, er_id, el_color, el_left, el_right), er_id) == 1 by {
                                                unfold(rb_parent_is(RbTree::Node(el_id, er_id, el_color, el_left, el_right), er_id)); normalize();
                                            }
                                            execute_until(statement(54));
                                            mark transplant;
                                            let { after: remaining } = step(__rb_change_child(node, successor, tmp, root), { before: up });
                                            have er_id->rb_left == at(transplant, er_id->rb_left) by { normalize() using { successor == er_id; }; }
                                            have er_id->rb_right == at(transplant, er_id->rb_right) by { normalize() using { successor == er_id; }; }
                                            let { left: cleft, right: cright } = unfold(sright);
                                            have er_id->rb_left == el_id;
                                            have er_id->rb_right == ec_id;
                                            open(erase_callbacks(augment)) { execute_until(statement(60)); }
                                            have er_id->rb_left == el_id;
                                            have er_id->rb_right == ec_id;
                                            have (pc & 1) == color_bit(erased_color) by { rewrite(pc == old(node->__rb_parent_color)); assumption(); }
                                            have pc == address(erased_parent) + (pc & 1) by { rewrite(pc == old(node->__rb_parent_color)); assumption(); }
                                            have color_bit(Color::Black) == 1 by { unfold(color_bit(Color::Black)); normalize(); }
                                            let moved_right = fold(rb_at(ec_id), { model: RbTree::Node(ec_id, er_id, Color::Black, ec_left, ec_right) }, { left: cleft, right: cright });
                                            have rb_parent_is(RbTree::Node(ec_id, er_id, Color::Black, ec_left, ec_right), er_id) == 1 by {
                                                unfold(rb_parent_is(RbTree::Node(ec_id, er_id, Color::Black, ec_left, ec_right), er_id)); normalize();
                                            }
                                            let replacement = fold(rb_at(er_id), { model: RbTree::Node(er_id, erased_parent, erased_color, RbTree::Node(el_id, er_id, el_color, el_left, el_right), RbTree::Node(ec_id, er_id, Color::Black, ec_left, ec_right)) },
                                                { left: moved_left, right: moved_right });
                                            have rb_tree_parent_consistent(plug(remaining.model, replacement.model)) == 1 by {
                                                rewrite(remaining.model == old(up.model));
                                                rewrite(replacement.model == RbTree::Node(er_id, erased_parent, erased_color, RbTree::Node(el_id, er_id, el_color, el_left, el_right), RbTree::Node(ec_id, er_id, Color::Black, ec_left, ec_right)));
                                                rewrite(RbTree::Node(er_id, erased_parent, erased_color, RbTree::Node(el_id, er_id, el_color, el_left, el_right), RbTree::Node(ec_id, er_id, Color::Black, ec_left, ec_right))
                                                    == rb_immediate_successor_child(er_id, erased_parent, erased_color, erased_left, er_right));
                                                assumption();
                                            }
                                            mark balanced;
                                            let { whole: whole } = refold_to_root(er_id, root, { c: remaining, t: replacement });
                                            have whole.model == plug(old(up.model), rb_erase_immediate_child_model(old(tree.model))) by {
                                                rewrite(whole.model == plug(at(balanced, remaining.model), RbTree::Node(er_id, erased_parent, erased_color, RbTree::Node(el_id, er_id, el_color, el_left, el_right), RbTree::Node(ec_id, er_id, Color::Black, ec_left, ec_right))));
                                                rewrite(at(balanced, remaining.model) == old(up.model));
                                                rewrite(rb_erase_immediate_child_model(old(tree.model)) == rb_immediate_successor_child(er_id, erased_parent, erased_color, erased_left, er_right));
                                                rewrite(rb_immediate_successor_child(er_id, erased_parent, erased_color, erased_left, er_right)
                                                    == RbTree::Node(er_id, erased_parent, erased_color, RbTree::Node(el_id, er_id, el_color, el_left, el_right), RbTree::Node(ec_id, er_id, Color::Black, ec_left, ec_right)));
                                                normalize();
                                            }
                                            open(erase_callbacks(augment)) { execute(); }
                                            let out = fold(erase_out(root, result), { model: EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_child_model(old(tree.model)))) }, { whole: whole });
                                            have erase_out_rb(out.model) == 1 by {
                                                rewrite(out.model == EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_child_model(old(tree.model)))));
                                                unfold(erase_out_rb(EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_child_model(old(tree.model))))));
                                                rewrite(rb_erase_immediate_child_model(old(tree.model)) == rb_immediate_successor_child(er_id, erased_parent, erased_color, erased_left, er_right));
                                                assumption();
                                            }
                                            have rb_tree_parent_consistent(erase_out_tree(out.model)) == 1 by {
                                                rewrite(out.model == EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_child_model(old(tree.model)))));
                                                unfold(erase_out_tree(EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_child_model(old(tree.model))))));
                                                rewrite(rb_erase_immediate_child_model(old(tree.model)) == rb_immediate_successor_child(er_id, erased_parent, erased_color, erased_left, er_right));
                                                assumption();
                                            }
                                            have erase_out_tree(out.model) == plug(old(up.model), rb_erase_immediate_child_model(old(tree.model))) by {
                                                rewrite(out.model == EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_child_model(old(tree.model)))));
                                                unfold(erase_out_tree(EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_child_model(old(tree.model)))))); normalize();
                                            }
                                            have out.model == erase_outcome(old(tree.model), old(up.model)) by {
                                                rewrite(out.model == EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_child_model(old(tree.model)))));
                                                rewrite(erase_outcome(old(tree.model), old(up.model)) == EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_child_model(old(tree.model)))));
                                                normalize();
                                            }
                                            have rb_tree_parent_consistent(erase_out_tree(out.model)) == 1 by {
                                                rewrite(out.model == EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_child_model(old(tree.model)))));
                                                unfold(erase_out_tree(EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_child_model(old(tree.model))))));
                                                rewrite(rb_erase_immediate_child_model(old(tree.model)) == rb_immediate_successor_child(er_id, erased_parent, erased_color, erased_left, er_right));
                                                assumption();
                                            }
                                            have erase_out_tree(out.model) == plug(old(up.model), erase_splice(old(tree.model))) by {
                                                rewrite(out.model == EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_child_model(old(tree.model)))));
                                                unfold(erase_out_tree(EraseOutcome::Balanced(plug(old(up.model), rb_erase_immediate_child_model(old(tree.model))))));
                                                rewrite(erase_splice(old(tree.model)) == rb_erase_immediate_child_model(old(tree.model)));
                                                normalize();
                                            }
                                            simp();
                                        },
                                    }
                                },
                                RbTree::Node(ep_id, ep_parent, ep_color, ep_left, ep_right) => {
                                    // The deeper-successor shape was handled first.
                                    have rb_left(tree.model) == erased_left by auto();
                                    have rb_right(tree.model) == erased_right by auto();
                                    have erased_left != RbTree::Empty by auto();
                                    have erased_right != RbTree::Empty by auto();
                                    have rb_left(tree.model) != RbTree::Empty by { rewrite(rb_left(tree.model) == erased_left); assumption(); }
                                    have rb_right(tree.model) != RbTree::Empty by { rewrite(rb_right(tree.model) == erased_right); assumption(); }
                                    have rb_left(erased_right) == er_left by {
                                        rewrite(erased_right == RbTree::Node(er_id, er_parent, er_color, er_left, er_right));
                                        unfold(rb_left(RbTree::Node(er_id, er_parent, er_color, er_left, er_right))); normalize();
                                    }
                                    have er_left != RbTree::Empty by auto();
                                    have rb_left(rb_right(tree.model)) != RbTree::Empty by {
                                        rewrite(rb_right(tree.model) == erased_right); rewrite(rb_left(erased_right) == er_left); assumption();
                                    }
                                    have rb_left(tree.model) != RbTree::Empty and rb_right(tree.model) != RbTree::Empty
                                        and rb_left(rb_right(tree.model)) != RbTree::Empty by assumption();
                                    contradiction(rb_left(tree.model) != RbTree::Empty and rb_right(tree.model) != RbTree::Empty
                                        and rb_left(rb_right(tree.model)) != RbTree::Empty);
                                },
                            }
                        },
                    }
                },
            }
        },
    }
    }
}
